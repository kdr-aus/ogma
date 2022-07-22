use super::*;
use astgraph::*;
use petgraph::prelude::*;
use std::ops::Deref;

type TypeGraphInner = petgraph::stable_graph::StableGraph<Node, Flow, petgraph::Directed, u32>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Node {
    pub input: Knowledge,
    pub output: Knowledge,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Knowledge {
    Unknown, // TODO remove this in favour of _reducing_ types set
    Any,
    Known(Type),
    Obliged(Type),
    Inferred(TypesSet),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct TypesSet(HashSet<Type>);

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Flow {
    /// Output knowledge flows into the input.
    OI,
    /// Input knowledge flows into the input.
    II,
    /// Output knowledge flows into the output.
    OO,
    /// Input knowledge flows into the output.
    IO,
}

/// A specific alteration to be made to the type graph.
#[derive(Debug)]
pub enum Chg {
    KnownInput(NodeIndex, Type),
    ObligeInput(NodeIndex, Type),
    InferInput(NodeIndex, Type),
    AnyInput(NodeIndex),
    KnownOutput(NodeIndex, Type),
    ObligeOutput(NodeIndex, Type),
    InferOutput(NodeIndex, Type),
    AddEdge {
        src: NodeIndex,
        dst: NodeIndex,
        flow: Flow,
    },
}

impl Chg {
    pub fn node(&self) -> NodeIndex {
        *match self {
            Chg::KnownInput(i, _) => i,
            Chg::ObligeInput(i, _) => i,
            Chg::InferInput(i, _) => i,
            Chg::AnyInput(i) => i,
            Chg::KnownOutput(i, _) => i,
            Chg::ObligeOutput(i, _) => i,
            Chg::InferOutput(i, _) => i,
            Chg::AddEdge {
                src,
                dst: _,
                flow: _,
            } => src,
        }
    }
}

#[derive(Debug)]
pub enum Conflict {
    /// The source is `Unknown`.
    UnknownSrc,
    /// There is a direct conflict where a _known_ source is trying to overwrite a _known_
    /// destination and the types do not match.
    ConflictingKnown { src: Type, dst: Type },
    /// There is an obligation to meet but concrete types do not match.
    UnmatchedObligation {
        src: Type,
        /// Obligation.
        dst: Type,
    },
    UnmatchedInferred {
        src: TypesSet,
        /// Inferred.
        dst: TypesSet,
    },
    /// Types match, but trying to flow an inferred node into stronger garauntee nodes such as
    /// `Known` or `Obliged`.
    OverpoweringInferred,
}

pub struct ResolutionError {
    pub from: NodeIndex,
    pub to: NodeIndex,
    pub flow: Flow,
    pub conflict: Conflict,
}

#[derive(Default, Debug, Clone)]
pub struct TypeGraph(TypeGraphInner);

// NOTE that we do not expose a mutable deref, keep mutation contained in this module.
impl Deref for TypeGraph {
    type Target = TypeGraphInner;
    fn deref(&self) -> &TypeGraphInner {
        &self.0
    }
}

impl TypeGraph {
    /// Builds a type graph based off the ast graph.
    pub fn build(ast_graph: &AstGraph) -> Self {
        let mut g = TypeGraph(ast_graph.map(
            |_, _| Node {
                input: Knowledge::Unknown,
                output: Knowledge::Unknown,
            },
            |_, _| Flow::OI,
        ));

        g.0.clear_edges(); // remove all the edges
        g
    }

    /// Apply _known_ types from the AST nodes.
    ///
    /// For instance, a number variant node can be assigned the type number as an output.
    pub fn apply_ast_types(&mut self, ag: &AstGraph) {
        // based on ast nodes
        for nidx in ag.node_indices() {
            let node = &ag[nidx];

            use AstNode::*;
            let ty = match node {
                Op { .. } | Flag(_) | Intrinsic { .. } | Def { .. } => None,
                Ident(_) => Some(Type::Str),
                Num { .. } => Some(Type::Num),
                Pound { ty, tag: _ } => ty.ty(),
                Var(_) => None,
                Expr(_) => None,
            };

            if let Some(ty) = ty.map(Knowledge::Known) {
                let current = self
                    .0
                    .node_weight_mut(nidx)
                    .expect("Type and Ast graphs should have same indices");
                assert!(
                    matches!(current.output, Knowledge::Unknown),
                    "overwriting a non-unknown type node"
                );
                current.input = Knowledge::Any; // all these nodes take any input
                current.output = ty;
            }
        }

        // based on any Keyed(Some(type))
        for (e, node) in ag
            .edge_indices()
            .filter(|&e| ag[e].is_key())
            .map(|e| (e, ag.edge_endpoints(e).expect("should exist").1))
        {
            if let Some(ty) = ag[e].keyed().cloned() {
                self.0[node].input = Knowledge::Known(ty);
            }
        }
    }

    /// Apply known edges for the flow of types from the ast graph:
    ///
    /// - The _input_ of an expression goes to the _input_ of the first op,
    /// - The _output_ of the last op in an expression to the _output_ of the expression,
    /// - The _output_ of a block into the _input_ of the next block,
    /// - A `#i` arg will use it's op nodes _input_ as the _input_ **and** _output_.
    ///
    /// For `Def`s:
    /// - `Def->Expr: II`
    /// - `Expr->Def: OO`
    /// - If keyed `None`:
    ///   - `Op->Def: II`
    ///   - `Def->Op: OO`
    ///   - This is because defs will **always** use the input defined on the op.
    /// - If **ALL** cmd nodes are `Def`s
    ///   - `Op->Arg: II`: where `Arg` is a callsite param **for all params**.
    pub fn apply_ast_edges(&mut self, ag: &AstGraph) {
        // NOTE: The graph .neighbors call returns items in the _reverse_ order they were added.
        // It also does not support a .rev() call.

        let exprs = ag
            .node_indices()
            .filter(|&n| ag[n].expr().is_some())
            .collect::<Vec<_>>();

        // Be careful here since the expression may be an argument and link to an command node
        let op_neighbors = |expr| ag.neighbors(expr).filter(|&n| ag[n].op().is_some());

        // The input of an expression goes to the input of the first op
        for &expr in &exprs {
            if let Some(op) = op_neighbors(expr).last() {
                // last, since this would have been the first op to add
                self.0.add_edge(expr, op, Flow::II); // input -> input
            }
        }

        // the output of the last op in an expression to the output of the expression
        for &expr in &exprs {
            if let Some(op) = op_neighbors(expr).next() {
                // first, since this would have been the last op to add
                self.0.add_edge(op, expr, Flow::OO); // output -> output
            }
        }

        // the output of a block into the input of the next block
        for &expr in &exprs {
            let froms = op_neighbors(expr).skip(1); // starts at nth-1 op
            let tos = op_neighbors(expr); // starts at last op

            for (from, to) in froms.zip(tos) {
                self.0.add_edge(from, to, Flow::OI); // output -> input
            }
        }

        // #i input/output is fed by it's op's input
        for poundi in ag.node_indices().filter_map(|n| match &ag[n] {
            AstNode::Pound {
                ty: PoundTy::Input,
                tag: _,
            } => Some(ArgNode(n)),
            _ => None,
        }) {
            let op = poundi.op(ag);
            self.0.add_edge(op.idx(), poundi.idx(), Flow::II); // op -> arg: II
            self.0.add_edge(op.idx(), poundi.idx(), Flow::IO); // op -> arg: IO
        }

        // defs
        for defnode in ag
            .node_indices()
            .filter_map(|n| ag[n].def().map(|_| DefNode(n)))
        {
            self.apply_ast_edges_defs(ag, defnode);
        }
    }

    fn apply_ast_edges_defs(&mut self, ag: &AstGraph, defnode: DefNode) {
        let def = defnode.idx();
        let op = defnode.parent(ag).idx();
        let expr = defnode.expr(ag).idx();

        // flow the input of the Def into the expression
        self.0.add_edge(def, expr, Flow::II);
        // flow the output of the expression into the Def
        self.0.add_edge(expr, def, Flow::OO);

        let is_keyed_none = ag[ag.find_edge(op, def).expect("edge from op to def")].keyed_none();
        let all_defs = ag
            .edges(op)
            .filter(|e| e.weight().is_key())
            .map(|e| e.target())
            .collect::<Vec<_>>();
        let is_only_def = all_defs.len() == 1;

        // can only link op to def if there is no type key
        if is_keyed_none {
            // flow the input of the op into the input of this Def
            self.0.add_edge(op, def, Flow::II);
        }

        // can only link def to op if there is no type key or if only def
        if is_keyed_none || is_only_def {
            // flow the output of the Def into the Op
            self.0.add_edge(def, op, Flow::OO);
        }

        if all_defs.iter().all(|n| ag[*n].def().is_some()) {
            self.link_def_arg_terms_with_ii_inner(ag, &all_defs);
        }
    }

    /// Add edges between a block's op (input) to _each_ arg (input).
    /// Only adds an edge if the positional argument is a **callsite** parameter.
    ///
    /// Returns if the type graph was altered.
    pub fn link_def_arg_terms_with_ii(&mut self, ag: &AstGraph, def: DefNode) -> bool {
        self.link_def_arg_terms_with_ii_inner(ag, &[def.idx()])
    }

    fn link_def_arg_terms_with_ii_inner(&mut self, ag: &AstGraph, defs: &[NodeIndex]) -> bool {
        let op = DefNode(defs[0]).parent(ag);
        let args = ag.get_args(DefNode(defs[0]));

        let params = defs
            .iter()
            .map(|&n| ag[n].def().expect("all def nodes"))
            .collect::<Vec<_>>();
        let min = params
            .iter()
            .map(|v| v.len())
            .min()
            .unwrap_or(0)
            .min(args.len());

        let mut chgd = false;

        for i in 0..min {
            let all_callsite = params.iter().all(|p| p[i].is_callsite_eval());
            if !all_callsite {
                continue;
            }

            let arg = args[i];

            if !self.contains_edge(op.idx(), arg.idx()) {
                chgd = true;
                self.0.add_edge(op.idx(), arg.idx(), Flow::II);
            }
        }

        chgd
    }

    pub fn set_root_input_ty(&mut self, ty: Type) {
        if let Some(n) = self.0.node_weight_mut(0.into()) {
            n.input = Knowledge::Known(ty);
        }
    }

    /// Returns if the graph was changed.
    pub fn flow_types(
        &mut self,
        completed_indices: &mut IndexSet,
    ) -> std::result::Result<bool, ResolutionError> {
        enum Update {
            ToInput,
            ToOutput,
            FromInput,
        }

        let mut chgd = false;

        let edges = self
            .edge_indices()
            .filter(|e| !completed_indices.contains(&e.index()))
            .collect::<Vec<_>>();

        for edge in edges {
            let flow = &self[edge];
            let (from_idx, to_idx) = self
                .edge_endpoints(edge)
                .expect("edge would exist in graph");
            let from = &self[from_idx];
            let to = &self.0[to_idx];
            let known_out = from.output.ty().is_some();
            let known_in = from.input.ty().is_some();
            let any_in = from.input.is_any();

            let reserr = |conflict| ResolutionError {
                from: from_idx,
                to: to_idx,
                flow: *flow,
                conflict,
            };

            let x = match flow {
                // Directed flow of input -> input
                Flow::II if known_in => {
                    from.input.can_flow(&to.input).map_err(reserr)?;
                    Some((Update::ToInput, from.input.clone()))
                }
                // Directed flow of output -> input
                Flow::OI if known_out => {
                    from.output.can_flow(&to.input).map_err(reserr)?;
                    Some((Update::ToInput, from.output.clone()))
                }
                // Directed flow of input -> output
                Flow::IO if known_in => {
                    from.input.can_flow(&to.output).map_err(reserr)?;
                    Some((Update::ToOutput, from.input.clone()))
                }
                // Directed flow of output -> output
                Flow::OO if known_out => {
                    from.output.can_flow(&to.output).map_err(reserr)?;
                    Some((Update::ToOutput, from.output.clone()))
                }
                // Backpropagate flow if to.input:Obliged | Known -> from.input
                Flow::II if matches!(to.input, Knowledge::Obliged(_) | Knowledge::Known(_)) => {
                    to.input.can_flow(&from.input).map_err(reserr)?;
                    Some((Update::FromInput, to.input.clone()))
                }
                // Backpropagate flow if to.input:Inferred -> from.input
                // Only propagate if can_flow.
                Flow::II
                    if matches!(to.input, Knowledge::Inferred(_))
                        && to.input.can_flow(&from.input).is_ok() =>
                {
                    Some((Update::FromInput, to.input.clone()))
                }
                // Flow input -> input, allowing Any to flow through
                // NOTE: Any should only be allowed on input types
                Flow::II if any_in => {
                    from.input.can_flow(&to.input).map_err(reserr)?;
                    Some((Update::ToInput, from.input.clone()))
                }
                Flow::II | Flow::IO | Flow::OI | Flow::OO => None,
            };

            if let Some((update, with)) = x {
                match update {
                    Update::ToInput => self.0[to_idx].input = with,
                    Update::ToOutput => self.0[to_idx].output = with,
                    Update::FromInput => self.0[from_idx].input = with,
                }

                completed_indices.insert(edge.index());
                chgd = true;
            }
        }

        Ok(chgd)
    }

    /// Apply the `chg` to the graph. Returns if the graph is actually altered (if the `chg` has
    /// already been applied, nothing would change).
    pub fn apply_chg(&mut self, chg: Chg) -> std::result::Result<bool, Conflict> {
        type R = std::result::Result<bool, Conflict>;

        fn set(k: &mut Knowledge, exp: Knowledge) -> R {
            (k == &exp).then(|| Ok(false)).unwrap_or_else(|| {
                exp.can_flow(k).map(|_| {
                    *k = exp;
                    true
                })
            })
        }

        fn apply<F>(tg: &mut TypeGraph, node: NodeIndex, setfn: F) -> R
        where
            F: FnOnce(&mut Node) -> R,
        {
            if let Some(node) = tg.0.node_weight_mut(node) {
                setfn(node)
            } else {
                Ok(false)
            }
        }

        match chg {
            Chg::KnownInput(node, ty) => {
                apply(self, node, |n| set(&mut n.input, Knowledge::Known(ty)))
            }
            Chg::ObligeInput(node, ty) => {
                apply(self, node, |n| set(&mut n.input, Knowledge::Obliged(ty)))
            }
            Chg::InferInput(node, ty) => {
                // TODO: should this return an error? usually `set` is called, which tests with
                // `can_flow`
                apply(self, node, |n| Ok(n.input.add_inferred(ty)))
            }
            Chg::AnyInput(node) => {
                // Only set the input to be Any if the there is no knowledge about the type
                if self[node].input.ty().is_none() {
                    apply(self, node, |n| set(&mut n.input, Knowledge::Any))
                } else {
                    Ok(false)
                }
            }
            Chg::KnownOutput(node, ty) => {
                apply(self, node, |n| set(&mut n.output, Knowledge::Known(ty)))
            }
            Chg::ObligeOutput(node, ty) => {
                apply(self, node, |n| set(&mut n.output, Knowledge::Obliged(ty)))
            }
            Chg::InferOutput(node, ty) => {
                // TODO: see InferInput
                apply(self, node, |n| Ok(n.output.add_inferred(ty)))
            }
            Chg::AddEdge { src, dst, flow } => {
                // TODO edges_connecting is not implemented yet for StableGraph
                // can be replicated with a filter
                let chgd = self
                    .0
                    .edges(src)
                    .filter(|e| e.target() == dst)
                    .all(|e| e.weight() != &flow);
                if chgd {
                    self.0.add_edge(src, dst, flow);
                }
                Ok(chgd)
            }
        }
    }
}

#[cfg(debug_assertions)]
impl TypeGraph {
    pub fn debug_write_flowchart(&self, ag: &AstGraph, buf: &mut String) {
        use fmt::Write;

        super::debug_write_flowchart(
            self,
            buf,
            |idx, _node| !matches!(&ag[idx], AstNode::Intrinsic { .. }),
            |idx, node, buf| {
                let ast_node = &ag[idx];
                write!(
                    buf,
                    "{idx} :: {ast} <br> {input} & {output}",
                    idx = idx.index(),
                    input = node.input,
                    output = node.output,
                    ast = ast_node
                )
            },
            |edge, buf| write!(buf, "{:?}", edge),
        )
        .unwrap()
    }
}

impl Node {
    /// Returns true if both the input and output both have types available to them.
    /// That is, either one will return `Some` when a `.ty()` call is made.
    pub fn has_types(&self) -> bool {
        self.input.ty().and(self.output.ty()).is_some()
    }
}

impl Knowledge {
    /// If the type is known, returns `Some`.
    pub fn known(&self) -> Option<&Type> {
        match self {
            Knowledge::Known(ty) => Some(ty),
            _ => None,
        }
    }

    /// If the type there is knowledge of some type, say if it is known or inferred, returns that
    /// knowledge.
    pub fn ty(&self) -> Option<&Type> {
        use Knowledge::*;
        match self {
            Known(ty) | Obliged(ty) => Some(ty),
            Inferred(ts) => ts.only(),
            _ => None,
        }
    }

    /// `Knowledge::Unknown` variant.
    pub fn is_unknown(&self) -> bool {
        matches!(self, Knowledge::Unknown)
    }

    /// `Knowledge::Any` variant.
    pub fn is_any(&self) -> bool {
        matches!(self, Knowledge::Any)
    }

    /// Adds `ty` into the `Inferred` [`TypesSet`].
    ///
    /// Returns if `self` was actually changed, since this is dependent on the state of the
    /// knowledge.
    pub fn add_inferred(&mut self, ty: Type) -> bool {
        use Knowledge::*;
        match self {
            Known(_) | Obliged(_) => false,
            Inferred(ts) => ts.insert(ty),
            Any | Unknown => {
                let mut set = TypesSet::empty();
                set.insert(ty);
                *self = Inferred(set);
                true
            }
        }
    }

    /// Checks that the this knowledge can 'flow' into the knowledged at `into`.
    ///
    /// Flow is driven by two aspects:
    /// 1. The ranking of the knowledge (`Known` is the strongest guarantee),
    /// 2. The types match.
    ///
    /// If there is a conflict between the two pieces of knowledge, a `Err(Conflict)` is returned.
    pub fn can_flow(&self, into: &Knowledge) -> std::result::Result<(), Conflict> {
        // NOTE this is not exhaustive.
        // For now we basically disallow many of the flow types
        // This is to test the TG flow and to ensure that the TG's flow is something that makes
        // sense but is also not overly constrained.
        // Any panics found in the wild should be sense-checked.
        use Conflict::*;
        use Knowledge::*;

        match (self, into) {
            // Unknown source cannot flow into anything!
            (Unknown, _) => Err(UnknownSrc),

            // A known source can flow into an unknown or any dest
            (Known(_), Unknown | Any) => Ok(()),
            // A known source can flow into itself or lower ranked items if the types match
            (Known(t1), Known(t2) | Obliged(t2)) if t1 == t2 => Ok(()),
            (Known(t1), Inferred(ts)) if ts.contains(t1) => Ok(()),

            // An obliged source can flow into an unknown or any dest
            (Obliged(_), Unknown | Any) => Ok(()),
            // An obliged source can flow into itself or lower ranked items if the types match
            (Obliged(t1), Obliged(t2)) if t1 == t2 => Ok(()),
            (Obliged(t1), Inferred(ts)) if ts.contains(t1) => Ok(()),

            // An inferred source can flow into an unknown or any dest
            (Inferred(_), Unknown | Any) => Ok(()),
            // An inferred source can flow into itself if the types match
            (Inferred(t1), Inferred(t2)) if t1 == t2 => Ok(()),

            // An any source can flow into an Any or Unknown dest
            (Any, Any | Unknown) => Ok(()),

            // Cannot flow if two known unmatching types
            (Known(t1), Known(t2)) if t1 != t2 => Err(ConflictingKnown {
                src: t1.clone(),
                dst: t2.clone(),
            }),
            // Cannot flow if obliged types does not match
            (Known(t1) | Obliged(t1), Obliged(t2)) if t1 != t2 => Err(UnmatchedObligation {
                src: t1.clone(),
                dst: t2.clone(),
            }),

            // Cannot flow if already inferred and does not match
            // NOTE: This might not be correct, the error might be right, but the handling might
            // need to be changed. For instance, if an inference does not match a known flow, then
            // we could _reset_ the compiler's compiled stack/steps and locals, but **keep the type
            // graph**. This way the information of the type graph remains, and it can 'reset' it's
            // flow.
            // NOTE: this would need to clear _all_ Inferred type graph entries.
            // NOTE: probably do this later if it is found that unreasonable errors are being
            // returned.
            (Known(t1), Inferred(ts)) if !ts.contains(t1) => Err(UnmatchedInferred {
                src: TypesSet::single(t1.clone()),
                dst: ts.clone(),
            }),
            // Cannot flow if inferred sets are disjoint
            (Inferred(ts1), Inferred(ts2)) if ts1.is_disjoint(ts2) => Err(UnmatchedInferred {
                src: ts1.clone(),
                dst: ts2.clone(),
            }),
            // Cannot flow if trying to flow an Inferred into an Obliged or Known,
            // even if the types match.
            (Inferred(ts), Known(t2) | Obliged(t2)) if ts.contains(t2) => Err(OverpoweringInferred),

            (a, b) => todo!("have not handled flow: {:?} -> {:?}", a, b),
        }
    }
}

impl fmt::Display for Knowledge {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Knowledge::*;

        match self {
            Known(t) => write!(f, "Known({})", t),
            Obliged(t) => write!(f, "Obliged({})", t),
            Inferred(t) => write!(f, "Inferred({})", t),
            Any => write!(f, "Any"),
            Unknown => write!(f, "Unknown"),
        }
    }
}

impl TypesSet {
    /// Return an empty set.
    pub fn empty() -> Self {
        TypesSet(Default::default())
    }

    /// Initialise a set with a single element: `ty`.
    pub fn single(ty: Type) -> Self {
        let mut s = Self::empty();
        s.insert(ty);
        s
    }

    /// The number of types in the set.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns if there are no types in the set.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The set contains `ty`.
    pub fn contains(&self, ty: &Type) -> bool {
        self.0.contains(ty)
    }

    /// Insert a type into the set.
    ///
    /// Returns `true` if the set was changed (`ty` did not exist in set), and `false` if the set
    /// was unchanged (`ty` already existed in set).
    pub fn insert(&mut self, ty: Type) -> bool {
        self.0.insert(ty)
    }

    /// If there is only a single element in the set, returns a reference to it.
    /// Otherwise returns `None`.
    pub fn only(&self) -> Option<&Type> {
        if self.len() == 1 {
            self.0.iter().next()
        } else {
            None
        }
    }

    /// Returns if this set shares no elements with `other`.
    pub fn is_disjoint(&self, other: &Self) -> bool {
        self.0.is_disjoint(&other.0)
    }

    /// Returns if this set intersects with another.
    /// That is, `self` shares one or more elements with `other`.
    pub fn intersects(&self, other: &Self) -> bool {
        !self.is_disjoint(other)
    }
}

impl fmt::Display for TypesSet {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut trail = false;
        write!(f, "{{")?;
        for x in self.0.iter() {
            if trail {
                write!(f, ", ")?;
            }
            trail = true;
            write!(f, "{x}")?;
        }

        write!(f, "}}")
    }
}
