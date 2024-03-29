use super::*;
use crate::lang::types::Types;
use astgraph::*;
use petgraph::prelude::*;
use std::{iter, ops::Deref, rc::Rc};

type TypeGraphInner = petgraph::stable_graph::StableGraph<Node, Flow, petgraph::Directed, u32>;

pub type AnonTypes = TypesSet;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Node {
    pub input: Knowledge,
    pub output: Knowledge,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Knowledge {
    Any,
    Known(Type),
    Obliged(Type),
    Inferred(TypesSet),
}

#[derive(Debug, PartialEq, Eq)]
pub struct TypesSet(Rc<HashSet<Type>>);

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
    RemoveInput(NodeIndex, Type),
    AnyInput(NodeIndex),
    KnownOutput(NodeIndex, Type),
    ObligeOutput(NodeIndex, Type),
    RemoveOutput(NodeIndex, Type),
    AddEdge {
        src: NodeIndex,
        dst: NodeIndex,
        flow: Flow,
    },
    /// Adds an anonymous type into the type graph, updating all inferred nodes.
    AnonTy(Type),
}

impl Chg {
    pub fn is_anon_ty(&self) -> bool {
        matches!(self, Chg::AnonTy(_))
    }

    pub fn node(&self) -> NodeIndex {
        *match self {
            Chg::KnownInput(i, _) => i,
            Chg::ObligeInput(i, _) => i,
            Chg::RemoveInput(i, _) => i,
            Chg::AnyInput(i) => i,
            Chg::KnownOutput(i, _) => i,
            Chg::ObligeOutput(i, _) => i,
            Chg::RemoveOutput(i, _) => i,
            Chg::AddEdge {
                src,
                dst: _,
                flow: _,
            } => src,
            Chg::AnonTy(_) => unreachable!("`Chg::node` is not available for `Chg::AnonTy`"),
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
pub struct TypeGraph {
    g: TypeGraphInner,
    anon_tys: AnonTypes,
}

// NOTE that we do not expose a mutable deref, keep mutation contained in this module.
impl Deref for TypeGraph {
    type Target = TypeGraphInner;
    fn deref(&self) -> &TypeGraphInner {
        &self.g
    }
}

impl TypeGraph {
    pub fn anon_tys(&self) -> &AnonTypes {
        &self.anon_tys
    }

    /// Builds a type graph based off the ast graph.
    pub fn build(ast_graph: &AstGraph, tys: &Types) -> Self {
        let full = TypesSet::full(tys);

        let mut g = ast_graph.map(
            |_, _| Node {
                input: Knowledge::Inferred(full.clone()),
                output: Knowledge::Inferred(full.clone()),
            },
            |_, _| Flow::OI,
        );

        g.clear_edges(); // remove all the edges

        Self {
            g,
            anon_tys: AnonTypes::empty(),
        }
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

            if let Some(ty) = ty {
                let current = self
                    .g
                    .node_weight_mut(nidx)
                    .expect("Type and Ast graphs should have same indices");
                assert!(
                    matches!(&current.output, Knowledge::Inferred(ts) if ts.contains(&ty)),
                    "only overwrite inferred with the type in the set"
                );
                current.input = Knowledge::Any; // all these nodes take any input
                current.output = Knowledge::Known(ty);
            }
        }

        // based on any Keyed(Some(type))
        for (e, node) in ag
            .edge_indices()
            .filter(|&e| ag[e].is_key())
            .map(|e| (e, ag.edge_endpoints(e).expect("should exist").1))
        {
            if let Some(ty) = ag[e].keyed().cloned() {
                self.g[node].input = Knowledge::Known(ty);
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
                self.g.add_edge(expr, op, Flow::II); // input -> input
            }
        }

        // the output of the last op in an expression to the output of the expression
        for &expr in &exprs {
            if let Some(op) = op_neighbors(expr).next() {
                // first, since this would have been the last op to add
                self.g.add_edge(op, expr, Flow::OO); // output -> output
            }
        }

        // the output of a block into the input of the next block
        for &expr in &exprs {
            let froms = op_neighbors(expr).skip(1); // starts at nth-1 op
            let tos = op_neighbors(expr); // starts at last op

            for (from, to) in froms.zip(tos) {
                self.g.add_edge(from, to, Flow::OI); // output -> input
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
            self.g.add_edge(op.idx(), poundi.idx(), Flow::II); // op -> arg: II
            self.g.add_edge(op.idx(), poundi.idx(), Flow::IO); // op -> arg: IO
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
        self.g.add_edge(def, expr, Flow::II);
        // flow the output of the expression into the Def
        self.g.add_edge(expr, def, Flow::OO);

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
            self.g.add_edge(op, def, Flow::II);
        }

        // can only link def to op if there is no type key or if only def
        if is_keyed_none || is_only_def {
            // flow the output of the Def into the Op
            self.g.add_edge(def, op, Flow::OO);
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
                self.g.add_edge(op.idx(), arg.idx(), Flow::II);
            }
        }

        chgd
    }

    /// Reduces inferred types sets given the viable input types for linked definitions.
    pub fn reduce_inferred_sets_given_def_constraints(&mut self, ag: &AstGraph) {
        for op in ag.op_nodes() {
            // only reduce where multiple inputs
            if !self[op.idx()].input.is_multiple() {
                continue;
            }

            let keys = op.cmds(ag).fold(Some(TypesSet::empty()), |set, cmd| {
                let e = &ag[ag.find_edge(op.idx(), cmd.idx()).unwrap()];
                match (set, e.keyed()) {
                    (Some(mut s), Some(t)) => {
                        s.insert(t.clone());
                        Some(s)
                    }
                    // if keyed on `None`, then we cannot reduce set
                    _ => None,
                }
            });

            if let Some(constrained) = keys {
                self.g[op.idx()].input = constrained.into();
            }
        }
    }

    pub fn set_root_input_ty(&mut self, ty: Type) {
        if let Some(n) = self.g.node_weight_mut(0.into()) {
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
            let to = &self[to_idx];
            let known_out = from.output.has_ty();
            let known_in = from.input.has_ty();
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
                    Update::ToInput => self.g[to_idx].input = with,
                    Update::ToOutput => self.g[to_idx].output = with,
                    Update::FromInput => self.g[from_idx].input = with,
                }

                completed_indices.insert(edge.index());
                chgd = true;
            }
        }

        Ok(chgd)
    }

    /// Reduces the inferred types sets to be the intersection between two sets joined by an edge.
    ///
    /// Returns if the graph was changed.
    /// If an intersection results in an empty set, an error is returned.
    pub fn intersect_inferred_sets(&mut self, completed_indices: &IndexSet) -> Result<bool> {
        fn int(a: &Knowledge, b: &Knowledge) -> Option<TypesSet> {
            match (a, b) {
                (Knowledge::Inferred(a), Knowledge::Inferred(b)) => {
                    Some(a.intersection(b)).filter(|i| i != a)
                }
                _ => None,
            }
        }

        let edges = self
            .edge_indices()
            .filter(|e| !completed_indices.contains(&e.index()))
            .collect::<Vec<_>>();

        let mut chgd = false;

        for edge in edges {
            let flow = &self[edge];
            let (from_idx, to_idx) = self
                .edge_endpoints(edge)
                .expect("edge would exist in graph");
            let from = &self[from_idx];
            let to = &self[to_idx];

            match flow {
                Flow::II => {
                    if let Some(i) = int(&from.input, &to.input) {
                        self.g[from_idx].input = i.clone().into();
                        self.g[to_idx].input = i.into();
                        chgd = true;
                    }
                }
                Flow::IO => {
                    if let Some(i) = int(&from.input, &to.output) {
                        self.g[from_idx].input = i.clone().into();
                        self.g[to_idx].output = i.into();
                        chgd = true;
                    }
                }
                Flow::OI => {
                    if let Some(i) = int(&from.output, &to.input) {
                        self.g[from_idx].output = i.clone().into();
                        self.g[to_idx].input = i.into();
                        chgd = true;
                    }
                }
                Flow::OO => {
                    if let Some(i) = int(&from.output, &to.output) {
                        self.g[from_idx].output = i.clone().into();
                        self.g[to_idx].output = i.into();
                        chgd = true;
                    }
                }
            }
        }

        Ok(chgd)
    }

    /// Upgrades any inferred knowledge which only have a single type to be `Obliged` to that type.
    pub fn upgrade_singleton_inferred_sets(&mut self) -> bool {
        let mut chgd = false;

        for n in self
            .iter_kn_mut()
            .filter(|x| matches!(x, Knowledge::Inferred(t) if t.is_single()))
        {
            *n = Knowledge::Obliged(n.ty().expect("will exist").clone());
            chgd = true;
        }

        chgd
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
            if let Some(node) = tg.g.node_weight_mut(node) {
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
            Chg::RemoveInput(node, ty) => apply(self, node, |n| Ok(n.input.rm_inferred(&ty))),
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
            Chg::RemoveOutput(node, ty) => apply(self, node, |n| Ok(n.output.rm_inferred(&ty))),
            Chg::AddEdge { src, dst, flow } => {
                // TODO edges_connecting is not implemented yet for StableGraph
                // can be replicated with a filter
                let chgd = self
                    .g
                    .edges(src)
                    .filter(|e| e.target() == dst)
                    .all(|e| e.weight() != &flow);
                if chgd {
                    self.g.add_edge(src, dst, flow);
                }
                Ok(chgd)
            }
            Chg::AnonTy(ty) => {
                let mut chgd = false;
                for n in self.iter_kn_mut().filter_map(|x| match x {
                    Knowledge::Inferred(x) => Some(x),
                    _ => None,
                }) {
                    let x = n.insert(ty.clone());
                    chgd |= x;
                }

                self.anon_tys.insert(ty);

                Ok(chgd)
            }
        }
    }

    fn iter_kn_mut(&mut self) -> impl Iterator<Item = &mut Knowledge> {
        self.g.node_weights_mut().flat_map(|n| {
            let Node { input, output } = n;
            iter::once(input).chain(iter::once(output))
        })
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
    /// Returns if there is a single known type.
    pub fn has_ty(&self) -> bool {
        match self {
            Knowledge::Known(_) | Knowledge::Obliged(_) => true,
            Knowledge::Inferred(ts) => ts.is_single(),
            _ => false,
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

    /// Returns if there are _more than one_ valid types (in the inferred state).
    pub fn is_multiple(&self) -> bool {
        matches!(self, Knowledge::Inferred(ts) if ts.len() > 1)
    }

    /// If the knowledge is an inferred [`TypesSet`], returns a reference to it.
    /// **Note that it only returns `Some` if the types set has _more than one element_.**
    pub fn tys(&self) -> Option<&TypesSet> {
        match self {
            Knowledge::Inferred(x) if x.len() > 1 => Some(x),
            _ => None,
        }
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
            Any => {
                let mut set = TypesSet::empty();
                set.insert(ty);
                *self = Inferred(set);
                true
            }
        }
    }

    /// Removes `ty` from the `Inferred` [`TypesSet`].
    ///
    /// Returns if `self` was actually changed, since this is dependent on the state of the
    /// knowledge.
    pub fn rm_inferred(&mut self, ty: &Type) -> bool {
        use Knowledge::*;
        match self {
            Known(_) | Obliged(_) | Any => false,
            Inferred(ts) => ts.remove(ty),
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
            // A known source can flow into an unknown or any dest
            (Known(_), Any) => Ok(()),
            // A known source can flow into itself or lower ranked items if the types match
            (Known(t1), Known(t2) | Obliged(t2)) if t1 == t2 => Ok(()),
            (Known(t1), Inferred(ts)) if ts.contains(t1) => Ok(()),

            // An obliged source can flow into an unknown or any dest
            (Obliged(_), Any) => Ok(()),
            // An obliged source can flow into itself or lower ranked items if the types match
            // It can also flow into a Known type, again if the types agree
            (Obliged(t1), Known(t2) | Obliged(t2)) if t1 == t2 => Ok(()),
            (Obliged(t1), Inferred(ts)) if ts.contains(t1) => Ok(()),

            // An inferred source can flow into an unknown or any dest
            (Inferred(_), Any) => Ok(()),
            // An inferred source can flow into itself if the types match
            (Inferred(t1), Inferred(t2)) if t1 == t2 => Ok(()),

            // An any source can flow into an Any or Inferred dest
            (Any, Any | Inferred(_)) => Ok(()),

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
            (Known(t1) | Obliged(t1), Inferred(ts)) if !ts.contains(t1) => Err(UnmatchedInferred {
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
        }
    }
}

impl TypesSet {
    /// Return an empty set.
    pub fn empty() -> Self {
        TypesSet(Default::default())
    }

    /// Return a full set of types.
    pub fn full(tys: &Types) -> Self {
        let mut s = Self::empty();
        for t in tys.iter().map(|(_, x)| x.clone()) {
            s.insert(t);
        }
        s
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

    /// Returns if there is only a single type in the set.
    pub fn is_single(&self) -> bool {
        self.len() == 1
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
        Rc::make_mut(&mut self.0).insert(ty)
    }

    /// Remove a type from the set.
    ///
    /// Returns `true` if the set was changed (`ty` existed in the set).
    pub fn remove(&mut self, ty: &Type) -> bool {
        Rc::make_mut(&mut self.0).remove(ty)
    }

    /// If there is only a single element in the set, returns a reference to it.
    /// Otherwise returns `None`.
    pub fn only(&self) -> Option<&Type> {
        if self.is_single() {
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

    pub fn intersection(&self, other: &Self) -> Self {
        if self == other {
            self.clone()
        } else {
            TypesSet(Rc::new(self.0.intersection(&other.0).cloned().collect()))
        }
    }

    pub fn iter(&self) -> impl ExactSizeIterator<Item = &Type> {
        self.0.iter()
    }
}

impl Default for TypesSet {
    fn default() -> Self {
        Self::empty()
    }
}

/// Clone is fast -- it is a reference count increment.
impl Clone for TypesSet {
    /// Clone is fast -- it is a reference count increment.
    fn clone(&self) -> Self {
        TypesSet(Rc::clone(&self.0))
    }
}

impl fmt::Display for TypesSet {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut trail = false;
        for x in self.0.iter() {
            if trail {
                write!(f, " ")?;
            }
            trail = true;
            write!(f, "{x}")?;
        }

        Ok(())
    }
}

impl From<TypesSet> for Knowledge {
    fn from(ts: TypesSet) -> Self {
        Knowledge::Inferred(ts)
    }
}
