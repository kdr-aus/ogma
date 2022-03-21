use super::*;
use kserd::Number;
use petgraph::prelude::*;
use std::ops::Deref;

type Inner = StableGraph<AstNode, Relation, Directed, u32>;

#[derive(Default, Debug, Clone)]
pub struct AstGraph(Inner);

// Note that we do not expose a mutable deref, keep mutation contained in this module.
impl Deref for AstGraph {
    type Target = Inner;
    fn deref(&self) -> &Inner {
        &self.0
    }
}

#[derive(Clone)]
pub enum AstNode {
    Op {
        op: Tag,
        blk: Tag,
    },
    Intrinsic {
        op: Tag,
        intrinsic: lang::impls::IntrinsicFn,
    },
    Def {
        expr: Tag,
        params: Vec<Parameter>,
    },
    Flag(Tag),
    Ident(Tag),
    Num {
        val: Number,
        tag: Tag,
    },
    Pound {
        ch: char,
        tag: Tag,
    },
    Var(Tag),
    Expr(Tag),
}

// NOTE that this is a mechanism for allowing transitive flags through the defs
/// The edges of the AST graph.
///
/// Most edges are `Normal`.
/// Ops connect to the various implementations through a `Keyed(Option<Type>)`.
/// Ops' terms connect to the various implementations using `Term(index)` where `index` _is the
/// position index in the block`.
/// Note that this position is a set for each flags and args, so if there were 2 terms, one flag
/// and one arg, each term would be connected with `Term(0)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Relation {
    Normal,
    Keyed(Option<Type>),
    Term(u8),
}

/// Engine equivalent of [`ast::Parameter`].
#[derive(Debug, Clone)]
pub struct Parameter {
    pub name: Tag,
    pub ty: ParameterTy,
}

#[derive(Debug, Clone)]
pub enum ParameterTy {
    Unspecified,
    Specified(Type),
    Expr,
}

const LOOPLIM: u32 = 128;

/// Initialises the syntax graph decomposing the expression.
///
/// This:
/// 1. Flattens the [`ast::Expression`],
/// 2. Expands any _defs_,
/// 3. Repeats at 1. if defs are found.
pub fn init(expr: ast::Expression, defs: &Definitions) -> Result<AstGraph> {
    let mut graph = AstGraph(Default::default());

    let expr_tag = expr.tag.clone();

    graph.flatten_expr(expr)?;

    let recursion_detector = &mut RecursionDetection::default();

    let mut count = 0;
    while graph.expand_defs(defs, recursion_detector)? {
        count += 1;
        if count > LOOPLIM {
            return Err(Error::ag_init_endless_loop(count, &expr_tag));
        }
    }

    Ok(graph)
}

/// Initialisation functions.
impl AstGraph {
    /// Returns the NodeIndex that the `expr` becomes.
    fn flatten_expr(&mut self, expr: ast::Expression) -> Result<NodeIndex> {
        use ast::*;

        let g = &mut self.0;

        // build the root expression node
        let Expression { tag, blocks } = expr;
        let root = g.add_node(AstNode::Expr(tag));

        // rather than building a recursive function, we'll use a queue of expressions to process,
        // since expressions are the recursive element
        let mut q = std::collections::VecDeque::new();
        q.push_back((root, blocks));

        // FIFO -- breadth-first
        while let Some((root, blocks)) = q.pop_front() {
            for blk in blocks {
                let blk_tag = blk.block_tag();
                let (op, terms) = blk.parts();

                let op = g.add_node(AstNode::Op { op, blk: blk_tag });
                g.add_edge(root, op, Relation::Normal); // edge from the expression root to the op

                for term in terms {
                    use ast::Argument::*;
                    use ast::Term::*;

                    let mut blks = None;

                    let node = match term {
                        Flag(f) => AstNode::Flag(f),
                        Arg(Ident(x)) => AstNode::Ident(x),
                        Arg(Num(val, tag)) => AstNode::Num { val, tag },
                        Arg(Pound(ch, tag)) => AstNode::Pound { ch, tag },
                        Arg(Var(x)) => AstNode::Var(x),
                        Arg(Expr(ast::Expression { tag, blocks })) => {
                            blks = Some(blocks);
                            AstNode::Expr(tag)
                        }
                    };

                    let term = g.add_node(node);
                    g.add_edge(op, term, Relation::Normal); // add a directed edge from op to the term

                    if let Some(blks) = blks {
                        q.push_back((term, blks));
                    }
                }
            }
        }

        Ok(root)
    }

    /// Returns `true` if definitions were found and expanded.
    fn expand_defs(
        &mut self,
        defs: &Definitions,
        recursion_detector: &mut RecursionDetection,
    ) -> Result<bool> {
        // it should be fastest just to filter the nodes and test edges rather than going through
        // .sinks

        let ops = self
            .node_indices()
            // is an Op
            .filter_map(|n| self[n].op().map(|_| OpNode(n)))
            // have not already expanded it
            .filter(|&n| !self.op_expanded(n))
            .collect::<Vec<_>>();

        let mut expanded = false;

        for op in ops {
            let x = self.expand_def(op, defs, recursion_detector)?;
            expanded |= x;
        }

        Ok(expanded)
    }

    fn expand_def(
        &mut self,
        opnode: OpNode,
        defs: &Definitions,
        recursion_detector: &mut RecursionDetection,
    ) -> Result<bool> {
        let opnode_ = NodeIndex::from(opnode);

        let op = self[opnode_]
            .op()
            .expect("opnode must be an Op variant")
            .0
            .clone();

        let impls = defs.impls();

        if !impls.contains_op(op.str()) {
            return Err(Error::op_not_found(&op, false));
        }

        let op_impls = impls
            .iter()
            .filter(|(name, _, _)| op.str() == name.as_str());

        recursion_detector.clear_cache();

        let mut expanded = false;

        for (name, key, im) in op_impls {
            // sub-root
            let cmd = match im {
                // always include an intrinsic
                Implementation::Intrinsic { loc: _, f } => self.0.add_node(AstNode::Intrinsic {
                    op: op.clone(),
                    intrinsic: f.clone(),
                }),
                Implementation::Definition(def) => {
                    // first, test that this def is not already being used in the call chain,
                    // detecting recursion.
                    // make an exception for unkeyed impls, since the path taken may be differing
                    let id = key.map(|t| format!("{}:{}", name, t));

                    if id
                        .as_ref()
                        .map(|id| recursion_detector.detect(self, opnode, id))
                        .unwrap_or(false)
                    {
                        continue;
                    }

                    // no recursion detected, this id will need to be added to the detector
                    let tys = defs.types();
                    let params = def
                        .params
                        .iter()
                        .map(|p| Parameter::from_ast(p, tys))
                        .collect::<Result<Vec<Parameter>>>()?;

                    let cmd = self.0.add_node(AstNode::Def {
                        expr: def.expr.tag.clone(),
                        params,
                    });
                    let expr = self.flatten_expr(def.expr.clone())?;
                    // link cmd to expr
                    self.0.add_edge(cmd, expr, Relation::Normal);
                    // add the id into the recursion detector
                    if let Some(id) = id {
                        recursion_detector.add_id(cmd, id);
                    }

                    cmd
                }
            };

            let g = &mut self.0;

            // link the op with this subroot, keyed by the key!
            g.add_edge(opnode_, cmd, Relation::Keyed(key.cloned()));

            // link the op's terms to this subroot
            // REVERSED since the neighbors are returned in reverse add order
            // flags first
            for (i, flag) in g
                .edges(opnode_)
                .filter(|e| e.weight().is_normal())
                .filter(|e| g[e.target()].flag().is_some())
                .map(|e| e.target())
                .collect::<Vec<_>>()
                .into_iter()
                .rev()
                .enumerate()
            {
                g.add_edge(flag, cmd, Relation::Term(i as u8));
            }
            // now args, normal connections that aren't flags
            for (i, arg) in g
                .edges(opnode_)
                .filter(|e| e.weight().is_normal())
                .filter(|e| g[e.target()].flag().is_none())
                .map(|e| e.target())
                .collect::<Vec<_>>()
                .into_iter()
                .rev()
                .enumerate()
            {
                g.add_edge(arg, cmd, Relation::Term(i as u8));
            }

            // if we got this far, update the flag
            expanded = true;
        }

        Ok(expanded)
    }

    /// Returns if the op has been expanded already, that is, it has children with keyed types.
    fn op_expanded(&self, opnode: OpNode) -> bool {
        self.edges(opnode.into())
            .any(|e| matches!(e.weight(), Relation::Keyed(_)))
    }
}

#[derive(Default)]
struct RecursionDetection {
    def_ids: IndexMap<Str>,
    parent_ids: Option<Vec<Str>>,
}

impl RecursionDetection {
    pub fn clear_cache(&mut self) {
        self.parent_ids = None;
    }

    pub fn add_id<I: Into<Str>>(&mut self, node: NodeIndex, id: I) {
        self.def_ids.insert(node.index(), id.into());
    }

    /// Why is this mutable? The recursion detector utilises a lazily loaded path system to avoid
    /// having to compute paths when not needed.
    pub fn detect(&mut self, ag: &AstGraph, opnode: OpNode, id: &str) -> bool {
        if self.parent_ids.is_none() {
            let x = self.parent_ids(ag, opnode);
            self.parent_ids = Some(x);
        }

        self.detect_inner(id)
    }

    fn detect_inner(&self, id: &str) -> bool {
        // this should have Some, but can return false anyway
        self.parent_ids
            .as_ref()
            .map(|paths| paths.iter().any(|i| i == id))
            .expect("should have paths")
    }

    fn parent_ids(&self, ag: &AstGraph, opnode: OpNode) -> Vec<Str> {
        let mut x = petgraph::algo::all_simple_paths(
            &ag.0,
            0.into(), // root node
            opnode.idx(),
            1,
            None,
        )
        .flat_map(|path: Vec<_>| {
            path.into_iter()
                .filter_map(|n| self.def_ids.get(&n.index()))
                .cloned()
        })
        .collect::<Vec<Str>>();

        x.reverse(); // small optimisation since recursion is generally from closest point

        x
    }
}

/// API.
impl AstGraph {
    /// Returns an iterator over the leaves of the graph.
    ///
    /// `filter` is used to specify a predicate for which nodes should be considered a 'sink'.
    /// So, if the filter is just `true` for any node, all nodes which do not have an outgoing
    /// edges would be returned.
    ///
    /// However, if the filter were to only return true for a `Op` variant node, the sinks would be
    /// the nodes which do not flow to another `Op` variant.
    ///
    /// This way, the sinks of a AST node variant can be found.
    pub fn sinks<F>(&self, filter: F) -> HashSet<NodeIndex>
    where
        F: Fn(NodeIndex) -> bool,
    {
        fn find_last_match<'a, F>(
            g: &'a AstGraph,
            sink: NodeIndex,
            filter: F,
        ) -> impl Iterator<Item = NodeIndex> + 'a
        where
            F: 'a + Fn(NodeIndex) -> bool + Copy,
        {
            let srcs = g.externals(Incoming);

            srcs.flat_map(move |src| {
                petgraph::algo::all_simple_paths::<Vec<_>, _>(&g.0, src, sink, 0, None)
                    .filter_map(move |v| v.into_iter().rev().find(|&n| filter(n)))
            })
        }

        let sinks = self.externals(Outgoing);

        let mut set = HashSet::default();

        for sink in sinks {
            if filter(sink) {
                // a sink matched the predicate, no need to walk path
                set.insert(sink);
            } else {
                set.extend(find_last_match(self, sink, &filter));
            }
        }

        set
    }

    /// Matches a specific implementation of a command (op) with the given input type.
    ///
    /// Uses type specificity to rank the matches.
    ///
    /// Returns `None` if no matches found which can occur if there are definitions keyed on
    /// specific types, but the input type does not match.
    pub fn get_impl(&self, opnode: OpNode, in_ty: &Type) -> Option<CmdNode> {
        opnode.debug_assert_is_op_node(self);

        let opnode = NodeIndex::from(opnode);

        let mut fallback = None;

        for edge in self.edges(opnode) {
            let wgt = edge.weight();
            if wgt == &Relation::Keyed(None) {
                fallback = Some(CmdNode(edge.target()));
            } else if matches!(wgt, Relation::Keyed(Some(t)) if t == in_ty) {
                return Some(CmdNode(edge.target())); // found a specific impl
            }
        }

        fallback
    }

    /// Get the arguments into a command node _in positional order_.
    pub fn get_args<N: Into<CmdNode>>(&self, node: N) -> Vec<ArgNode> {
        self.get_terms(node.into(), false).map(ArgNode).collect()
    }

    /// Get the flags into a command node _in positional order_.
    pub fn get_flags<N: Into<CmdNode>>(&self, node: N) -> Vec<Tag> {
        self.get_terms(node.into(), true)
            .map(|n| self[n].flag().expect("should be a flag variant"))
            .cloned()
            .collect()
    }

    fn get_terms(&self, node: CmdNode, flag: bool) -> impl Iterator<Item = NodeIndex> {
        debug_assert!(self.is_cmd_node(node.idx()), "expecting a command node");

        // the terms are the ones going _into_ the node, using the `Term` edge.
        // the process here is to construct a vec that gets filled in.
        // we PANIC if a position is not filled, that should be an internal logic error,
        let mut v = Vec::new();

        let terms = self
            .edges_directed(node.idx(), Incoming)
            .filter(|e| !(flag ^ self[e.source()].flag().is_some()))
            .filter_map(|e| e.weight().term().map(|i| (i, e.source())));

        for (i, node) in terms {
            let i = i as usize;
            if i >= v.len() {
                v.resize(i + 1, None);
            }
            v[i] = Some(node);
        }

        v.into_iter()
            .map(|x| x.expect("all positions should be populated"))
    }

    /// This node is a command node, that is, there exists an edge from an OpNode with a Keyed
    /// type.
    fn is_cmd_node(&self, node: NodeIndex) -> bool {
        self.edges_directed(node, Incoming)
            .any(|e| e.weight().is_key() && self[e.source()].op().is_some())
    }

    /// This node is an argument node, that is, matches the node type of an argument and has a
    /// single edge coming into it (from the op node).
    pub fn is_arg_node(&self, node: NodeIndex) -> bool {
        use AstNode::*;

        match self[node] {
            // these are always in argument positions
            Ident(_) | Num { .. } | Pound { .. } | Var(_) => true,
            // expr might be a root or under a Def
            Expr(_) => self
                // get incoming node
                .edges_directed(node, Incoming)
                .next()
                // check it is an op
                .map(|e| self[e.source()].op().is_some())
                // if no edge, would be a root
                .unwrap_or(false),
            Op { .. } | Def { .. } | Intrinsic { .. } | Flag(_) => false,
        }
    }

    /// Returns an iterator going from the root node to, and including, `to`.
    pub fn path_from_root(&self, to: NodeIndex) -> impl DoubleEndedIterator<Item = NodeIndex> {
        let mut v = vec![to];

        let mut n = to;

        while n != 0.into() {
            let parent = self
                .edges_directed(n, Direction::Incoming)
                .filter(|e| e.weight().term().is_none())
                .map(|e| e.source())
                .next()
                .expect("link should exist");
            v.push(parent);
            n = parent;
        }

        v.reverse();

        v.into_iter()
    }

    pub fn op_nodes(&self) -> impl Iterator<Item = OpNode> + '_ {
        self.node_indices()
            .filter_map(move |n| self[n].op().map(|_| OpNode(n)))
    }

    pub fn expr_nodes(&self) -> impl Iterator<Item = ExprNode> + '_ {
        self.node_indices()
            .filter_map(move |n| self[n].expr().map(|_| ExprNode(n)))
    }

    pub fn arg_nodes(&self) -> impl Iterator<Item = ArgNode> + '_ {
        self.node_indices()
            .filter_map(move |n| self.is_arg_node(n).then(|| ArgNode(n)))
    }

    pub fn def_nodes(&self) -> impl Iterator<Item = DefNode> + '_ {
        self.node_indices()
            .filter_map(move |n| self[n].def().map(|_| DefNode(n)))
    }
}

#[cfg(debug_assertions)]
impl AstGraph {
    pub fn debug_write_table_of_nodes(&self, buf: &mut String) {
        use std::fmt::Write;

        writeln!(buf, "```kserd").unwrap();
        writeln!(buf, r#"header = ["Index","AST Node"]"#).unwrap();
        writeln!(buf, "data = [").unwrap();

        for (idx, node) in self.node_indices().map(|i| (i, &self[i])) {
            writeln!(buf, "    [{},\"{}\"]", idx.index(), node).unwrap();
        }

        writeln!(buf, "]").unwrap();
        writeln!(buf, "rowslim = 200").unwrap();
        writeln!(buf, "```").unwrap();
    }

    pub fn debug_write_flowchart(&self, tg: &super::tygraph::TypeGraph, buf: &mut String) {
        use fmt::Write;

        super::debug_write_flowchart(
            self,
            buf,
            |_, _| true,
            |idx, node, buf| {
                let tynode = &tg[idx];
                write!(
                    buf,
                    "{idx} :: {ast} <br> {input} & {output}",
                    idx = idx.index(),
                    ast = node,
                    input = tynode.input,
                    output = tynode.output,
                )
            },
            |edge, buf| write!(buf, "{}", edge),
        )
        .unwrap()
    }
}

impl AstNode {
    /// If this is an op node, returns the `(op, blk)` tags.
    pub fn op(&self) -> Option<(&Tag, &Tag)> {
        match self {
            AstNode::Op { op, blk } => Some((op, blk)),
            _ => None,
        }
    }

    /// If this is a def node, returns the params as `Some`.
    pub fn def(&self) -> Option<&[Parameter]> {
        match self {
            AstNode::Def { expr: _, params } => Some(params.as_slice()),
            _ => None,
        }
    }

    /// If this is a flag node, returns the tag as Some.
    pub fn flag(&self) -> Option<&Tag> {
        match self {
            AstNode::Flag(x) => Some(x),
            _ => None,
        }
    }

    /// If this is a variable node, returns the tag as `Some`.
    pub fn var(&self) -> Option<&Tag> {
        match self {
            AstNode::Var(x) => Some(x),
            _ => None,
        }
    }

    /// If this is an expression node, returns the tag as Some.
    pub fn expr(&self) -> Option<&Tag> {
        match self {
            AstNode::Expr(x) => Some(x),
            _ => None,
        }
    }

    pub fn tag(&self) -> &Tag {
        use AstNode::*;

        match self {
            Op { op, blk: _ } => op,
            Intrinsic { op, intrinsic: _ } => op,
            Def { expr, params: _ } => expr,
            Flag(f) => f,
            Ident(s) => s,
            Num { val: _, tag } => tag,
            Pound { ch: _, tag } => tag,
            Var(v) => v,
            Expr(e) => e,
        }
    }
}

impl fmt::Display for AstNode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use AstNode::*;

        match self {
            Op { op, blk: _ } => write!(f, "Op({})", op.str()),
            Intrinsic {
                op: _,
                intrinsic: _,
            } => write!(f, "Intrinsic"),
            Def { expr: _, params: _ } => write!(f, "Def"),
            Flag(t) => write!(f, "Flag(--{})", t.str()),
            Ident(x) => write!(f, "Ident({})", x.str()),
            Num { val, tag: _ } => write!(f, "Num({})", val),
            Pound { ch, tag: _ } => write!(f, "Pound(#{})", ch),
            Var(t) => write!(f, "Var(${})", t.str()),
            Expr(t) => write!(f, "Expr({})", t.str()),
        }
    }
}

impl fmt::Debug for AstNode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl Relation {
    pub fn is_normal(&self) -> bool {
        matches!(self, Relation::Normal)
    }

    pub fn is_key(&self) -> bool {
        matches!(self, Relation::Keyed(_))
    }

    /// Returns if this relation is keyed, but **not** on a type.
    pub fn keyed_none(&self) -> bool {
        matches!(self, Relation::Keyed(None))
    }

    pub fn keyed(&self) -> Option<&Type> {
        match self {
            Relation::Keyed(x) => x.as_ref(),
            Relation::Normal => None,
            Relation::Term(_) => None,
        }
    }

    pub fn term(&self) -> Option<u8> {
        match self {
            Relation::Term(x) => Some(*x),
            _ => None,
        }
    }
}

impl fmt::Display for Relation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Relation::*;

        match self {
            Normal => write!(f, "Normal"),
            Keyed(Some(ty)) => write!(f, "Keyed({})", ty),
            Keyed(None) => write!(f, "Keyed(None)"),
            Term(x) => write!(f, "Term({})", x),
        }
    }
}

impl Parameter {
    fn from_ast(param: &ast::Parameter, tys: &types::Types) -> Result<Self> {
        let ast::Parameter { ident, ty } = param;

        let name = ident.clone();
        let ty = ty.as_ref();
        let ty = if ty.map(|t| t.str() == "Expr").unwrap_or(false) {
            ParameterTy::Expr
        } else {
            ty.map(|t| tys.get_using_tag(t))
                .transpose()?
                .map(Clone::clone)
                .map(ParameterTy::Specified)
                .unwrap_or(ParameterTy::Unspecified)
        };

        Ok(Self { name, ty })
    }

    /// This parameter should be evaluated at the call site.
    pub fn is_callsite_eval(&self) -> bool {
        match self.ty {
            ParameterTy::Unspecified | ParameterTy::Specified(_) => true,
            ParameterTy::Expr => false,
        }
    }

    /// This parameter is marked with `Expr` and should be passed through to be evaluated at the
    /// consuming execution block.
    pub fn is_exesite_eval(&self) -> bool {
        !self.is_callsite_eval()
    }

    pub fn ty(&self) -> Option<&Type> {
        match &self.ty {
            ParameterTy::Specified(ty) => Some(ty),
            ParameterTy::Unspecified | ParameterTy::Expr => None,
        }
    }
}

impl ParameterTy {
    pub fn is_expr(&self) -> bool {
        matches!(self, ParameterTy::Expr)
    }
}

impl OpNode {
    fn debug_assert_is_op_node(self, g: &AstGraph) {
        debug_assert!(g[self.idx()].op().is_some(), "expecting an op node");
    }

    /// Fetches the parent expression node which holds this block.
    pub fn parent(self, g: &AstGraph) -> ExprNode {
        self.debug_assert_is_op_node(g);

        g.edges_directed(self.idx(), Incoming)
            .filter(|e| e.weight().is_normal())
            .find_map(|e| g[e.source()].expr().map(|_| ExprNode(e.source())))
            .expect("op nodes should have a parent expr node")
    }

    /// Fetches the next block's opnode, if there is one.
    pub fn next(self, g: &AstGraph) -> Option<OpNode> {
        self.debug_assert_is_op_node(g);

        // in reverse order, so it is one _before_ self
        g.neighbors(self.parent(g).idx())
            .filter_map(|n| g[n].op().map(|_| OpNode(n)))
            .take_while(|&n| n != self)
            .last()
    }

    /// Fetches the previous block's opnode, if there is one.
    pub fn prev(self, g: &AstGraph) -> Option<OpNode> {
        self.debug_assert_is_op_node(g);

        // in reverse order, so it is one _after_ self
        g.neighbors(self.parent(g).idx())
            .filter_map(|n| g[n].op().map(|_| OpNode(n)))
            .skip_while(|&n| n != self)
            .nth(1) // skip self
    }

    pub fn op_tag(self, g: &AstGraph) -> &Tag {
        g[self.idx()].op().expect("will be an op").0
    }

    pub fn blk_tag(self, g: &AstGraph) -> &Tag {
        g[self.idx()].op().expect("will be an op").1
    }

    /// Iterates the associated command nodes with this op.
    pub fn cmds(self, g: &AstGraph) -> impl Iterator<Item = CmdNode> + '_ {
        self.debug_assert_is_op_node(g);

        // op connects to cmd nodes via a 'keyed' edge
        g.edges(self.idx())
            .filter(|e| e.weight().is_key())
            .map(|e| e.target())
            .map(CmdNode)
    }
}

impl ArgNode {
    pub fn tag(self, g: &AstGraph) -> &Tag {
        g[self.idx()].tag()
    }

    /// Fetches the block's OpNode that this argument comprises.
    pub fn op(self, g: &AstGraph) -> OpNode {
        debug_assert!(g.is_arg_node(self.idx()), "expecting an argument node");

        g.edges_directed(self.idx(), Incoming)
            .find_map(|e| e.weight().is_normal().then(|| e.source()))
            .map(OpNode)
            .expect("argument nodes should have a parent op node")
    }

    /// Try fetching a direct child op of this arg node.
    /// This only occurs if the argument variant is an expression.
    pub fn child_op(self, g: &AstGraph) -> Option<OpNode> {
        g[self.idx()].expr().map(|_| ExprNode(self.0).first_op(g))
    }
}

impl CmdNode {
    /// Fetch the parent OpNode from this command node.
    pub fn parent(self, g: &AstGraph) -> OpNode {
        debug_assert!(g.is_cmd_node(self.idx()), "expecting a command node");

        g.edges_directed(self.idx(), Incoming)
            .find_map(|e| e.weight().is_key().then(|| e.source()))
            .map(OpNode)
            .expect("command nodes should have a parent op node")
    }

    /// Returns if this command node is a def node.
    pub fn def(self, g: &AstGraph) -> Option<DefNode> {
        g[self.idx()].def().map(|_| DefNode(self.idx()))
    }
}

impl IntrinsicNode {
    /// Fetch the parent OpNode from this intrinsic node.
    pub fn parent(self, g: &AstGraph) -> OpNode {
        debug_assert!(
            matches!(g[self.idx()], AstNode::Intrinsic { .. }),
            "expecting an intrinsic node"
        );
        CmdNode::from(self).parent(g)
    }
}

impl DefNode {
    #[inline(always)]
    fn debug_assert_is_def_node(self, g: &AstGraph) {
        debug_assert!(
            matches!(g[self.idx()], AstNode::Def { .. }),
            "expecting a def node"
        );
    }

    /// Fetch the parent OpNode from this command node.
    pub fn parent(self, g: &AstGraph) -> OpNode {
        self.debug_assert_is_def_node(g);
        CmdNode::from(self).parent(g)
    }

    /// Fetch the def's expression from a definition node.
    pub fn expr(self, g: &AstGraph) -> ExprNode {
        self.debug_assert_is_def_node(g);

        g.neighbors(self.idx())
            .next()
            .map(ExprNode)
            .expect("definition node should have a sub expression")
    }

    pub fn params(self, g: &AstGraph) -> &[Parameter] {
        self.debug_assert_is_def_node(g);
        g[self.idx()].def().expect("filtered to def node")
    }
}

impl ExprNode {
    pub fn tag(self, g: &AstGraph) -> &Tag {
        g[self.idx()].tag()
    }

    /// Fetches the first block's op for this expression.
    pub fn first_op(self, g: &AstGraph) -> OpNode {
        debug_assert!(
            matches!(g[self.idx()], AstNode::Expr(_)),
            "expecting an expression node"
        );

        g.neighbors(self.idx())
            .filter_map(|n| g[n].op().map(|_| OpNode(n)))
            .last()
            .expect("all expressions have at least one block op node")
    }
}
