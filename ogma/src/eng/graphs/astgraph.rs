use crate::prelude::*;
use kserd::Number;
use std::ops::Deref;

type Inner = petgraph::stable_graph::StableGraph<AstNode, (), petgraph::Directed, u32>;

#[derive(Debug)]
pub struct AstGraph(Inner);

// Note that we do not expose a mutable deref, keep mutation contained in this module.
impl Deref for AstGraph {
    type Target = Inner;
    fn deref(&self) -> &Inner {
        &self.0
    }
}

#[derive(Debug)]
pub enum AstNode {
    Op { op: Tag, blk: Tag },
    Flag(Tag),
    Ident(Tag),
    Num { val: Number, tag: Tag },
    Pound { ch: char, tag: Tag },
    Var(Tag),
    Expr(Tag),
}

/// Initialises the syntax graph decomposing the expression.
///
/// This:
/// 1. Flattens the [`ast::Expression`],
/// 2. Expands any _defs_,
/// 3. Repeats at 1. if defs are found.
pub fn init(expr: ast::Expression, defs: &Definitions) -> AstGraph {
    let mut graph = AstGraph(Default::default());

    graph.flatten_expr(expr);
    while graph.expand_defs(defs) {}

    graph
}

impl AstGraph {
    fn flatten_expr(&mut self, expr: ast::Expression) {
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
                g.add_edge(root, op, ()); // edge from the expression root to the op

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
                    g.add_edge(op, term, ()); // add a directed edge from op to the term

                    if let Some(blks) = blks {
                        q.push_back((term, blks));
                    }
                }
            }
        }
    }

    /// Returns `true` if definitions were found and expanded.
    fn expand_defs(&mut self, defs: &Definitions) -> bool {
        // TODO wire in
        false
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

    /// If this is a flag node, returns the tag as Some.
    pub fn flag(&self) -> Option<&Tag> {
        match self {
            AstNode::Flag(x) => Some(x),
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
            Flag(f) => f,
            Ident(s) => s,
            Num { val: _, tag } => tag,
            Pound { ch: _, tag } => tag,
            Var(v) => v,
            Expr(e) => e,
        }
    }
}
