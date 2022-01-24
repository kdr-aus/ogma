use crate::prelude::*;
use kserd::Number;

type AstGraphInner = petgraph::graph::Graph<AstNode, ()>;
type TypeGraphInner = petgraph::graph::Graph<TyNode, ()>;
#[derive(Debug)]
struct AstGraph(AstGraphInner);
#[derive(Debug)]
struct TypeGraph(TypeGraphInner);

#[derive(Debug)]
enum AstNode {
    Op(Tag),
    Flag(Tag),
    Ident(Tag),
    Num { val: Number, tag: Tag },
    Pound { ch: char, tag: Tag },
    Var(Tag),
    Expr(Tag),
}

/// Initialises the syntax graph and the type graph by decomposing the expression.
fn init_graphs(expr: ast::Expression) -> (AstGraph, TypeGraph) {
    use ast::*;

    let mut g = AstGraphInner::default();

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
            let (op, terms) = blk.parts();

            let op = g.add_node(AstNode::Op(op));
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

    // clone the nodes of the graph, but do not care about the edges
    let mut ty = TypeGraph(g.map(|_, _| TyNode::Unknown, |_, _| ()));
    ty.0.clear_edges();

    let ast = AstGraph(g);

    (ast, ty)
}

#[derive(Debug, PartialEq, Eq)]
enum TyNode {
    Known(Type),
    Unknown,
}

impl TypeGraph {
    /// Apply _known_ types from the AST nodes.
    ///
    /// For instance, a number variant node can be assigned the type number.
    fn apply_ast_types(&mut self, ag: &AstGraph) {
        let ag = &ag.0;

        for nidx in ag.node_indices() {
            let node = &ag[nidx];

            use AstNode::*;
            let ty = match node {
                Op(_) | Flag(_) => None,
                Ident(_) => Some(Type::Str),
                Num { .. } => Some(Type::Num),
                Pound { ch: 'n', .. } => Some(Type::Nil),
                Pound { ch: 't', .. } | Pound { ch: 'f', .. } => Some(Type::Bool),
                Pound { .. } => None,
                Var(_) => None,
                Expr(_) => None
            };

            if let Some(ty) = ty.map(TyNode::Known) {
                let current = self
                    .0
                    .node_weight_mut(nidx)
                    .expect("Type and Ast graphs should have same indices");
                assert!(
                    matches!(current, TyNode::Unknown),
                    "overwriting a non-unknown type node"
                );
                *current = ty;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

        fn expr(s: &str) -> ast::Expression {
            lang::parse::expression(s, Default::default(), &Default::default()).unwrap()
        }

    #[test]
    fn expression_decomposition_checks() {
        let expr = expr("filter foo < 3 | len");

        let (ag, tg) = init_graphs(expr);
        let (ag, tg) = (ag.0, tg.0);

        dbg!(&ag);

        assert_eq!(ag.node_count(), 7);
        assert_eq!(ag.edge_count(), 6);

        assert_eq!(tg.node_count(), 7);
        assert_eq!(tg.edge_count(), 0);

        assert!(ag.contains_edge(0.into(), 1.into())); // root -> filter
        assert!(ag.contains_edge(0.into(), 4.into())); // root -> len
        assert!(ag.contains_edge(1.into(), 2.into())); // filter -> foo
        assert!(ag.contains_edge(1.into(), 3.into())); // filter -> < 3
        assert!(ag.contains_edge(3.into(), 5.into())); // < 3 -> <
        assert!(ag.contains_edge(5.into(), 6.into())); // < -> 3
    }

    #[test]
    fn assigning_ast_types() {
        let expr = expr("filter foo < 3 | len | = #t");

        let (ag, mut tg) = init_graphs(expr);
        tg.apply_ast_types(&ag);

        let tg = tg.0;

        assert_eq!(tg.node_count(), 9);

        assert_eq!(tg.node_weight(0.into()), Some(&TyNode::Unknown)); // root
        assert_eq!(tg.node_weight(1.into()), Some(&TyNode::Unknown)); // filter
        assert_eq!(tg.node_weight(2.into()), Some(&TyNode::Known(Type::Str))); // foo
        assert_eq!(tg.node_weight(3.into()), Some(&TyNode::Unknown)); // < 3
        assert_eq!(tg.node_weight(4.into()), Some(&TyNode::Unknown)); // len
        assert_eq!(tg.node_weight(5.into()), Some(&TyNode::Unknown)); // =
        assert_eq!(tg.node_weight(6.into()), Some(&TyNode::Known(Type::Bool))); // #t
        assert_eq!(tg.node_weight(7.into()), Some(&TyNode::Unknown)); // <
        assert_eq!(tg.node_weight(8.into()), Some(&TyNode::Known(Type::Num))); // 3
    }
}
