use crate::prelude::*;
use kserd::Number;

type AstGraphInner = petgraph::graph::Graph<AstNode, ()>;
type TypeGraphInner = petgraph::graph::Graph<(), ()>;
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
    let mut ty = TypeGraph(g.map(|_, _| (), |_, _| ()));
    ty.0.clear_edges();

    let ast = AstGraph(g);

    (ast, ty)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn expression_decomposition_checks() {
        fn expr(s: &str) -> ast::Expression {
            lang::parse::expression(s, Default::default(), &Default::default()).unwrap()
        }

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
}
