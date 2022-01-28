//! Compilation.

use super::*;

mod astgraph;
mod tygraph;

use astgraph::{AstGraph, AstNode};
use tygraph::TypeGraph;

pub fn compile(expr: ast::Expression, defs: &Definitions) -> Result<()> {
    let ag = astgraph::init(expr, defs); // flatten and expand expr/defs

    let mut tg = TypeGraph::build(&ag);

    // apply ast known types and link edges
    tg.apply_ast_types(&ag);
    tg.apply_ast_edges(&ag);

    todo!()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn init_graphs(expr: &str) -> (AstGraph, TypeGraph) {
        let defs = &Definitions::default();
        let expr = lang::parse::expression(expr, Default::default(), defs).unwrap();

        let ag = astgraph::init(expr, defs);
        let tg = TypeGraph::build(&ag);
        (ag, tg)
    }

    #[test]
    fn expression_decomposition_checks() {
        let (ag, tg) = init_graphs("filter foo eq 3 | len");

        dbg!(&ag);

        assert_eq!(ag.node_count(), 7);
        assert_eq!(ag.edge_count(), 6);

        assert_eq!(tg.node_count(), 7);
        assert_eq!(tg.edge_count(), 0);

        assert!(ag.contains_edge(0.into(), 1.into())); // root -> filter
        assert!(ag.contains_edge(0.into(), 4.into())); // root -> len
        assert!(ag.contains_edge(1.into(), 2.into())); // filter -> foo
        assert!(ag.contains_edge(1.into(), 3.into())); // filter -> eq 3
        assert!(ag.contains_edge(3.into(), 5.into())); // < 3 -> eq
        assert!(ag.contains_edge(5.into(), 6.into())); // eq -> 3
    }

    #[test]
    fn assigning_ast_types() {
        let (ag, mut tg) = init_graphs("filter foo eq 3 | len | = #t");

        tg.apply_ast_types(&ag);

        assert_eq!(tg.node_count(), 9);

        use tygraph::{Knowledge, Node};
        let def = || Node {
            input: Knowledge::Unknown,
            output: Knowledge::Unknown,
        };

        assert_eq!(tg.node_weight(0.into()), Some(&def())); // root
        assert_eq!(tg.node_weight(1.into()), Some(&def())); // filter
        assert_eq!(
            tg.node_weight(2.into()),
            Some(&Node {
                input: Knowledge::Unknown,
                output: Knowledge::Known(Type::Str)
            })
        ); // foo
        assert_eq!(tg.node_weight(3.into()), Some(&def())); // < 3
        assert_eq!(tg.node_weight(4.into()), Some(&def())); // len
        assert_eq!(tg.node_weight(5.into()), Some(&def())); // =
        assert_eq!(
            tg.node_weight(6.into()),
            Some(&Node {
                input: Knowledge::Unknown,
                output: Knowledge::Known(Type::Bool),
            })
        ); // #t
        assert_eq!(tg.node_weight(7.into()), Some(&def())); // eq
        assert_eq!(
            tg.node_weight(8.into()),
            Some(&Node {
                input: Knowledge::Unknown,
                output: Knowledge::Known(Type::Num)
            })
        ); // 3
    }

    #[test]
    fn ag_and_tg_with_tg_initialised() {
        let (ag, mut tg) = init_graphs("ls | filter foo eq 0 | len");

        tg.apply_ast_types(&ag);
        tg.apply_ast_edges(&ag);

        assert_eq!(ag.node_count(), 8);
        assert_eq!(ag.edge_count(), 7);

        assert_eq!(tg.node_count(), 8);
        assert_eq!(tg.edge_count(), 6);

        // Check AST graph edges
        assert!(ag.contains_edge(0.into(), 1.into())); // root -> ls
        assert!(ag.contains_edge(0.into(), 2.into())); // root -> filter
        assert!(ag.contains_edge(0.into(), 5.into())); // root -> len

        assert!(ag.contains_edge(2.into(), 3.into())); // filter -> foo
        assert!(ag.contains_edge(2.into(), 4.into())); // filter -> eq 0

        assert!(ag.contains_edge(4.into(), 6.into())); // eq 0 -> eq
        assert!(ag.contains_edge(6.into(), 7.into())); // eq -> 0

        // Type graph nodes
        use tygraph::{Flow, Knowledge, Node};
        let def = || Node {
            input: Knowledge::Unknown,
            output: Knowledge::Unknown,
        };

        assert_eq!(tg.node_weight(0.into()), Some(&def())); // root
        assert_eq!(tg.node_weight(1.into()), Some(&def())); // ls
        assert_eq!(tg.node_weight(2.into()), Some(&def())); // filter
        assert_eq!(
            tg.node_weight(3.into()),
            Some(&Node {
                input: Knowledge::Unknown,
                output: Knowledge::Known(Type::Str)
            })
        ); // foo
        assert_eq!(tg.node_weight(4.into()), Some(&def())); // eq 0
        assert_eq!(tg.node_weight(5.into()), Some(&def())); // len
        assert_eq!(tg.node_weight(6.into()), Some(&def())); // eq
        assert_eq!(
            tg.node_weight(7.into()),
            Some(&Node {
                input: Knowledge::Unknown,
                output: Knowledge::Known(Type::Num),
            })
        ); // 0

        dbg!(tg
            .edge_indices()
            .map(|i| tg.edge_endpoints(i))
            .collect::<Vec<_>>());

        // Type graph edges
        let getedge = |a: u32, b: u32| &tg[tg.find_edge(a.into(), b.into()).unwrap()];
        assert_eq!(getedge(0, 1), &Flow::II); // root -> ls: II
    }
}
