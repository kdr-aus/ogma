//! Compilation.

use super::*;

mod astgraph;
mod tygraph;

use astgraph::{AstGraph, AstNode};
use tygraph::TypeGraph;

pub fn compile(expr: ast::Expression) -> Result<()> {
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
        let (ag, tg) = init_graphs("filter foo < 3 | len");

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
        let (ag, mut tg) = init_graphs("filter foo < 3 | len | = #t");

        tg.apply_ast_types(&ag);

        assert_eq!(tg.node_count(), 9);

        use tygraph::Knowledge;
        assert_eq!(tg.node_weight(0.into()), Some(&Knowledge::Unknown)); // root
        assert_eq!(tg.node_weight(1.into()), Some(&Knowledge::Unknown)); // filter
        assert_eq!(tg.node_weight(2.into()), Some(&Knowledge::Known(Type::Str))); // foo
        assert_eq!(tg.node_weight(3.into()), Some(&Knowledge::Unknown)); // < 3
        assert_eq!(tg.node_weight(4.into()), Some(&Knowledge::Unknown)); // len
        assert_eq!(tg.node_weight(5.into()), Some(&Knowledge::Unknown)); // =
        assert_eq!(
            tg.node_weight(6.into()),
            Some(&Knowledge::Known(Type::Bool))
        ); // #t
        assert_eq!(tg.node_weight(7.into()), Some(&Knowledge::Unknown)); // <
        assert_eq!(tg.node_weight(8.into()), Some(&Knowledge::Known(Type::Num)));
        // 3
    }
}
