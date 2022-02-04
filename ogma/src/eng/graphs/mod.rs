use super::*;

pub mod astgraph;
pub mod tygraph;

// To add a bit of comp-time checking that the _correct_ node index is being passed around,
// I am going to implement struct wrappers which can iter-op with NodeIndex and move away from
// using a raw NodeIndex
macro_rules! wrapr {
    ($( $name:ident )*) => {
        $(
            #[derive(Copy, Clone, PartialEq, Eq, Debug)]
            pub struct $name(pub petgraph::prelude::NodeIndex);
            impl $name {
                pub fn idx(self) -> petgraph::prelude::NodeIndex {
                    self.0
                }
                pub fn index(self) -> usize {
                    self.0.index()
                }
            }
            impl From<$name> for petgraph::prelude::NodeIndex {
                fn from(n: $name) -> Self {
                    n.idx()
                }
            }
        )*
    };
}

wrapr!(OpNode CmdNode ArgNode ExprNode IntrinsicNode DefNode);

impl From<IntrinsicNode> for CmdNode {
    fn from(x: IntrinsicNode) -> Self {
        CmdNode(x.0)
    }
}

impl From<DefNode> for CmdNode {
    fn from(x: DefNode) -> Self {
        CmdNode(x.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use astgraph::*;
    use tygraph::*;

    fn init_graphs(expr: &str) -> (AstGraph, TypeGraph) {
        let defs = &Definitions::default();
        let expr = lang::parse::expression(expr, Default::default(), defs).unwrap();

        let ag = astgraph::init(expr, defs).unwrap();
        let tg = TypeGraph::build(&ag);
        (ag, tg)
    }

    fn check_relation(g: &AstGraph, from: u32, to: u32, edgeidx: u32, v: Relation) {
        assert_eq!(g.find_edge(from.into(), to.into()), Some(edgeidx.into()));
        assert_eq!(g.edge_weight(edgeidx.into()), Some(&v));
    }

    #[test]
    fn expression_decomposition_checks() {
        use AstNode::*;
        use Relation::*;

        let (ag, tg) = init_graphs("filter foo eq 3 | len");

        dbg!(&ag);

        assert!(matches!(ag.node_weight(0.into()), Some(Expr(_)))); // root
        assert!(matches!(ag.node_weight(1.into()), Some(Op { .. }))); // filter
        assert!(matches!(ag.node_weight(2.into()), Some(Ident(_)))); // foo
        assert!(matches!(ag.node_weight(3.into()), Some(Expr(_)))); // eq 3
        assert!(matches!(ag.node_weight(4.into()), Some(Op { .. }))); // len
        assert!(matches!(ag.node_weight(5.into()), Some(Op { .. }))); // eq
        assert!(matches!(ag.node_weight(6.into()), Some(Num { .. }))); // 3
        assert!(matches!(ag.node_weight(7.into()), Some(Intrinsic { .. }))); // filter intrinsic
        assert!(matches!(ag.node_weight(8.into()), Some(Intrinsic { .. }))); // len intrinsic
        assert!(matches!(ag.node_weight(9.into()), Some(Intrinsic { .. }))); // eq intrinsic
        assert!(matches!(ag.node_weight(10.into()), None));

        assert_eq!(ag.node_count(), 10);
        assert_eq!(ag.edge_count(), 12);

        assert_eq!(tg.node_count(), 10);
        assert_eq!(tg.edge_count(), 0); // zeroed initially

        check_relation(&ag, 0, 1, 0, Normal); // root -> filter
        check_relation(&ag, 1, 2, 1, Normal); // filter -> foo
        check_relation(&ag, 1, 3, 2, Normal); // filter -> eq 3
        check_relation(&ag, 0, 4, 3, Normal); // root -> len
        check_relation(&ag, 3, 5, 4, Normal); // eq 3 -> eq
        check_relation(&ag, 5, 6, 5, Normal); // eq -> 3
        check_relation(&ag, 1, 7, 6, Keyed(None)); // filter -> intrinsic
        check_relation(&ag, 2, 7, 7, Term(0)); // foo -> intrinsic
        check_relation(&ag, 3, 7, 8, Term(1)); // eq 3 -> intrinsic
        check_relation(&ag, 4, 8, 9, Keyed(None)); // len -> intrinsic
        check_relation(&ag, 5, 9, 10, Keyed(None)); // eq -> intrinsic
        check_relation(&ag, 6, 9, 11, Term(0)); // 3 -> intrinsic
    }

    #[test]
    fn assigning_ast_types() {
        let (ag, mut tg) = init_graphs("filter foo eq 3 | len | eq #t");

        tg.apply_ast_types(&ag);

        assert_eq!(tg.node_count(), 13);

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
                input: Knowledge::Any,
                output: Knowledge::Known(Type::Str)
            })
        ); // foo
        assert_eq!(tg.node_weight(3.into()), Some(&def())); // < 3
        assert_eq!(tg.node_weight(4.into()), Some(&def())); // len
        assert_eq!(tg.node_weight(5.into()), Some(&def())); // eq
        assert_eq!(
            tg.node_weight(6.into()),
            Some(&Node {
                input: Knowledge::Any,
                output: Knowledge::Known(Type::Bool),
            })
        ); // #t
        assert_eq!(tg.node_weight(7.into()), Some(&def())); // eq
        assert_eq!(
            tg.node_weight(8.into()),
            Some(&Node {
                input: Knowledge::Any,
                output: Knowledge::Known(Type::Num)
            })
        ); // 3
    }

    #[test]
    fn ag_and_tg_with_tg_initialised() {
        use AstNode::*;
        use Relation::*;

        let (ag, mut tg) = init_graphs("ls | filter foo eq 0 | len");

        tg.apply_ast_types(&ag);
        tg.apply_ast_edges(&ag);

        dbg!(&ag);
        dbg!(&tg);

        assert_eq!(ag.node_count(), 12);
        assert_eq!(ag.edge_count(), 14);

        assert_eq!(tg.node_count(), 12);

        // Check AST graph edges
        assert!(matches!(ag.node_weight(0.into()), Some(Expr(_)))); // root
        assert!(matches!(ag.node_weight(1.into()), Some(Op { .. }))); // ls
        assert!(matches!(ag.node_weight(2.into()), Some(Op { .. }))); // filter
        assert!(matches!(ag.node_weight(3.into()), Some(Ident(_)))); // foo
        assert!(matches!(ag.node_weight(4.into()), Some(Expr(_)))); // eq 0
        assert!(matches!(ag.node_weight(5.into()), Some(Op { .. }))); // len
        assert!(matches!(ag.node_weight(6.into()), Some(Op { .. }))); // eq
        assert!(matches!(ag.node_weight(7.into()), Some(Num { .. }))); // 0
        assert!(matches!(ag.node_weight(8.into()), Some(Intrinsic { .. }))); // ls intrinsic
        assert!(matches!(ag.node_weight(9.into()), Some(Intrinsic { .. }))); // filter intrinsic
        assert!(matches!(ag.node_weight(10.into()), Some(Intrinsic { .. }))); // len intrinsic
        assert!(matches!(ag.node_weight(11.into()), Some(Intrinsic { .. }))); // eq intrinsic
        assert!(matches!(ag.node_weight(12.into()), None));

        check_relation(&ag, 0, 1, 0, Normal); // root -> ls
        check_relation(&ag, 0, 2, 1, Normal); // root -> filter
        check_relation(&ag, 0, 5, 4, Normal); // root -> len

        check_relation(&ag, 2, 3, 2, Normal); // filter -> foo
        check_relation(&ag, 2, 4, 3, Normal); // filter -> eq 0

        check_relation(&ag, 4, 6, 5, Normal); // eq 0 -> eq
        check_relation(&ag, 6, 7, 6, Normal); // eq -> 0

        check_relation(&ag, 1, 8, 7, Keyed(None)); // ls -> intrinsic
        check_relation(&ag, 2, 9, 8, Keyed(None)); // filter -> intrinsic
        check_relation(&ag, 5, 10, 11, Keyed(None)); // len -> intrinsic
        check_relation(&ag, 6, 11, 12, Keyed(None)); // eq -> intrinsic

        check_relation(&ag, 3, 9, 9, Term(0)); // foo -> filter intrinsic
        check_relation(&ag, 4, 9, 10, Term(1)); // eq 0 -> filter intrinsic

        check_relation(&ag, 7, 11, 13, Term(0)); // 0 -> eq intrinsic

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
                input: Knowledge::Any,
                output: Knowledge::Known(Type::Str)
            })
        ); // foo
        assert_eq!(tg.node_weight(4.into()), Some(&def())); // eq 0
        assert_eq!(tg.node_weight(5.into()), Some(&def())); // len
        assert_eq!(tg.node_weight(6.into()), Some(&def())); // eq
        assert_eq!(
            tg.node_weight(7.into()),
            Some(&Node {
                input: Knowledge::Any,
                output: Knowledge::Known(Type::Num),
            })
        ); // 0

        dbg!(tg
            .edge_indices()
            .map(|i| tg.edge_endpoints(i))
            .collect::<Vec<_>>());

        assert_eq!(tg.edge_count(), 6);

        // Type graph edges
        let getedge = |a: u32, b: u32| &tg[tg.find_edge(a.into(), b.into()).unwrap()];
        assert_eq!(getedge(0, 1), &Flow::II); // root -> ls: II
        assert_eq!(getedge(1, 2), &Flow::OI); // ls -> filter: OI
        assert_eq!(getedge(2, 5), &Flow::OI); // filter -> len: OI
        assert_eq!(getedge(5, 0), &Flow::OO); // len -> root: OO

        assert_eq!(getedge(4, 6), &Flow::II); // eq 0 -> eq: II
        assert_eq!(getedge(6, 4), &Flow::OO); // eq -> eq 0: OO
    }

    #[test]
    fn expression_decomposition_with_args_and_flags() {
        use AstNode::*;
        use Relation::*;

        let (ag, _) = init_graphs("range 0 --foo 'str' --bar");

        dbg!(&ag);

        assert!(matches!(ag.node_weight(0.into()), Some(Expr(_)))); // root
        assert!(matches!(ag.node_weight(1.into()), Some(Op { .. }))); // range
        assert!(matches!(ag.node_weight(2.into()), Some(Num { .. }))); // 0
        assert!(matches!(ag.node_weight(3.into()), Some(Flag(_)))); // foo
        assert!(matches!(ag.node_weight(4.into()), Some(Ident(_)))); // 'str'
        assert!(matches!(ag.node_weight(5.into()), Some(Flag(_)))); // bar
        assert!(matches!(ag.node_weight(6.into()), Some(Intrinsic { .. }))); // range intrinsic
        assert!(matches!(ag.node_weight(7.into()), None));

        assert_eq!(ag.node_count(), 7);
        assert_eq!(ag.edge_count(), 10);

        check_relation(&ag, 0, 1, 0, Normal); // root -> range
        check_relation(&ag, 1, 2, 1, Normal); // range -> 0
        check_relation(&ag, 1, 3, 2, Normal); // range -> 'str'
        check_relation(&ag, 1, 4, 3, Normal); // range -> --foo
        check_relation(&ag, 1, 5, 4, Normal); // range -> --bar
        check_relation(&ag, 1, 6, 5, Keyed(None)); // range -> intrinsic
        check_relation(&ag, 3, 6, 6, Term(0)); // --foo -> intrinsic
        check_relation(&ag, 5, 6, 7, Term(1)); // --bar -> intrinsic
        check_relation(&ag, 2, 6, 8, Term(0)); // 0 -> intrinsic
        check_relation(&ag, 4, 6, 9, Term(1)); // 'str' -> intrinsic
    }

    #[test]
    fn get_terms_test() {
        let (ag, _) = init_graphs("range 0 3 --foo --bar");

        let cmdnode = CmdNode(6.into());

        let args = ag.get_args(cmdnode);

        assert_eq!(args.len(), 2);

        assert!(matches!(ag[args[0].idx()], AstNode::Num { val, .. } if val == 0));
        assert!(matches!(ag[args[1].idx()], AstNode::Num { val, .. } if val == 3));

        let flags = ag.get_flags(cmdnode);

        assert_eq!(flags.len(), 2);

        assert_eq!(flags[0].str(), "foo");
        assert_eq!(flags[1].str(), "bar");
    }

    #[test]
    fn expression_decomposition_with_defs() {
        use AstNode::*;
        use Relation::*;

        let (ag, _) = init_graphs("= 3");

        dbg!(&ag);

        assert!(matches!(ag.node_weight(0.into()), Some(Expr(_)))); // root
        assert!(matches!(ag.node_weight(1.into()), Some(Op { .. }))); // =
        assert!(matches!(ag.node_weight(2.into()), Some(Num { .. }))); // 3
        assert!(matches!(ag.node_weight(3.into()), Some(Def(_)))); // Def
        assert!(matches!(ag.node_weight(4.into()), Some(Expr(_)))); // eq $rhs
        assert!(matches!(ag.node_weight(5.into()), Some(Op { .. }))); // eq
        assert!(matches!(ag.node_weight(6.into()), Some(Var(_)))); // $rhs
        assert!(matches!(ag.node_weight(7.into()), Some(Intrinsic { .. }))); // eq intrinsic
        assert!(matches!(ag.node_weight(8.into()), None));

        assert_eq!(ag.node_count(), 8);
        assert_eq!(ag.edge_count(), 9);

        check_relation(&ag, 0, 1, 0, Normal); // root -> =
        check_relation(&ag, 1, 2, 1, Normal); // = -> 3
        check_relation(&ag, 4, 5, 2, Normal); // eq $rhs -> eq
        check_relation(&ag, 5, 6, 3, Normal); // eq -> $rhs
        check_relation(&ag, 3, 4, 4, Normal); // Def -> eq $rhs
        check_relation(&ag, 1, 3, 5, Keyed(None)); // = -> Def
        check_relation(&ag, 2, 3, 6, Term(0)); // 3 -> Def
        check_relation(&ag, 5, 7, 7, Keyed(None)); // = -> Def
        check_relation(&ag, 6, 7, 8, Term(0)); // 3 -> Def
    }

    #[test]
    fn def_tg_linking() {
        let (ag, mut tg) = init_graphs("= 3");

        tg.apply_ast_types(&ag);
        tg.apply_ast_edges(&ag);

        dbg!(&ag);
        dbg!(&tg);

        // Assert some info about the AST nodes
        assert_eq!(ag.node_count(), 8);
        assert_eq!(ag.edge_count(), 9);
        // 0: = 3
        // 1: =
        // 2: 3
        // 3: Def ([ rhs ])
        // 4: eq $rhs
        // 5: eq
        // 6: $rhs
        // 7: eq Intrinsic

        // Type graph nodes
        use tygraph::{Flow, Knowledge, Node};
        let def = || Node {
            input: Knowledge::Unknown,
            output: Knowledge::Unknown,
        };

        assert_eq!(tg.edge_count(), 4);

        assert_eq!(tg.node_weight(0.into()), Some(&def())); // root
        assert_eq!(tg.node_weight(1.into()), Some(&def())); // =
        assert_eq!(
            tg.node_weight(2.into()),
            Some(&Node {
                input: Knowledge::Any,
                output: Knowledge::Known(Type::Num)
            })
        ); // 3
        assert_eq!(tg.node_weight(3.into()), Some(&def())); // def
        assert_eq!(tg.node_weight(4.into()), Some(&def())); // eq $rhs
        assert_eq!(tg.node_weight(5.into()), Some(&def())); // eq
        assert_eq!(tg.node_weight(6.into()), Some(&def())); // $rhs
        assert_eq!(tg.node_weight(7.into()), Some(&def())); // eq intrinsic

        // Type graph edges
        let getedge = |a: u32, b: u32| &tg[tg.find_edge(a.into(), b.into()).unwrap()];
        assert_eq!(getedge(0, 1), &Flow::II); // root -> =: II
        assert_eq!(getedge(1, 0), &Flow::OO); // = -> root: OO

        assert_eq!(getedge(4, 5), &Flow::II); // eq $rhs -> eq: II
        assert_eq!(getedge(5, 4), &Flow::OO); // eq -> eq $rhs: OO
    }
}
