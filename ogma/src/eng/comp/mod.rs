//! Compilation.

use super::*;

mod astgraph;
mod tygraph;

use ::petgraph::graph::NodeIndex;
use astgraph::{AstGraph, AstNode};
use tygraph::TypeGraph;

type IndexSet = crate::HashSet<usize>;
type IndexMap<V> = crate::HashMap<usize, V>;

pub fn compile(expr: ast::Expression, defs: &Definitions, input_ty: Type) -> Result<()> {
    let ag = astgraph::init(expr, defs); // flatten and expand expr/defs
    let tg = TypeGraph::build(&ag);

    let mut compiler = Compiler {
        defs,
        ag,
        tg,
        flowed_edges: IndexSet::default(),
        compiled_nodes: Default::default(),
    };

    compiler.init_tg(); // initialise TG

    compiler.tg.set_root_input_ty(input_ty); // set the root input

    while !compiler.finished() {
        compiler.resolve_tg();
        if compiler.compile_blocks() {
            continue;
        }
        if compiler.infer_inputs() {
            continue;
        }
        if compiler.infer_outputs() {
            continue;
        }

        // if we get here we should error, could not progress on any steps
        todo!("error!")
    }

    // TODO better output
    // - the ordered root steps
    // - the completed type graph
    // - ???
    Ok(())
}

struct Compiler<'d> {
    defs: &'d Definitions,
    ag: AstGraph,
    tg: TypeGraph,
    /// The edges in the `tg` that have been resolved and flowed.
    flowed_edges: IndexSet,
    /// A map of op nodes which have succesfully compiled into a `Step`.
    compiled_nodes: IndexMap<Step>,
}

impl<'d> Compiler<'d> {
    fn init_tg(&mut self) {
        // apply ast known types and link edges
        self.tg.apply_ast_types(&self.ag);
        self.tg.apply_ast_edges(&self.ag);
    }

    fn finished(&self) -> bool {
        self.ag
            .neighbors(0.into())
            .all(|i| self.compiled_nodes.contains_key(&i.index()))
    }

    fn resolve_tg(&mut self) {
        while self.tg.flow_types(&mut self.flowed_edges) {}
    }

    fn compile_blocks(&mut self) -> bool {
        // get indices which have known input types
        let nodes = self
            .ag
            .node_indices()
            .filter(|&idx| {
                // not already compiled
                !self.compiled_nodes.contains_key(&idx.index())
                // and is a Op variant
            && self.ag[idx].op().is_some()
            // and the input has a type
            && !self.tg[idx].input.is_unknown()
            })
            .collect::<Vec<_>>();

        let mut succeed = false;

        for node in nodes {
            let in_ty = self.tg[node]
                .input
                .ty()
                .expect("filtered to NOT unknown")
                .clone();
            let x = self.ag[node].op().expect("filtered to OP node");
            let (op_tag, blk_tag) = (x.0.clone(), x.1.clone());
            let vars = &mut Locals::default();
            let flags = self.create_block_flags(node).expect("filtered to OP node");
            let args = self.create_block_args(node).expect("filtered to OP node");
            let defs = self.defs;

            let block = Block {
                in_ty,
                blk_tag,
                op_tag,
                defs,
                vars,
                flags,
                args,
                args_count: 0,
                type_annotation: String::new(),
            };

            match Step::compile(defs.impls(), block) {
                Ok(step) => {
                    succeed = true;
                    let out_ty = step.out_ty.clone();
                    let _is_empty = self.compiled_nodes.insert(node.index(), step).is_none();
                    debug_assert!(
                        _is_empty,
                        "just replaced an already compiled step which should not happen"
                    );

                    // since this compilation was successful, the output type is known!
                    // the TG is updated with this information
                    self.tg.add_known_output(node, out_ty);
                }
                Err(_) => (),
            }
        }

        succeed
    }

    fn infer_inputs(&mut self) -> bool {
        // TODO wire in
        false
    }

    fn infer_outputs(&mut self) -> bool {
        // TODO wire in properly
        false
    }

    // TODO maybe remove this?
    // note that order returned is reversed (as a stack).
    fn create_block_flags(&self, opnode_idx: NodeIndex) -> Option<Vec<Tag>> {
        if self.ag[opnode_idx].op().is_some() {
            // neighbours are in reversed order, which matches the block flags order

            self.ag
                .neighbors(opnode_idx)
                .filter_map(|i| self.ag[i].flag())
                .cloned()
                .collect::<Vec<_>>()
                .into()
        } else {
            None
        }
    }

    // TODO remove this in favour of an index based system in future
    fn create_block_args(&self, opnode_idx: NodeIndex) -> Option<Vec<ast::Argument>> {
        use ast::Argument as Arg;
        use AstNode::*;

        if self.ag[opnode_idx].op().is_some() {
            // neighbours are in reversed order, which matches the block args order
            self.ag
                .neighbors(opnode_idx)
                .filter_map(|i| match &self.ag[i] {
                    Op { .. } | Flag(_) => None,
                    Ident(s) => Some(Arg::Ident(s.clone())),
                    Num { val, tag } => Some(Arg::Num(*val, tag.clone())),
                    Pound { ch, tag } => Some(Arg::Pound(*ch, tag.clone())),
                    Var(t) => Some(Arg::Var(t.clone())),
                    // note that expression would instead reference the AG/TG
                    Expr(e) => todo!("expressions are not support in this prototype: {}", e),
                })
                .collect::<Vec<_>>()
                .into()
        } else {
            None
        }
    }
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

    /// Always uses input type of `Nil`.
    fn compile(expr: &str) -> Result<()> {
        let defs = &Definitions::default();
        let expr = lang::parse::expression(expr, Default::default(), defs).unwrap();

        super::compile(expr, defs, Type::Nil)
    }

    #[test]
    fn compilation_test_01() {
        // simply just use `ls`
        assert!(compile("ls").is_ok());
    }

    #[test]
    fn compilation_test_02() {
        // ls then len, this tests the input works for len
        assert!(compile("ls | len").is_ok());
    }

    #[test]
    fn compilation_test_03() {
        // tests an inferred input, no defs or variables
        assert!(compile("ls | filter foo eq 'bar' | len").is_ok());
    }
}
