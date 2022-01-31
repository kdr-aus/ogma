//! Compilation.

use super::*;
use astgraph::{AstGraph, AstNode};
use graphs::*;
use tygraph::TypeGraph;

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

    let mut err = None;

    while !compiler.finished() {
        eprintln!("resolving");
        compiler.resolve_tg()?;
        eprintln!("compiling blocks");
        match compiler.compile_blocks() {
            Ok(()) => {
                eprintln!("success");
                continue;
            }
            Err(e) => err = Some(e),
        }
        eprintln!("inferring inputs");
        if compiler.infer_inputs() {
            eprintln!("success");
            continue;
        }
        eprintln!("inferring outputs");
        if compiler.infer_outputs() {
            eprintln!("success");
            continue;
        }

        // if we get here we should error, could not progress on any steps
        return Err(err.unwrap_or_else(||
                Error {
                    cat: err::Category::Semantics,
                    desc: "compilation failed with no other errors".into(),
                    traces: vec![],
                    help_msg: Some("this is an internal bug, please report it at <https://github.com/kdr-aus/ogma/issues>".into())
        }
        ));
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

    fn resolve_tg(&mut self) -> Result<()> {
        loop {
            match self.tg.flow_types(&mut self.flowed_edges) {
                Ok(true) => (), // keep going!
                Ok(false) => break Ok(()),
                Err(reserr) => {
                    todo!("need to handle resolution error properly")
                }
            }
        }
    }

    /// Compile blocks step.
    ///
    /// Compiles blocks that are:
    /// - Not yet compiled.
    /// - Have a known input type.
    ///
    /// The return type indicates if the compiler loop should return to resolving stage.
    /// - If any block succeeds, `Ok(())` is returned.
    /// - If all blocks fail but the TG gets updated in the process (as in, it gains more
    /// knowledge), `Ok(())` is also returned.
    /// - If all blocks fail, the _last_ error message is returned.
    fn compile_blocks(&mut self) -> Result<()> {
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

        let mut goto_resolve = false;
        let mut err = None;

        for node in nodes {
            let mut chgs = Vec::new();
            let in_ty = self.tg[node]
                .input
                .ty()
                .cloned()
                .expect("known input at this point");

            let block = Block::construct(self, node, in_ty, &mut chgs);

            dbg!(block.op_tag());

            match Step::compile(self.defs.impls(), block) {
                Ok(step) => {
                    goto_resolve = true;
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
                Err(e) => err = Some(e),
            }

            dbg!(goto_resolve);
            dbg!(&chgs);
            goto_resolve = chgs.into_iter().fold(goto_resolve, |g, chg| {
                let chgd = self.tg.apply_chg(chg);
                g | chgd
            });
            dbg!(goto_resolve);
        }

        goto_resolve
            .then(|| ())
            .ok_or_else(|| err.expect("error should be some if unsuccesful"))
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

    fn create_block_args(&self, opnode_idx: NodeIndex) -> Option<Vec<NodeIndex>> {
        use AstNode::*;

        if self.ag[opnode_idx].op().is_some() {
            // neighbours are in reversed order, which matches the block args order
            self.ag
                .neighbors(opnode_idx)
                .filter(|&i| {
                    matches!(
                        &self.ag[i],
                        Ident(_) | Num { .. } | Pound { .. } | Var(_) | Expr(_)
                    )
                })
                .collect::<Vec<_>>()
                .into()
        } else {
            None
        }
    }
}

impl<'a> Block<'a> {
    fn construct(
        compiler: &'a Compiler,
        opnode: NodeIndex,
        in_ty: Type,
        chgs: &'a mut Vec<tygraph::Chg>,
    ) -> Self {
        let node = opnode;
        let flags = compiler
            .create_block_flags(node)
            .expect("filtered to OP node");
        let args = compiler
            .create_block_args(node)
            .expect("filtered to OP node");
        let defs = &compiler.defs;

        Block {
            node,
            in_ty,
            flags,
            args,
            args_count: 0,
            ag: &compiler.ag,
            tg: &compiler.tg,
            tg_chgs: chgs,
            defs,
            #[cfg(debug_assertions)]
            output_ty: None,
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
        // tests a nested expression
        compile("range 0 { \\ 3 } | len").unwrap();
        println!("Test 02 ----------------------------");
        compile("ls | range 0 { len } | len").unwrap();
    }

    #[test]
    fn compilation_test_04() {
        // tests argument resolving
        compile("range 0 3").unwrap();
    }

    #[test]
    fn compilation_test_05() {
        // tests an inferred input, no defs or variables
        assert!(compile("ls | filter foo eq 'bar' | len").is_ok());
    }
}
