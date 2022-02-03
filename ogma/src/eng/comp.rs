//! Compilation.

use super::*;
use astgraph::{AstGraph, AstNode};
use graphs::*;
use tygraph::TypeGraph;

pub fn compile(expr: ast::Expression, defs: &Definitions, input_ty: Type) -> Result<()> {
    let ag = astgraph::init(expr, defs)?; // flatten and expand expr/defs
    let tg = TypeGraph::build(&ag);

    let mut compiler = Compiler {
        defs,
        ag,
        tg,
        flowed_edges: Default::default(),
        compiled_ops: Default::default(),
        compiled_exprs: Default::default(),
    };

    compiler.init_tg(); // initialise TG

    compiler.tg.set_root_input_ty(input_ty); // set the root input

    let mut err = None;

    while !compiler.finished() {
        eprintln!("Resolving TG");
        compiler.resolve_tg()?;

        eprintln!("Populating compiled expressions");
        if compiler.populate_compiled_expressions() {
            eprintln!("✅ SUCCESS");
            continue;
        }

        eprintln!("Compiling blocks");
        match compiler.compile_blocks() {
            Ok(()) => {
                eprintln!("✅ SUCCESS");
                continue;
            }
            Err(e) => err = Some(e),
        }

        eprintln!("Inferring inputs");
        if compiler.infer_inputs() {
            eprintln!("✅ SUCCESS");
            continue;
        }

        eprintln!("Inferring outputs");
        if compiler.infer_outputs() {
            eprintln!("✅ SUCCESS");
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

pub struct Compiler<'d> {
    pub defs: &'d Definitions,
    ag: AstGraph,
    tg: TypeGraph,
    /// The edges in the `tg` that have been resolved and flowed.
    flowed_edges: IndexSet,
    /// A map of **Op** nodes which have succesfully compiled into a `Step`.
    compiled_ops: IndexMap<Step>,
    /// A map of **Expr** nodes which have succesfully compiled into an evaluation stack.
    compiled_exprs: IndexMap<eval::Stack>,
}

impl<'d> Compiler<'d> {
    fn init_tg(&mut self) {
        // apply ast known types and link edges
        self.tg.apply_ast_types(&self.ag);
        self.tg.apply_ast_edges(&self.ag);
    }

    /// We can determine if compilation is finished by seeing if there is a root evaluation stack.
    fn finished(&self) -> bool {
        self.compiled_exprs.contains_key(&0)
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
                !self.compiled_ops.contains_key(&idx.index())
            // and the input has a type
            && !self.tg[idx].input.is_unknown()
            })
            .filter_map(|idx| {
                // and is a Op variant
                self.ag[idx].op().map(|_| OpNode(idx))
            })
            .collect::<Vec<_>>();

        let mut goto_resolve = false;
        let mut err = None;
        let mut chgs = Vec::new();

        for node in nodes {
            let in_ty = self.tg[node.idx()]
                .input
                .ty()
                .cloned()
                .expect("known input at this point");

            match self.compile_block(node, in_ty, &mut chgs) {
                Ok(step) => {
                    goto_resolve = true;
                    let out_ty = step.out_ty.clone();
                    let _is_empty = self.compiled_ops.insert(node.index(), step).is_none();
                    debug_assert!(
                        _is_empty,
                        "just replaced an already compiled step which should not happen"
                    );

                    // since this compilation was successful, the output type is known!
                    // the TG is updated with this information
                    chgs.push(tygraph::Chg::KnownOutput(node.idx(), out_ty));
                }
                Err(e) => err = Some(e),
            }
        }

        let tg_chgd = self.apply_tg_chgs(chgs.into_iter());

        (goto_resolve | tg_chgd)
            .then(|| ())
            .ok_or_else(|| err.expect("error should be some if unsuccesful"))
    }

    pub fn compile_block(
        &self,
        opnode: OpNode,
        in_ty: Type,
        chgs: &mut Vec<tygraph::Chg>,
    ) -> Result<Step> {
        let cmd_node = self
            .ag
            .get_impl(opnode, &in_ty)
            .ok_or_else(|| Error::op_not_found(self.ag[opnode.idx()].tag()))?;

        match &self.ag[cmd_node.idx()] {
            AstNode::Intrinsic { op } => {
                let block = Block::construct(self, IntrinsicNode(cmd_node.into()), in_ty, chgs);

                dbg!(block.op_tag());

                // TODO -- rather store the func in Intrinsic,
                Step::compile(self.defs.impls(), block)
            }
            AstNode::Def(params) => {
                // check if there exists an entry for the sub-expression,
                // if so, wrap that in a Step and call it done!
                let expr = self.ag.def_expr(DefNode(cmd_node.into()));
                match self.compiled_exprs.get(&expr.index()) {
                    Some(stack) => todo!("wrap in a step"),
                    None => Err(Error::incomplete_expr_compilation(
                        self.ag[expr.idx()].tag(),
                    )),
                }
            }
            x => unreachable!(
                "impl nodes are expected to be Intrinsic or Def, found: {:?}",
                x
            ),
        }
    }

    fn infer_inputs(&mut self) -> bool {
        // we get _lowest_ nodes that are:
        // 1. Op variants,
        // 2. are not compiled,
        // 3. have unknown inputs

        let infer_nodes = self.ag.sinks(|n| {
            // 1. op variants
            self.ag[n].op().is_some()
            // 2. not compiled
            && !self.compiled_ops.contains_key(&n.index())
            // 3. unknown input
            && self.tg[n].input.is_unknown()
        });

        let mut chgs = infer_nodes
            .into_iter()
            .map(OpNode) // we filter to just Ops
            .filter_map(|n| ty::infer::input(n, self).map(|t| (n, t)))
            .map(|(node, ty)| tygraph::Chg::InferInput(node.idx(), ty))
            .collect::<Vec<_>>();

        self.apply_tg_chgs(chgs.into_iter())
    }

    fn infer_outputs(&mut self) -> bool {
        // TODO wire in properly
        false
    }

    /// Populate the compiled expression map.
    ///
    /// Loops through incomplete expressions and tries to make an entry in the map if all blocks in
    /// the expression have a compiled step.
    ///
    /// Returns if the map gets updated.
    fn populate_compiled_expressions(&mut self) -> bool {
        let exprs = self
            .ag
            .node_indices()
            .filter_map(|n| self.ag[n].expr().map(|_| ExprNode(n)))
            .filter(|n| !self.compiled_exprs.contains_key(&n.index()))
            .filter(|n| self.tg[n.idx()].has_types())
            .collect::<Vec<_>>();

        let mut chgd = false;

        for expr in exprs {
            if let Some(stack) = eval::Stack::build(&self, expr) {
                chgd = true;
                let _is_empty = self.compiled_exprs.insert(expr.index(), stack).is_none();
                debug_assert!(
                    _is_empty,
                    "just replaced an already compiled expression stack which should not happen"
                );
            }
        }

        chgd
    }

    /// Returns if the TG was altered when applying the changes.
    fn apply_tg_chgs<C>(&mut self, chgs: C) -> bool
    where
        C: Iterator<Item = tygraph::Chg>,
    {
        chgs.map(|c| self.tg.apply_chg(c))
            .fold(false, std::ops::BitOr::bitor)
    }
}

impl<'a> Block<'a> {
    fn construct(
        compiler: &'a Compiler,
        node: IntrinsicNode,
        in_ty: Type,
        chgs: &'a mut Vec<tygraph::Chg>,
    ) -> Self {
        let opnode = compiler.ag.parent_opnode(node.into());
        let mut flags = compiler.ag.get_flags(node);
        let mut args = compiler.ag.get_args(node);
        let defs = &compiler.defs;

        flags.reverse();
        args.reverse();

        Block {
            node: opnode,
            in_ty,
            flags,
            args,
            args_count: 0,
            ag: &compiler.ag,
            tg: &compiler.tg,
            compiled_exprs: &compiler.compiled_exprs,
            tg_chgs: chgs,
            defs,
            #[cfg(debug_assertions)]
            output_ty: None,
        }
    }
}

impl eval::Stack {
    fn build(compiler: &Compiler, expr_node: ExprNode) -> Option<Self> {
        let Compiler {
            ag, compiled_ops, ..
        } = compiler;
        let expr_node = expr_node.idx();

        let just_op = |n: petgraph::prelude::NodeIndex| ag[n].op().map(|_| OpNode(n));

        let mut count = 0;
        let all_have_step = ag.neighbors(expr_node).filter_map(just_op).all(|op| {
            count += 1;
            compiled_ops.contains_key(&op.index())
        });

        if !all_have_step {
            return None;
        }

        let mut steps = Vec::with_capacity(count);
        steps.extend(
            ag.neighbors(expr_node)
                .filter_map(just_op)
                .map(|op| {
                    compiled_ops
                        .get(&op.index())
                        .expect("just checked it exists")
                })
                .cloned(),
        );

        let mut stack = Self::new(steps);

        #[cfg(debug_assertions)]
        stack.add_types(&compiler.tg[expr_node]);

        Some(stack)
    }

    #[cfg(debug_assertions)]
    fn add_types(&mut self, tynode: &graphs::tygraph::Node) {
        self.in_ty = tynode
            .input
            .ty()
            .expect("expressions input type should be known at this point")
            .clone();
        self.out_ty = tynode
            .output
            .ty()
            .expect("expressions output type should be known at this point")
            .clone();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Always uses input type of `Nil`.
    fn compile(expr: &str) -> Result<()> {
        let defs = &Definitions::default();
        let expr = lang::parse::expression(expr, Default::default(), defs).unwrap();

        super::compile(expr, defs, Type::Nil).map_err(|e| {
            eprintln!("{}", e);
            e
        })
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
        compile("ls | filter foo eq 'bar' | len").unwrap();
        compile("ls | filter foo eq 3 | len").unwrap();
        compile("ls | filter foo eq #n | len").unwrap();
        compile("ls | filter foo eq #t | len").unwrap();
        compile("ls | filter foo eq #f | len").unwrap();

        // now to test more complex expressions
        // TODO these expressions SHOULD fail the inferer, since `\\` takes _any_ type, it can not
        // infer what type `filter` is should be passing through.
        // This is interesting, and it would be good to get decent error messages explaining why
        // the inference failed and where to put a type
        //         compile("ls | filter foo eq { \\ #n } | len").unwrap();
        //         compile("ls | filter foo eq { \\ #t } | len").unwrap();
        //         compile("ls | filter foo eq { \\ #f } | len").unwrap();
        //         compile("ls | filter foo eq { \\ 3 } | len").unwrap();
        //         compile("ls | filter foo eq { \\ 'bar' } | len").unwrap();
    }

    #[test]
    fn compilation_test_06() {
        // lets test a def!
        compile("\\ 3 | > 2").unwrap();
    }
}
