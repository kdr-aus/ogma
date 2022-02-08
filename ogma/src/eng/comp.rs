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
        locals: Default::default(),
    };

    compiler.init_tg(input_ty); // initialise TG

    // initialise an empty Locals into the first op node
    compiler.locals.insert(
        compiler
            .ag
            .neighbors(0.into())
            .filter(|&x| compiler.ag[x].op().is_some())
            .last()
            .expect("there should be a root Op node")
            .index(),
        Locals::default(),
    );

    let mut err = None;

    while !compiler.finished() {
        eprintln!("Resolving TG");
        compiler.resolve_tg()?;

        eprintln!("Populating compiled expressions");
        if compiler.populate_compiled_expressions() {
            eprintln!("✅ SUCCESS");
            continue;
        }

        eprintln!("Assigning variable types");
        if compiler.assign_variable_types() {
            eprintln!("✅ SUCCESS");
            continue;
        }

        eprintln!("Inserting available def locals");
        if compiler.insert_available_def_locals() {
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
        match compiler.infer_inputs() {
            Ok(true) => {
                eprintln!("✅ SUCCESS");
                continue;
            }
            Err(e) => err = Some(e),
            _ => (),
        }

        eprintln!("Inferring outputs");
        if compiler.infer_outputs() {
            eprintln!("✅ SUCCESS");
            continue;
        }

        // if we get here we should error, could not progress on any steps
        // output the state of the compiler...
        compiler.write_debug_report("debug-compiler.md");

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
    /// A map of **Op** nodes which have a _known **input** `Locals`_.
    locals: IndexMap<Locals>,
}

impl<'d> Compiler<'d> {
    pub fn ag(&self) -> &AstGraph {
        &self.ag
    }

    fn init_tg(&mut self, root_ty: Type) {
        // apply ast known types and link edges
        self.tg.apply_ast_types(&self.ag);
        self.tg.apply_ast_edges(&self.ag);

        self.tg.set_root_input_ty(root_ty); // set the root input
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
                Ok((step, locals)) => {
                    goto_resolve = true;
                    let out_ty = step.out_ty.clone();

                    // insert the compiled step into the map
                    let _is_empty = self.compiled_ops.insert(node.index(), step).is_none();
                    debug_assert!(
                        _is_empty,
                        "just replaced an already compiled step which should not happen"
                    );

                    // insert the returned, mutated, locals into the locals map (if it is some).
                    // need to insert it into the **next** op after this one.
                    if let Some(locals) = locals {
                        if let Some(next) = node.next(&self.ag) {
                            self.insert_locals(locals, next);
                        }
                    }

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
    ) -> Result<(Step, Option<Locals>)> {
        let cmd_node = self
            .ag
            .get_impl(opnode, &in_ty)
            .ok_or_else(|| Error::op_not_found(self.ag[opnode.idx()].tag()))?;

        match &self.ag[cmd_node.idx()] {
            AstNode::Intrinsic { op } => {
                let mut locals = self.locals.get(&opnode.index()).cloned();

                let block = Block::construct(self, cmd_node, in_ty, locals.as_mut(), chgs);

                // TODO -- rather store the func in Intrinsic,
                Step::compile(self.defs.impls(), block).map(|step| (step, locals))
            }
            AstNode::Def(params) => {
                // check if there exists an entry for the sub-expression,
                // if so, wrap that in a Step and call it done!
                let expr = DefNode(cmd_node.idx()).expr(&self.ag);
                match self.compiled_exprs.get(&expr.index()) {
                    Some(stack) => {
                        let step = Step::from(stack.clone());
                        let locals = self.locals.get(&opnode.index()).cloned();
                        Ok((step, locals))
                    }
                    None => {
                        // there is not, but we can add to the TG that this sub-expression will
                        // have input of `in_ty`.
                        chgs.push(tygraph::Chg::KnownInput(expr.idx(), in_ty));

                        Err(Error::incomplete_expr_compilation(
                            self.ag[expr.idx()].tag(),
                        ))
                    }
                }
            }
            x => unreachable!(
                "impl nodes are expected to be Intrinsic or Def, found: {:?}",
                x
            ),
        }
    }

    fn infer_inputs(&mut self) -> Result<bool> {
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

        let x = infer_nodes
            .into_iter()
            .map(OpNode) // we've filtered to just Ops
            .fold((Vec::new(), None), |(mut chgs, mut err), op| {
                match ty::infer::input(op, self) {
                    Ok(ty) => chgs.push(tygraph::Chg::InferInput(op.idx(), ty)),
                    Err(e) if chgs.is_empty() => {
                        err = Some(e.crate_err(self.ag[op.idx()].op().unwrap().1))
                    }
                    _ => (),
                }

                (chgs, err)
            });

        match x {
            (chgs, Some(err)) if chgs.is_empty() => Err(err),
            (chgs, _) => Ok(self.apply_tg_chgs(chgs.into_iter())),
        }
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

    /// Assign types to variables by looking in the block's `Locals`.
    ///
    /// Assigns types to variables by seeing if there is an input `Locals` for the block's Op, and
    /// checking for the variable in that locals.
    ///
    /// If the TG is altered, returns `true`.
    fn assign_variable_types(&mut self) -> bool {
        let chgs = self
            .ag
            .node_indices()
            // just get the variables
            .filter_map(|n| self.ag[n].var().map(|v| (n, v)))
            // output type is unknown
            .filter(|(n, _)| self.tg[*n].output.is_unknown())
            // map in if has a Locals
            .filter_map(|(n, v)| {
                let opnode = ArgNode(n).op(&self.ag);
                self.locals.get(&opnode.index()).map(|l| (n, v, l))
            })
            .filter_map(|(n, v, l)| {
                l.get(v.str()).map(|v| match v {
                    Local::Var(v) => tygraph::Chg::KnownOutput(n, v.ty().clone()),
                    Local::Param(x) => tygraph::Chg::KnownOutput(n, x.out_ty().clone()),
                })
            })
            .collect::<Vec<tygraph::Chg>>();

        self.apply_tg_chgs(chgs.into_iter())
    }

    /// Returns if the TG was altered when applying the changes.
    fn apply_tg_chgs<C>(&mut self, chgs: C) -> bool
    where
        C: Iterator<Item = tygraph::Chg>,
    {
        chgs.map(|c| self.tg.apply_chg(c))
            .fold(false, std::ops::BitOr::bitor)
    }

    /// Inserts a locals _input_ entry into the locals map.
    /// This function is recursive, it walks through child expression arguments and also inserts
    /// the locals entry into the _first_ op node.
    fn insert_locals(&mut self, locals: Locals, op: OpNode) {
        let _is_empty = self.locals.insert(op.index(), locals.clone()).is_none();

        debug_assert!(
            _is_empty,
            "just replaced an already populated locals, which should not happen"
        );

        // repeat this process for each expr argument
        let ops = self
            .ag
            .neighbors(op.idx())
            .filter_map(|n| self.ag[n].expr().map(|_| ExprNode(n)))
            .map(|e| e.first_op(&self.ag))
            .collect::<Vec<_>>();

        for op in ops {
            self.insert_locals(locals.clone(), op);
        }
    }

    /// Looks at the `Def` command nodes and builds a `Locals` for the first op if:
    /// 1. The parent op has an available locals to scaffold off, and
    /// 2. _All_ parameters have a known type.
    fn insert_available_def_locals(&mut self) -> bool {
        struct D {
            def: DefNode,
            parent: OpNode,
            first: OpNode,
            in_ty: Type,
        }

        // repeat the process since a Def might have sub-Defs which would get processed by this.
        let mut defs = Vec::new();
        let mut skip = HashSet::default();

        let mut chgd = false;
        let tg_chgs = &mut Vec::new();

        loop {
            let getdefs = self
                .ag
                .node_indices()
                // filter to just Def nodes
                .filter_map(|n| self.ag[n].def().map(|_| DefNode(n)))
                // skip any defs previously processed
                .filter(|def| !skip.contains(def))
                // map to a D structure
                .map(|def| D {
                    def,
                    parent: def.parent(&self.ag),
                    first: def.expr(&self.ag).first_op(&self.ag),
                    in_ty: Type::Nil,
                })
                // check that the op does not already have a locals map
                .filter(|d| !self.locals.contains_key(&d.first.index()))
                // get the input type of parent block
                .filter_map(|d| {
                    self.tg[d.parent.idx()].input.ty().map(|ty| D {
                        in_ty: ty.clone(),
                        ..d
                    })
                })
                // get the Locals of the parent Op node
                .filter_map(|d| self.locals.get(&d.parent.index()).map(|l| (d, l.clone())));

            defs.clear();
            defs.extend(getdefs);

            if defs.is_empty() {
                break; // finish the loop, no more to do
            }

            for (d, locals) in defs.drain(..) {
                let D {
                    def,
                    parent: _,
                    first,
                    in_ty,
                } = d;

                skip.insert(def);

                let params = self.ag[def.idx()].def().expect("filtered to def node");

                if let Ok(locals) = locals.inject_params(self, params, def, in_ty, tg_chgs) {
                    chgd = true;
                    self.insert_locals(locals, first);
                }
            }
        }

        let tg_chgd = self.apply_tg_chgs(tg_chgs.drain(..));

        chgd || tg_chgd
    }
}

#[cfg(debug_assertions)]
impl<'a> Compiler<'a> {
    pub fn write_debug_report<F: AsRef<std::path::Path>>(&self, file: F) {
        use std::fmt::Write;
        let mut report = String::new();

        writeln!(&mut report, "# Compiler Debug Report").unwrap();

        writeln!(&mut report, "## AST Graph Nodes").unwrap();
        writeln!(&mut report, "---").unwrap();
        self.ag.debug_write_table_of_nodes(&mut report);

        writeln!(&mut report, "## AST Graph Chart").unwrap();
        writeln!(&mut report, "---").unwrap();
        self.ag.debug_write_flowchart(&self.tg, &mut report);

        writeln!(&mut report, "## Type Graph Chart").unwrap();
        writeln!(&mut report, "---").unwrap();
        self.tg.debug_write_flowchart(&self.ag, &mut report);

        writeln!(&mut report, "## Current Locals").unwrap();
        writeln!(&mut report, "---").unwrap();
        self.debug_locals_map(&mut report).unwrap();

        let path = file.as_ref();

        std::fs::write(path, report).unwrap();
    }

    fn debug_locals_map(&self, buf: &mut String) -> std::fmt::Result {
        use std::fmt::Write;

        writeln!(buf, "```")?;
        for (n, _locals) in self.locals.iter() {
            writeln!(
                buf,
                "{} :: {}",
                n,
                self.ag[petgraph::prelude::NodeIndex::from(*n as u32)]
            )?;
        }
        writeln!(buf, "```")?;

        Ok(())
    }
}

impl<'a> Block<'a> {
    fn construct(
        compiler: &'a Compiler,
        node: CmdNode,
        in_ty: Type,
        locals: Option<&'a mut Locals>,
        chgs: &'a mut Vec<tygraph::Chg>,
    ) -> Self {
        let opnode = node.parent(&compiler.ag);
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
            locals,
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

impl Locals {
    pub fn inject_params(
        mut self,
        compiler: &Compiler,
        params: &[astgraph::Parameter],
        defnode: DefNode,
        blk_in_ty: Type,
        tygraph_chgs: &mut Vec<tygraph::Chg>,
    ) -> Result<Self> {
        let mut blk = Block::construct(
            compiler,
            defnode.into(),
            blk_in_ty,
            Some(&mut self),
            tygraph_chgs,
        );

        dbg!(blk.op_tag());
        dbg!(blk.blk_tag());
        dbg!(blk.in_ty());

        let mut args = Vec::with_capacity(params.len());

        for astgraph::Parameter { name, ty } in params {
            dbg!(name, ty);
            let arg = blk.next_arg()?.supplied(None)?;

            let arg = match ty {
                Some(ty) => arg.returns(ty.clone())?,
                None => arg,
            }
            .concrete()?;

            args.push((Str::new(name.str()), arg));
        }

        for (name, arg) in args {
            self.add_param(name, arg);
        }

        Ok(self)
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
        eprintln!("TEST #1 ------- \\ 3 | = 3");
        compile("\\ 3 | = 3").unwrap();

        eprintln!("TEST #1 ------- \\ 3 | > 2");
        compile("\\ 3 | > 2").unwrap();
    }

    #[test]
    fn compilation_test_07() {
        // initial variable testing
        compile("let $x | \\ $x").unwrap();
    }
}
