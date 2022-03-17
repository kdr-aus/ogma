//! Compilation.

use super::*;
use astgraph::{AstGraph, AstNode};
use graphs::*;
use locals_graph::LocalsGraph;
use tygraph::TypeGraph;

mod infer;
mod params;
mod resolve_tg;

use params::*;

/// Compile an expression.
///
/// `input_ty` is optional. If not specified, `Nil` is
/// used.
pub fn compile<I>(expr: ast::Expression, defs: &Definitions, input_ty: I) -> Result<FullCompilation>
where
    I: Into<Option<Type>>,
{
    compile_with_seed_vars(
        expr,
        defs,
        input_ty.into().unwrap_or(Type::Nil),
        Default::default(),
    )
}

pub fn compile_with_seed_vars(
    expr: ast::Expression,
    defs: &Definitions,
    input_ty: Type,
    seed_vars: var::SeedVars,
) -> Result<FullCompilation> {
    eprintln!("COMPILING: '{}'", expr.tag);
    dbg!(&seed_vars);

    let ag = astgraph::init(expr, defs)?; // flatten and expand expr/defs
    let tg = TypeGraph::build(&ag);
    let lg = LocalsGraph::build(&ag);

    let mut compiler = Compiler {
        defs,
        ag,
        tg,
        lg,
        flowed_edges: Default::default(),
        compiled_ops: Default::default(),
        compiled_exprs: Default::default(),
        output_infer_opnode: None,
        callsite_params: Default::default(),
        inferrence_depth: 0,
    };

    compiler.init_tg(input_ty); // initialise TG

    compiler.lg.seed(seed_vars);

    dbg!(&compiler.lg);

    let mut compiler = compiler.compile(ExprNode(0.into()))?;

    let err = "should exist on successful compilation";

    // NOTE: this can be used to investigate compilation/evaluation issues by visualising the
    // compiler state. gated by a compilation flag, it must be turned off for release modes
    compiler.write_debug_report("debug-compiler.md");

    Ok(FullCompilation {
        eval_stack: compiler.compiled_exprs.remove(&0).expect(err), // root expr stack
        env: Environment::new(&compiler.lg),
    })
}

pub struct FullCompilation {
    pub eval_stack: eval::Stack,
    pub env: Environment,
}

// TODO: check sizing, maybe box this??
#[derive(Clone)]
pub struct Compiler<'d> {
    pub defs: &'d Definitions,
    ag: AstGraph,
    tg: TypeGraph,
    lg: LocalsGraph,
    /// The edges in the `tg` that have been resolved and flowed.
    flowed_edges: IndexSet,
    /// A map of **Op** nodes which have succesfully compiled into a `Step`.
    compiled_ops: IndexMap<Step>,
    /// A map of **Expr** nodes which have succesfully compiled into an evaluation stack.
    compiled_exprs: IndexMap<eval::Stack>,
    /// A op node which has been flag for output inferrence.
    output_infer_opnode: Option<OpNode>,
    /// A map of **Def** nodes which have had their call site parameters prepared as variables.
    callsite_params: IndexMap<Vec<CallsiteParam>>,
    /// Depth limit of inference to loop down to.
    inferrence_depth: u32,
}

trait BreakOn {
    fn idx(self) -> usize;
}
impl BreakOn for ExprNode {
    fn idx(self) -> usize {
        self.index()
    }
}
impl BreakOn for OpNode {
    fn idx(self) -> usize {
        self.index()
    }
}

/// Common.
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

    // TODO box here
    fn compile<B: BreakOn>(mut self, break_on: B) -> Result<Self> {
        let mut err = None;

        let brk_key = &break_on.idx();
        while !(self.compiled_exprs.contains_key(brk_key)
            || self.compiled_ops.contains_key(brk_key))
        {
            self.write_debug_report("debug-compiler.md");

            eprintln!("Resolving TG");
            self.resolve_tg()?;

            eprintln!("Populating compiled expressions");
            if self.populate_compiled_expressions() {
                eprintln!("✅ SUCCESS");
                continue;
            }

            eprintln!("Assigning variable types");
            if self.assign_variable_types() {
                eprintln!("✅ SUCCESS");
                continue;
            }

            eprintln!("Inserting available def locals");
            if self.insert_available_def_locals()? {
                eprintln!("✅ SUCCESS");
                continue;
            }

            eprintln!("Linking def's args for known paths");
            if self.link_known_def_path_args() {
                eprintln!("✅ SUCCESS");
                continue;
            }

            eprintln!("Compiling blocks");
            match self.compile_blocks() {
                Ok(()) => {
                    eprintln!("✅ SUCCESS");
                    continue;
                }
                // Break early if a hard error.
                Err(e) if e.hard => return Err(e),
                Err(e) => err = Some(e),
            }

            // TODO remove this
            //             eprintln!("Flow compiled op's locals");
            //             if self.flow_compiled_ops_locals() {
            //                 eprintln!("✅ SUCCESS");
            //                 continue;
            //             }

            eprintln!("Inferring inputs");
            match self.infer_inputs() {
                Ok(true) => {
                    eprintln!("✅ SUCCESS");
                    continue;
                }
                Err(e) => err = Some(e),
                _ => (),
            }

            eprintln!("Inferring outputs");
            if self.infer_outputs() {
                eprintln!("✅ SUCCESS");
                continue;
            }

            self.write_debug_report("debug-compiler.md");

            return Err(err.unwrap_or_else(||
                Error {
                    cat: err::Category::Internal,
                    desc: "compilation failed with no other errors".into(),
                    help_msg: Some("this is an internal bug, please report it at <https://github.com/kdr-aus/ogma/issues>".into()),
                        ..Error::default()
        }
        ));
        }

        Ok(self)
    }

    /// Returns if any of the graphs were altered when applying the changes.
    pub fn apply_graph_chgs<C>(&mut self, chgs: C) -> bool
    where
        C: Iterator<Item = graphs::Chg>,
    {
        use graphs::Chg::*;

        chgs.map(|c| match c {
            Tg(c) => self.tg.apply_chg(c),
            Lg(c) => self.lg.apply_chg(c),
        })
        .fold(false, std::ops::BitOr::bitor)
    }

    /// Inserts a locals _input_ entry into the locals map.
    /// This function is recursive, it walks through child expression arguments and also inserts
    /// the locals entry into the _first_ op node.
    fn insert_locals(&mut self, locals: &Locals, op: OpNode) {
        todo!("remove");
        //         let _is_empty = self.locals.insert(op.index(), locals.clone()).is_none();
        //
        //         debug_assert!(
        //             _is_empty,
        //             "just replaced an already populated locals, which should not happen"
        //         );
        //
        //         // repeat this process for each expr argument
        //         let ops = self
        //             .ag
        //             .neighbors(op.idx())
        //             .filter_map(|n| self.ag[n].expr().map(|_| ExprNode(n)))
        //             .map(|e| e.first_op(&self.ag))
        //             .collect::<Vec<_>>();
        //
        //         for op in ops {
        //             self.insert_locals(locals, op);
        //         }
    }

    /// Iterates over def nodes that are deduced to be the compilation path.
    /// 
    /// It deducts the path by looking at the input type into the parent op, since this keys the
    /// impl to take. If the input type is not known yet it, it sees if there is only a singular
    /// path to take (and it is a def path).
    fn def_nodes_with_known_path(&self) -> impl Iterator<Item = DefNode> + '_ {
        self.ag.op_nodes()
            .filter_map(move |op| {
                match self.tg[op.idx()].input.ty() {
                    Some(ty) => self.ag.get_impl(op, ty).and_then(|cmd| cmd.def(&self.ag)),
                    None => {
                        let mut cmds = op.cmds(&self.ag);
                        let def = cmds.next().and_then(|cmd| cmd.def(&self.ag));
                        def.filter(|_| cmds.next().is_none())
                    }
                }
            })
    }
}

/// Populating compiled expressions.
impl<'d> Compiler<'d> {
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
}

/// Assigning variable types.
impl<'d> Compiler<'d> {
    /// Assign types to variables by looking in the block's `Locals`.
    ///
    /// Assigns types to variables by seeing if there is an input `Locals` for the block's Op, and
    /// checking for the variable in that locals.
    ///
    /// If the TG is altered, returns `true`.
    fn assign_variable_types(&mut self) -> bool {
        use tygraph::{Chg::*, Flow};

        let mut chgs = Vec::new();

        for node in self.ag.node_indices() {
            // just get the variables
            let var_tag = match self.ag[node].var() {
                Some(t) => t,
                None => continue,
            };

            // output type is unknown
            if !self.tg[node].output.is_unknown() {
                continue;
            }

            // map in if has a Locals
            let local = match self.lg.get(node, var_tag.str()) {
                Some(l) => l,
                None => continue,
            };

            match local {
                Local::Var(v) => {
                    chgs.push(KnownOutput(node, v.ty().clone()));
                    chgs.push(AnyInput(node));
                }
                Local::Ptr { to, tag: _ } => {
                    // connect the type flow from the pointed to arg node
                    chgs.push(AddEdge {
                        src: to.idx(),
                        dst: node,
                        flow: Flow::II,
                    });
                    chgs.push(AddEdge {
                        src: to.idx(),
                        dst: node,
                        flow: Flow::OO,
                    });
                }
            }
        }

        self.apply_graph_chgs(chgs.into_iter().map(Into::into))
    }
}

/// Linking def's args for known paths.
impl<'d> Compiler<'d> {
    fn link_known_def_path_args(&mut self) -> bool {
        // filter ops which are not compiled
        // filter to ops where the input type is known
        // get the cmd node, if a def, then this is known as the path to take

        let defnodes = self.def_nodes_with_known_path()
            // without compiled steps
            .filter(|def| !self.compiled_ops.contains_key(&def.parent(&self.ag).index()))
            .collect::<Vec<_>>();

        let mut chgd = false;

        for defnode in defnodes {
            let x = self.tg.link_def_arg_terms_with_ii(&self.ag, defnode);
            chgd |= x;
        }

        chgd
    }
}

/// Compiling blocks.
impl<'d> Compiler<'d> {
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

            let mut infer_output = false;

            match self.compile_block(node, in_ty, &mut chgs, &mut infer_output) {
                Ok(step) => {
                    goto_resolve = true;
                    let out_ty = step.out_ty.clone();

                    // insert the compiled step into the map
                    let _is_empty = self.compiled_ops.insert(node.index(), step).is_none();
                    debug_assert!(
                        _is_empty,
                        "just replaced an already compiled step which should not happen"
                    );

                    // since this compilation was successful, the output type is known!
                    // the TG is updated with this information
                    chgs.push(tygraph::Chg::KnownOutput(node.idx(), out_ty).into());

                    // we also seal off the op node in the locals graph, this op is not going to
                    // alter it's dependent locals maps
                    self.lg.seal_node(node.idx(), &self.ag);
                }
                Err(mut e) => {
                    if infer_output {
                        self.output_infer_opnode = Some(node);
                    }

                    // add a stack trace by looking at the def interfaces
                    let parents = self
                        .ag
                        .path_from_root(node.idx())
                        // add traces backwards
                        .rev()
                        // interface between def calls
                        .filter_map(|n| self.ag[n].def().map(|_| DefNode(n)))
                        // get the parent op
                        .map(|def| def.parent(&self.ag))
                        // use the block tage as the trace
                        .map(|op| op.blk_tag(&self.ag));

                    for parent in parents {
                        e = e.add_trace(parent);
                    }

                    err = Some(e);
                }
            }
        }

        let chgd = self.apply_graph_chgs(chgs.into_iter());

        (goto_resolve | chgd)
            .then(|| ())
            .ok_or_else(|| err.expect("error should be some if unsuccesful"))
    }

    pub fn compile_block(
        &self,
        opnode: OpNode,
        in_ty: Type,
        chgs: Chgs,
        infer_output: &mut bool,
    ) -> Result<Step> {
        let cmd_node = self
            .ag
            .get_impl(opnode, &in_ty)
            .ok_or_else(|| Error::op_not_found(self.ag[opnode.idx()].tag()))?;

        match &self.ag[cmd_node.idx()] {
            AstNode::Intrinsic { op, intrinsic } => {
                let block = Block::construct(self, cmd_node, in_ty, chgs, infer_output);

                intrinsic(block)
            }
            AstNode::Def { expr, params } => {
                // check if there exists an entry for the sub-expression,
                // if so, wrap that in a Step and call it done!
                let defnode = DefNode(cmd_node.idx());
                let expr = defnode.expr(&self.ag);
                match self.compiled_exprs.get(&expr.index()) {
                    Some(stack) => {
                        // map the callsite params into the **op** node's arguments (for eval)
                        // if there are no callsite params, but the stack exists, the def has been
                        // able to compile without param reference.
                        // This is okay! we just pass an empty params vector to be resolved, and it
                        // saves some processing and memory.
                        let params =
                            self.map_callsite_params_for_def_step(defnode, &in_ty, chgs)?;
                        let out_ty = self.tg[expr.idx()]
                            .output
                            .ty()
                            .cloned()
                            .expect("shoud be known if a stack exists");
                        Ok(Step::def(params, stack.clone(), out_ty))
                    }
                    None => {
                        // there is not, but we can add to the TG that this sub-expression will
                        // have input of `in_ty`.
                        chgs.push(tygraph::Chg::KnownInput(expr.idx(), in_ty).into());

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

    /// For a def step, a vector mapping callsite [`Argument`]s to [`Variable`]s is required.
    /// The argument construction is held off until the block compilation occurs. This function
    /// helps construct the arguments using a def's callsite_params entry.
    ///
    /// # Panics
    /// This function is meant to be called once a def's sub-expression has been successfully
    /// compiled. Assumptions are made that elements will exist. If they do not, this function will
    /// panic, and is most likely the cause of a logic bug.
    /// The exception are the argument's input and output types. These might still not be
    /// completely up to date, so alterations will impact the tg_chgs and should be proagated
    /// through.
    ///
    /// - `Compiler.locals` expects to have an entry for the def's parent op
    /// - `Compiler.callsite_params` expects to have an entry for the def
    ///   - **If one does not exist, it returns an empty vector**.
    /// - `CallsiteParam.arg_idx` should index into the def's argument list
    /// - the argument builder expects both input and output types of the argument to be known
    fn map_callsite_params_for_def_step(
        &self,
        def: DefNode,
        in_ty: &Type,
        chgs: Chgs,
    ) -> Result<Vec<(Variable, Argument)>> {
        let Compiler {
            defs,
            ag,
            tg,
            lg,
            flowed_edges,
            compiled_ops,
            compiled_exprs,
            output_infer_opnode,
            callsite_params,
            inferrence_depth,
        } = self;

        let args = ag.get_args(def);

        callsite_params
            .get(&def.index())
            .map(|x| x.as_slice())
            .unwrap_or(&[])
            .iter()
            .map(
                |CallsiteParam {
                     param,
                     var,
                     arg_idx,
                 }| {
                    let arg = args[*arg_idx as usize]; // indexing should be safe since it was built against the args
                    let arg = arg::ArgBuilder::new(
                        arg,
                        ag,
                        tg,
                        lg,
                        chgs,
                        Some(in_ty.clone()),
                        compiled_exprs,
                    )
                    .supplied(in_ty.clone());
                    let arg = match param.ty().cloned() {
                        Some(ty) => arg.and_then(|a| a.returns(ty)),
                        None => arg,
                    };
                    arg.and_then(|a| a.concrete()).map(|arg| (var.clone(), arg))
                },
            )
            .collect()
    }
}

/// Flow compiled op's locals.
impl<'d> Compiler<'d> {
    /// Flows locals about according to the following:
    ///
    /// 1. Op is compiled but next op has no locals.
    ///   - This may occur if the op can be compiled with `None` locals
    fn flow_compiled_ops_locals(&mut self) -> bool {
        todo!("remove this");

        //         let ops = self
        //             .ag
        //             .node_indices()
        //             // get just ops
        //             .filter_map(|n| self.ag[n].op().map(|_| OpNode(n)))
        //             .collect::<Vec<_>>();
        //
        //         let mut chgd = false;
        //
        //         for op in ops {
        //             let opidx = &op.index();
        //
        //             let compiled = self.compiled_ops.contains_key(opidx);
        //
        //             // 1. op is compiled, but next op has no locals
        //             if compiled {
        //                 if let Some(next) = op.next(&self.ag) {
        //                     match (
        //                         self.locals.get(opidx).cloned(),
        //                         self.locals.contains_key(&next.index()),
        //                     ) {
        //                         (Some(locals), false) => {
        //                             chgd = true;
        //                             self.insert_locals(&locals, next);
        //                         }
        //                         _ => (),
        //                     }
        //                 }
        //             }
        //         }
        //
        //         chgd
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

        writeln!(&mut report, "## Locals").unwrap();
        writeln!(&mut report, "---").unwrap();
        self.lg.debug_write(&mut report, &self.ag).unwrap();

        writeln!(&mut report, "## Current Compiled Ops").unwrap();
        writeln!(&mut report, "---").unwrap();
        self.debug_index_map(&self.compiled_ops, &mut report)
            .unwrap();

        let path = file.as_ref();

        std::fs::write(path, report).unwrap();
    }

    fn debug_index_map<T>(&self, map: &IndexMap<T>, buf: &mut String) -> std::fmt::Result {
        use std::fmt::Write;

        let mut keys = map.keys().copied().collect::<Vec<_>>();
        keys.sort_unstable();

        writeln!(buf, "```")?;
        for n in keys {
            writeln!(
                buf,
                "{} :: {}",
                n,
                self.ag[petgraph::prelude::NodeIndex::from(n as u32)]
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
        chgs: Chgs<'a>,
        output_infer: &'a mut bool,
    ) -> Self {
        let opnode = node.parent(&compiler.ag);
        let mut flags = compiler.ag.get_flags(node);
        let mut args = compiler.ag.get_args(node);
        let defs = &compiler.defs;

        flags.reverse();
        args.reverse();

        let Compiler {
            defs,
            ag,
            tg,
            lg,
            flowed_edges,
            compiled_ops,
            output_infer_opnode,
            callsite_params,
            compiled_exprs,
            inferrence_depth,
        } = compiler;

        Block {
            node: opnode,
            in_ty,
            flags,
            args,
            args_count: 0,
            ag,
            tg,
            lg,
            compiled_exprs,
            chgs,
            infer_output: output_infer,
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

        // .neighbors() returns in reverse order added.
        steps.reverse();

        let mut stack = Self::new(steps);

        #[cfg(debug_assertions)]
        stack.add_types(&compiler.tg[expr_node]);

        Some(stack)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Always uses input type of `Nil`.
    fn compile(expr: &str) -> Result<()> {
        compile_w_defs(expr, &Definitions::default())
    }

    fn compile_w_defs(expr: &str, defs: &Definitions) -> Result<()> {
        let expr = lang::parse::expression(expr, Default::default(), defs).unwrap();

        super::compile(expr, defs, None)
            .map_err(|e| {
                eprintln!("{}", e);
                e
            })
            .map(|_| ())
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

        eprintln!("TEST #2 ------- \\ 3 | > 2");
        compile("\\ 3 | > 2").unwrap();
    }

    #[test]
    fn compilation_test_07() {
        // initial variable testing
        compile("let $x | \\ $x").unwrap();
    }

    #[test]
    fn compilation_test_08() {
        // output inferring
        // no defs
        eprintln!("TEST #1 ------- ls | filter {{ get 'foo' | eq 3 }}");
        compile("ls | filter { get 'foo' | eq 3 }").unwrap();
        // with def
        eprintln!("TEST #2 ------- ls | filter {{ get 'foo' | > 3 }}");
        compile("ls | filter { get 'foo' | > 3 }").unwrap();

        // with Str
        // no defs
        eprintln!("TEST #1 ------- ls | filter {{ get 'foo' | eq 'bar' }}");
        compile("ls | filter { get 'foo' | eq 'bar' }").unwrap();
        // with def
        eprintln!("TEST #2 ------- ls | filter {{ get 'foo' | > 'bar' }}");
        compile("ls | filter { get 'foo' | > 'bar' }").unwrap();
    }

    #[test]
    fn compilation_test_09() {
        compile("ls | filter name != 'foo'").unwrap();
    }

    #[test]
    fn compilation_test_10() {
        let defs = &mut Definitions::default();

        let test = |s, defs: &_| {
            eprintln!("TESTING ::: {}", s);
            compile_w_defs(s, defs).unwrap();
        };

        test("\\3 | let $a | + $a", defs);
        test("\\3 | let $a | + { \\$a }", defs);
        test("\\3 | let $a | + { \\$a | + 3 }", defs);
        test("\\3 | let $a | + { \\3 | + $a }", defs);

        lang::process_definition("def foo (rhs) { + $rhs }", Default::default(), None, defs)
            .unwrap();
        test("\\3 | foo 3", defs);

        lang::process_definition(
            "def foo (rhs) { \\3 | + $rhs }",
            Default::default(),
            None,
            defs,
        )
        .unwrap();
        test("\\3 | foo 4", defs);

        lang::process_definition("def-ty Point { x:Num }", Default::default(), None, defs).unwrap();
        lang::process_definition(
            "def + Point (rhs) { Point { get x | + { \\$rhs | get x }}}",
            Default::default(),
            None,
            defs,
        )
        .unwrap();
        test("Point 3 | + Point 4", defs);
    }

    #[test]
    fn compilation_test_11() {
        compile("\\ 3 | let $a | + { + { + { \\ $a } } }").unwrap();
    }

    #[test]
    fn compilation_test_12() {
        compile("\\ { let $b | \\ #t | \\ $b }").unwrap();
    }

    #[test]
    fn compilation_test_13() {
        let defs = &mut Definitions::default();

        lang::process_definition("def foo () { > 3 | \\ 3 }", Default::default(), None, defs)
            .unwrap();

        compile_w_defs("\\ 3 | > { foo }", defs).unwrap();
    }

    #[test]
    fn compilation_test_14() {
        let x = compile("\\ $x").unwrap_err().to_string();
        println!("{}", x);
        assert_eq!(
            &x,
            "Semantics Error: variable `x` does not exist
--> shell:3
 | \\ $x
 |    ^ `x` not in scope
--> help: variables must be in scope and can be defined using the `let` command
"
        );
    }

    #[test]
    fn compilation_test_15() {
        // testing Expr params
        let x = compile("Table | last { get foo --Num }").unwrap();

        let defs = &mut Definitions::default();
    }

    #[test]
    fn compilation_test_16() {
        // testing that defs do not resolve their OO if other defs are available
        let defs = &mut Definitions::default();

        lang::process_definition("def foo Num () { \\ 3 }", Default::default(), None, defs)
            .unwrap();
        lang::process_definition(
            "def foo Str () { \\ 'foo' }",
            Default::default(),
            None,
            defs,
        )
        .unwrap();

        compile_w_defs("\\ 3 | foo", defs).unwrap();
        compile_w_defs("\\ 'foo' | foo", defs).unwrap();

        // test that arity is robust
        lang::process_definition(
            "def foo Str (x:Num) { \\ 'foo' }",
            Default::default(),
            None,
            defs,
        )
        .unwrap();

        compile_w_defs("\\ 3 | foo", defs).unwrap();
        compile_w_defs("\\ 'foo' | foo 2", defs).unwrap();

        let x = compile_w_defs("\\ 3 | foo 2", defs)
            .unwrap_err()
            .to_string();
        assert_eq!(
            &x,
            r#"Semantics Error: too many arguments supplied
--> shell:10
 | \ 3 | foo 2
 |           ^ this argument is unnecessary
"#
        );
        let x = compile_w_defs("\\ 3 | foo 2 3", defs)
            .unwrap_err()
            .to_string();
        assert_eq!(
            &x,
            r#"Semantics Error: too many arguments supplied
--> shell:10
 | \ 3 | foo 2 3
 |           ^^^ these arguments are unnecessary
"#
        );
        let x = compile_w_defs("\\ 'foo' | foo", defs)
            .unwrap_err()
            .to_string();
        assert_eq!(
            &x,
            r#"Semantics Error: expecting more than 0 arguments
--> shell:10
 | \ 'foo' | foo
 |           ^^^ expecting additional argument(s)
--> help: try using the `--help` flag to view requirements.
          `foo` is defined to accept parameters `(x:Num)`
"#
        );
        let x = compile_w_defs("\\ 'foo' | foo 2 3", defs)
            .unwrap_err()
            .to_string();
        assert_eq!(
            &x,
            r#"Semantics Error: too many arguments supplied
--> shell:16
 | \ 'foo' | foo 2 3
 |                 ^ this argument is unnecessary
"#
        );
    }
}
