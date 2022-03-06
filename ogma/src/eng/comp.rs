//! Compilation.

use super::*;
use astgraph::{AstGraph, AstNode};
use graphs::*;
use tygraph::TypeGraph;

/// Compile an expression.
///
/// `input_ty` and `locals` are optional. If not specified, `Nil` and an empty input locals are
/// used. If they are specified, then compilation builds atop them.
pub fn compile<I, L>(
    expr: ast::Expression,
    defs: &Definitions,
    input_ty: I,
    locals: L,
) -> Result<FullCompilation>
where
    I: Into<Option<Type>>,
    L: Into<Option<Locals>>,
{
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
        output_infer_opnode: None,
        callsite_params: Default::default(),
    };

    let input_ty = input_ty.into().unwrap_or(Type::Nil);

    compiler.init_tg(input_ty); // initialise TG

    // initialise an empty Locals into the first op node
    // route through Compiler::insert_locals, since it handles locals propagation
    // THIS IS THE RETURN LOCALS AS WELL!
    let vars = locals.into().unwrap_or_default();
    let root = ExprNode(0.into());
    compiler.insert_locals(&vars, root.first_op(compiler.ag()));

    let mut compiler = compiler.compile(root)?;

    let err = "should exist on successful compilation";

    // NOTE: this can be used to investigate compilation/evaluation issues by visualising the
    // compiler state. gated by a compilation flag, it must be turned off for release modes
    compiler.write_debug_report("debug-compiler.md");

    Ok(FullCompilation {
        eval_stack: compiler.compiled_exprs.remove(&0).expect(err), // root expr stack
        vars,
    })
}

pub struct FullCompilation {
    pub eval_stack: eval::Stack,
    pub vars: Locals,
}

// TODO: check sizing, maybe box this??
#[derive(Clone)]
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
    /// A op node which has been flag for output inferrence.
    output_infer_opnode: Option<OpNode>,
    /// A map of **Def** nodes which have had their call site parameters prepared as variables.
    callsite_params: IndexMap<Vec<CallsiteParam>>,
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
    pub fn compile(mut self, break_on: ExprNode) -> Result<Self> {
        let mut err = None;

        let brk_key = &break_on.index();
        while !self.compiled_exprs.contains_key(brk_key) {
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
                Err(e) => err = Some(e),
            }

            eprintln!("Flow compiled op's locals");
            if self.flow_compiled_ops_locals() {
                eprintln!("✅ SUCCESS");
                continue;
            }

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
                    traces: vec![],
                    help_msg: Some("this is an internal bug, please report it at <https://github.com/kdr-aus/ogma/issues>".into())
        }
        ));
        }

        Ok(self)
    }

    /// Returns if the TG was altered when applying the changes.
    pub fn apply_tg_chgs<C>(&mut self, chgs: C) -> bool
    where
        C: Iterator<Item = tygraph::Chg>,
    {
        chgs.map(|c| self.tg.apply_chg(c))
            .fold(false, std::ops::BitOr::bitor)
    }

    /// Inserts a locals _input_ entry into the locals map.
    /// This function is recursive, it walks through child expression arguments and also inserts
    /// the locals entry into the _first_ op node.
    fn insert_locals(&mut self, locals: &Locals, op: OpNode) {
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
            self.insert_locals(locals, op);
        }
    }
}

/// Resolve TG
impl<'d> Compiler<'d> {
    fn resolve_tg(&mut self) -> Result<()> {
        loop {
            match self.tg.flow_types(&mut self.flowed_edges) {
                Ok(true) => (), // keep going!
                Ok(false) => break Ok(()),
                Err(reserr) => break Err(self.ty_resolution_err(reserr)),
            }
        }
    }

    fn ty_resolution_err(&self, reserr: tygraph::ResolutionError) -> Error {
        use crate::common::err::*;
        use tygraph::Conflict;

        let mut err = Error {
            cat: Category::Type,
            desc: "Type resolution failed".into(),
            traces: Vec::new(),
            help_msg: None,
        };

        let tygraph::ResolutionError { from, to, conflict } = reserr;

        let from = self.ag[from].tag();
        let to = self.ag[to].tag();

        match conflict {
            Conflict::UnknownSrc => {
                err.desc.push_str(". Unknown source type");
                err.traces.push(Trace::from_tag(
                    from,
                    "this node's type is unknown".to_string(),
                ));
            }
            Conflict::UnmatchedObligation { src, dst } => {
                err.desc.push_str(". Conflicting obligation type");
                err.traces.push(Trace::from_tag(
                    from,
                    format!("this node has type `{}`", src),
                ));
                err.traces.push(Trace::from_tag(
                    to,
                    format!("but this node is obliged to return `{}`", dst),
                ));
            }
        }

        err
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
            let local = match self
                .locals
                .get(&ArgNode(node).op(&self.ag).index())
                .and_then(|locals| locals.get(var_tag.str()))
            {
                Some(l) => l,
                None => continue,
            };

            let chg = match local {
                Local::Var(v) => tygraph::Chg::KnownOutput(node, v.ty().clone()),
                Local::Param(x) => tygraph::Chg::KnownOutput(node, x.out_ty().clone()),
            };

            chgs.push(chg);
            chgs.push(tygraph::Chg::AnyInput(node));
        }

        self.apply_tg_chgs(chgs.into_iter())
    }
}

/// Inserting available def locals.
impl<'d> Compiler<'d> {
    /// Looks at the `Def` command nodes and builds a `Locals` for the first op if:
    /// 1. The parent op has an available locals to scaffold off, and
    /// 2. _All_ parameters have a known type.
    fn insert_available_def_locals(&mut self) -> Result<bool> {
        struct D {
            def: DefNode,
            parent: OpNode,
            first: OpNode,
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
                })
                // check that the op does not already have a locals map
                .filter(|d| !self.locals.contains_key(&d.first.index()))
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
                } = d;

                skip.insert(def);

                let params = self.ag[def.idx()].def().expect("filtered to def node");

                // TODO should this be an error pathway?
                // since the error pathway is not having enough params (or too many??)
                match locals.inject_params(self, params, def, tg_chgs)? {
                    LocalInjection::Success {
                        locals,
                        callsite_params,
                    } => {
                        chgd = true;
                        self.insert_locals(&locals, first);
                        let _is_empty = self
                            .callsite_params
                            .insert(def.index(), callsite_params)
                            .is_none();
                        debug_assert!(
                            _is_empty,
                            "just replaced a callsite_params entry which should not happen"
                        );
                    }
                    LocalInjection::UnknownReturnTy(argnode) => {
                        // TODO what to do about unknown return arguments!?
                    }
                }
            }
        }

        let tg_chgd = self.apply_tg_chgs(tg_chgs.drain(..));

        Ok(chgd || tg_chgd)
    }
}

/// Linking def's args for known paths.
impl<'d> Compiler<'d> {
    fn link_known_def_path_args(&mut self) -> bool {
        // filter ops which are not compiled
        // filter to ops where the input type is known
        // get the cmd node, if a def, then this is known as the path to take

        let defnodes = self
            .ag
            .node_indices()
            // just OpNodes
            .filter_map(|n| self.ag[n].op().map(|_| OpNode(n)))
            // without compiled steps
            .filter(|n| !self.compiled_ops.contains_key(&n.index()))
            // where input type is known
            .filter_map(|n| self.tg[n.idx()].input.ty().map(|t| (n, t)))
            // map to the def node path
            .filter_map(|(n, ty)| self.ag.get_impl(n, ty))
            // only if a Def
            .filter_map(|n| self.ag[n.idx()].def().map(|_| DefNode(n.idx())))
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
                Ok((step, locals)) => {
                    goto_resolve = true;
                    let out_ty = step.out_ty.clone();

                    // insert the compiled step into the map
                    dbg!(node, locals.is_some());
                    let _is_empty = self.compiled_ops.insert(node.index(), step).is_none();
                    debug_assert!(
                        _is_empty,
                        "just replaced an already compiled step which should not happen"
                    );

                    // insert the returned, mutated, locals into the locals map (if it is some).
                    // need to insert it into the **next** op after this one.
                    if let Some(locals) = locals {
                        if let Some(next) = node.next(&self.ag) {
                            self.insert_locals(&locals, next);
                        }
                    }

                    // since this compilation was successful, the output type is known!
                    // the TG is updated with this information
                    chgs.push(tygraph::Chg::KnownOutput(node.idx(), out_ty));
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
        infer_output: &mut bool,
    ) -> Result<(Step, Option<Locals>)> {
        let cmd_node = self
            .ag
            .get_impl(opnode, &in_ty)
            .ok_or_else(|| Error::op_not_found(self.ag[opnode.idx()].tag()))?;

        match &self.ag[cmd_node.idx()] {
            AstNode::Intrinsic { op, intrinsic } => {
                let mut locals = self.locals.get(&opnode.index()).cloned();

                let block =
                    Block::construct(self, cmd_node, in_ty, locals.as_mut(), chgs, infer_output);

                intrinsic(block).map(|step| (step, locals))
            }
            AstNode::Def(params) => {
                // check if there exists an entry for the sub-expression,
                // if so, wrap that in a Step and call it done!
                let defnode = DefNode(cmd_node.idx());
                let expr = defnode.expr(&self.ag);
                match self.compiled_exprs.get(&expr.index()) {
                    Some(stack) => {
                        // map the callsite params into the **op** node's arguments (for eval)
                        let params =
                            self.map_callsite_params_for_def_step(defnode, &in_ty, chgs)?;
                        let out_ty = self.tg[expr.idx()]
                            .output
                            .ty()
                            .cloned()
                            .expect("shoud be known if a stack exists");
                        let step = Step::def(params, stack.clone(), out_ty);
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
    /// - `CallsiteParam.arg_idx` should index into the def's argument list
    /// - the argument builder expects both input and output types of the argument to be known
    fn map_callsite_params_for_def_step(
        &self,
        def: DefNode,
        in_ty: &Type,
        tg_chgs: &mut Vec<tygraph::Chg>,
    ) -> Result<Vec<(Variable, Argument)>> {
        let Compiler {
            defs,
            ag,
            tg,
            flowed_edges,
            compiled_ops,
            compiled_exprs,
            locals,
            output_infer_opnode,
            callsite_params,
        } = self;

        let args = ag.get_args(def);
        let mut locals = locals
            .get(&def.parent(ag).index())
            .expect("input locals should exist")
            .clone();
        let locals = &mut Some(&mut locals);

        callsite_params
            .get(&def.index())
            .expect("if the sub-expression exists, there should be an associated callsite params")
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
                        tg_chgs,
                        Some(in_ty.clone()),
                        locals,
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
        let ops = self
            .ag
            .node_indices()
            // get just ops
            .filter_map(|n| self.ag[n].op().map(|_| OpNode(n)))
            .collect::<Vec<_>>();

        let mut chgd = false;

        for op in ops {
            let opidx = &op.index();

            let compiled = self.compiled_ops.contains_key(opidx);

            // 1. op is compiled, but next op has no locals
            if compiled {
                if let Some(next) = op.next(&self.ag) {
                    match (
                        self.locals.get(opidx).cloned(),
                        self.locals.contains_key(&next.index()),
                    ) {
                        (Some(locals), false) => {
                            chgd = true;
                            self.insert_locals(&locals, next);
                        }
                        _ => (),
                    }
                }
            }
        }

        chgd
    }
}

/// Infer inputs.
impl<'d> Compiler<'d> {
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
}

/// Infer outputs.
impl<'d> Compiler<'d> {
    fn infer_outputs(&mut self) -> bool {
        if let Some(opnode) = self.output_infer_opnode.take() {
            let defs = self.defs;
            // replace a dummy compiler value
            let this = std::mem::replace(
                self,
                Compiler {
                    ag: Default::default(),
                    tg: Default::default(),
                    compiled_ops: Default::default(),
                    compiled_exprs: Default::default(),
                    output_infer_opnode: Default::default(),
                    flowed_edges: Default::default(),
                    locals: Default::default(),
                    callsite_params: Default::default(),
                    defs,
                },
            );
            // infer output
            let x = ty::infer::output(opnode, this);
            // store if we were successful
            let success = x.is_ok();
            // bring back the compiler to self, throw out the dummy
            *self = x.unwrap_or_else(|c| c);
            // return the inferring result
            success
        } else {
            false
        }
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
        self.debug_index_map(&self.locals, &mut report).unwrap();

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
        locals: Option<&'a mut Locals>,
        chgs: &'a mut Vec<tygraph::Chg>,
        output_infer: &'a mut bool,
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
                    dbg!(ag[op.idx()].tag());
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

enum LocalInjection {
    Success {
        locals: Locals,
        callsite_params: Vec<CallsiteParam>,
    },
    UnknownReturnTy(ArgNode),
}

#[derive(Debug, Clone)]
struct CallsiteParam {
    param: astgraph::Parameter,
    var: Variable,
    arg_idx: u8,
}

impl Locals {
    fn inject_params(
        mut self,
        compiler: &Compiler,
        params: &[astgraph::Parameter],
        defnode: DefNode,
        tygraph_chgs: &mut Vec<tygraph::Chg>,
    ) -> Result<LocalInjection> {
        let _sink = &mut false;

        let mut args = compiler.ag().get_args(defnode);
        args.reverse();

        let mut callsite_vars = Vec::with_capacity(params.len());
        //         let mut expr_vars = Vec::with_capacity(params.len());

        let mut arg_count = 0;
        let blk_tag = compiler.ag()[defnode.parent(compiler.ag()).idx()].tag();
        let locals = &mut Some(&mut self);

        let Compiler {
            ag,
            tg,
            compiled_exprs,
            ..
        } = compiler;

        for (idx, param) in params.into_iter().enumerate() {
            // only point of failure
            let argnode = arg::pop(&mut args, arg_count, blk_tag)?;
            arg_count += 1;

            // TODO need to handle Expr parameter types, will need to alter the structure of
            // astgraph::Parameter

            // the parameter is to be resolved at the call site
            let arg =
                arg::ArgBuilder::new(argnode, ag, tg, tygraph_chgs, None, locals, compiled_exprs);

            let arg = match param.ty() {
                Some(ty) => arg.returns(ty.clone())?,
                None => arg,
            };

            // we do not need to .concrete the arg, since we don't really want to get the Argument
            // that it returns. Instead, all we really want to know about this argument is it's
            // output type.
            match arg.return_ty() {
                Some(ty) => {
                    callsite_vars.push((idx, param, ty.clone()));
                }
                None => return Ok(LocalInjection::UnknownReturnTy(argnode)),
            }
        }

        let callsite_params = callsite_vars
            .into_iter()
            .map(|(arg_idx, param, ty)| {
                let tag = param.name.clone();
                let name = Str::new(tag.str());
                CallsiteParam {
                    param: param.clone(),
                    // TODO validate that this is the tag that should be sent through
                    var: self.add_new_var(name, ty, tag),
                    arg_idx: arg_idx as u8,
                }
            })
            .collect();

        Ok(LocalInjection::Success {
            locals: self,
            callsite_params,
        })
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

        super::compile(expr, defs, None, None)
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
}
