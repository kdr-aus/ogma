//! `Def` parameter handling.
//!
//! Parameters come in two flavours;
//! 1. Evaluated at the _callsite_, and
//! 2. Expressions are _lazy_ and resolved when _used_.
//!
//! The handling of these parameters is dichotomous. The **callsite** params must have a variable
//! slot assigned which is _set_ before evaluation of the sub-expression.
//! The **lazy** param should be treated like a regular argument, _except that it points to an
//! argument node **outside** of the regular one_.
//!
//! ## Lazy Params
//! The requirement for lazy parameters to shadow the referencer argument is so that local
//! injection can be valid. For example, passing a filter predicate through a def boundary needs to
//! support the `$row` variable being available for the predicate.
//! With the locals graph, this is possible to inject the variable locally, and even environment
//! capturing seems to fall out this graph implementation (testing to be done...).
use super::*;
use astgraph::Parameter;

impl<'d> Compiler<'d> {
    pub fn insert_available_def_locals(&mut self) -> Result<bool> {
        // only map defs where we know it will take that path.
        // the reason is two fold;
        // 1. errors can be hard returned which assists in debugging,
        // 2. it avoids unnecessary variable slots which would not be used
        let defs = self
            .ag
            .op_nodes()
            // where input type is known
            .filter_map(|n| self.tg[n.idx()].input.ty().map(|t| (n, t)))
            // map to the def node path
            .filter_map(|(n, ty)| self.ag.get_impl(n, ty))
            // only if a Def
            .filter_map(|n| n.def(&self.ag))
            // defs without constructed callsite params
            .filter(|d| !self.callsite_params.contains_key(&d.index()))
            .collect::<Vec<_>>();

        let chgs = &mut Vec::new();
        let mut chgd = false;

        for def in defs {
            let params = def.params(&self.ag);

            match map_def_params_into_variables(self, def, chgs)? {
                LocalInjection::LgChange => (), // continue,
                LocalInjection::Success { callsite_params } => {
                    chgd = true;
                    let _is_empty = self
                        .callsite_params
                        .insert(def.index(), callsite_params)
                        .is_none();
                    debug_assert!(
                        _is_empty,
                        "just replaced a callsite_params entry which should not happen"
                    );

                    // seal off the def's expr node
                    // no more changes should occur since we have had succcess building.
                    self.lg.seal_node(def.expr(&self.ag).idx(), &self.ag);
                }
                LocalInjection::UnknownReturnTy(argnode) => {
                    // TODO what to do about unknown return arguments!?
                }
            }
        }

        let chgd2 = self.apply_graph_chgs(chgs.drain(..));
        Ok(chgd || chgd2)
    }
}

pub enum LocalInjection {
    Success { callsite_params: Vec<CallsiteParam> },
    LgChange,
    UnknownReturnTy(ArgNode),
}

#[derive(Debug, Clone)]
pub struct CallsiteParam {
    pub param: astgraph::Parameter,
    pub var: Variable,
    pub arg_idx: u8,
}

pub fn map_def_params_into_variables(
    compiler: &Compiler,
    defnode: DefNode,
    chgs: Chgs,
) -> Result<LocalInjection> {
    let Compiler {
        ag,
        tg,
        lg,
        compiled_exprs,
        defs,
        ..
    } = compiler;

    // flags are not supported:
    let flags = ag.get_flags(defnode);
    if !flags.is_empty() {
        return Err(Error::unused_flags(flags.iter()));
    }

    let mut args = ag.get_args(defnode);
    args.reverse();

    let params = defnode.params(ag);

    let mut callsite_params = Vec::with_capacity(params.len());

    let blk_tag = defnode.parent(ag).blk_tag(ag);

    let mut lg_chg = false;

    for (idx, param) in params.into_iter().enumerate() {
        let idx = idx as u8;
        // point of failure
        let argnode = arg::pop(&mut args, idx, blk_tag).map_err(|_| {
            let op = defnode.parent(ag);
            let optag = op.op_tag(ag);
            let impl_ = tg[op.idx()]
                .input
                .ty()
                .and_then(|inty| defs.impls().get_impl(optag, inty).ok())
                .or_else(|| {
                    defs.impls()
                        .iter()
                        .find_map(|x| (x.0 == optag.str()).then(|| x.2))
                })
                .and_then(|i| match i {
                    Implementation::Definition(x) => Some(x.as_ref()),
                    _ => None,
                });

            Error::insufficient_args(blk_tag, idx, impl_)
        })?;

        if param.ty.is_expr() {
            // the parameter is lazy
            if let Err(chg) = map_lazy_param(compiler, argnode, defnode, param) {
                chgs.push(chg.into());
                lg_chg = true;
            }
        } else {
            // the parameter is to be resolved at the call site
            match map_callsite_param(compiler, argnode, defnode, idx, param, chgs)? {
                Ok(Some(cp)) => callsite_params.push(cp),
                Ok(None) => lg_chg = true,
                Err(li) => return Ok(li),
            }
        }
    }

    finalise_args(&args, ag)?;

    if lg_chg {
        return Ok(LocalInjection::LgChange);
    }

    Ok(LocalInjection::Success { callsite_params })
}

/// A lazy parameter does not need to do much apart from ensure there is an entry in the locals
/// graph.
fn map_lazy_param(
    compiler: &Compiler,
    argnode: ArgNode,
    defnode: DefNode,
    param: &Parameter,
) -> std::result::Result<(), locals_graph::Chg> {
    let Compiler { ag, lg, .. } = compiler;

    // the param is defined (scoped) at the expression still
    let expr = defnode.expr(ag);
    lg.new_lazy(
        expr.idx(),
        Str::new(param.name.str()),
        argnode,
        param.name.clone(),
    )
}

fn map_callsite_param(
    compiler: &Compiler,
    argnode: ArgNode,
    defnode: DefNode,
    arg_idx: u8,
    param: &Parameter,
    chgs: Chgs,
) -> Result<std::result::Result<Option<CallsiteParam>, LocalInjection>> {
    let Compiler {
        ag,
        tg,
        lg,
        compiled_exprs,
        ..
    } = compiler;

    let arg = arg::ArgBuilder::new(argnode, ag, tg, lg, chgs, None, compiled_exprs);

    let arg = match param.ty() {
        // point of failure
        Some(ty) => arg.returns(ty.clone())?,
        None => arg,
    };

    // point of failure - we need to test if variable exists.
    // This is only necessary if the argument is a variable variant.
    // The `assert_var_exists` call will check if the locals are sealed, along with
    // checks if the argument is a variable.
    if let Some(false) = arg.assert_var_exists()? {
        return Ok(Err(LocalInjection::LgChange));
    }

    // we do not need to .concrete the arg, since we don't really want to get the Argument
    // that it returns. Instead, all we really want to know about this argument is it's
    // output type.
    let ty = match arg.return_ty() {
        Some(ty) => ty,
        None => {
            return Ok(Err(LocalInjection::UnknownReturnTy(argnode)));
        }
    };

    // this callsite param would create a new variable available at the expression node of
    // the def
    let expr = defnode.expr(ag);
    Ok(Ok(lg
        .new_var(
            expr.idx(),
            Str::new(param.name.str()),
            ty.clone(),
            param.name.clone(),
        )
        .map(|var| CallsiteParam {
            param: param.clone(),
            var,
            arg_idx,
        })
        .map_err(|chg| chgs.push(chg.into()))
        .ok()))
}

fn finalise_args(mut args: &[ArgNode], ag: &AstGraph) -> Result<()> {
    if !args.is_empty() {
        Err(Error::unused_args(args.iter().map(|a| ag[a.idx()].tag())))
    } else {
        Ok(())
    }
}