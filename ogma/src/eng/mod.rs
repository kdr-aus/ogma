//! Compilation and evaluation engine.

use crate::prelude::*;
use lang::var::{Environment, Locals};

mod arg;
mod eval;
mod hir;
mod ty;

pub(crate) use self::{
    eval::{DefImplEvaluator, Evaluator},
    hir::{handle_help, Context},
};

// ###### ARGUMENT #############################################################
/// Compiled argument.
pub struct Argument {
    /// The argument tag.
    pub tag: Tag,
    in_ty: Type,
    out_ty: Type,
    hold: Hold,
}

enum Hold {
    Lit(Value),
    Var(Variable),
    Expr(Evaluator),
}

// ###### BLOCK ################################################################
/// A compilation unit for a single [`ast::Block`].
///
/// The block is foundational to the compilation engine.
pub struct Block<'d, 'v> {
    in_ty: Type,
    /// The entire block tag.
    pub blk_tag: Tag,
    /// The operation (command) tag.
    pub op_tag: Tag,
    /// Definitions,
    pub defs: &'d Definitions,
    /// Variables tracking.
    vars: &'v mut Locals,
    /// Must be empty upon finalisation, unused flags return error.
    ///
    /// > Stored in reverse order as a stack.
    flags: Vec<Tag>,
    /// Does not include flags.
    /// Must be empty upon finalisation, unused args return error.
    ///
    /// > Stored in reverse order as a stack.
    args: Vec<ast::Argument>,
    /// Counter of the arguments used.
    args_count: usize,
}

impl<'d, 'v> Block<'d, 'v> {
    fn next_arg_raw(&mut self) -> Result<ast::Argument> {
        let arg = self
            .args
            .pop()
            .ok_or_else(|| Error::insufficient_args(&self.blk_tag, self.args_count))?;
        self.args_count += 1;
        Ok(arg)
    }

    fn arg_recursive(&self, arg: ast::Argument, in_ty: Type, locals: &Locals) -> Result<Argument> {
        use ast::Argument as A;
        use eval::make_input_pound_expr;

        let (hold, tag, out_ty) = match arg {
            A::Ident(ident) => (Hold::Lit(Str::new(ident.str()).into()), ident, Type::Str),
            A::Num(n, tag) => (Hold::Lit(n.into()), tag, Type::Num),
            A::Pound('t', tag) => (Hold::Lit(true.into()), tag, Type::Bool),
            A::Pound('f', tag) => (Hold::Lit(false.into()), tag, Type::Bool),
            A::Pound('n', tag) => (Hold::Lit(Value::Nil), tag, Type::Nil),
            A::Pound('i', tag) => (
                Hold::Expr(make_input_pound_expr(in_ty.clone(), tag.clone())),
                tag,
                in_ty.clone(),
            ),
            A::Pound(ch, tag) => return Err(Error::unknown_spec_literal(ch, &tag)),
            A::Var(var) => {
                match locals
                    .get(var.str())
                    .ok_or_else(|| Error::var_not_found(&var))?
                {
                    Local::Param(arg, locals) => {
                        // update result with the outside var (similar to Local::Var)
                        return self
                            .arg_recursive(arg.clone(), in_ty, locals)
                            .map_err(|e| e.add_trace(&var))
                            .map(|mut x| (x.tag = var, x).1);
                    }
                    Local::Var(v) => {
                        let mut v = v.clone();
                        // update the location of this var to give correct error reporting
                        v.tag = var.clone();
                        let ty = v.ty().clone();
                        (Hold::Var(v), var, ty)
                    }
                }
            }
            A::Expr(expr) => {
                let tag = expr.tag.clone();
                let eval = Evaluator::construct(in_ty.clone(), expr, self.defs, locals.clone())
                    .map_err(|e| e.add_trace(&self.blk_tag))?;
                let out_ty = eval.ty().clone();
                (Hold::Expr(eval), tag, out_ty)
            }
        };

        Ok(Argument {
            tag,
            in_ty,
            out_ty,
            hold,
        })
    }

    fn finalise(&self) -> Result<()> {
        if let Some(flag) = self.flags.last() {
            Err(Error::unused_flag(flag))
        } else if let Some(arg) = self.args.get(0) {
            Err(Error::unused_arg(arg))
        } else {
            Ok(())
        }
    }
}

// ###### STEP #################################################################
/// A compiled block, ready for evaluation.
pub struct Step {
    out_ty: Type,
    f: Box<dyn Fn(Value, Context) -> StepR + Sync>,
}

type StepR = Result<(Value, Environment)>;
