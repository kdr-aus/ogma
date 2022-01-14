//! Compilation and evaluation engine.

use crate::prelude::*;

mod arg;
mod eval;
mod hir;
mod ty;
mod var;

pub(crate) use self::{
    eval::{DefImplEvaluator, Evaluator},
    hir::{handle_help, Context},
    var::{Environment, Local, Locals, Variable},
};

// ###### ARGUMENT #############################################################
/// Compiled argument.
///
/// TODO: reduce the size of this, possibly by boxing the Hold??
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

    /// A tracked type annotation code representation.
    ///
    /// TODO: This implementation is currently pretty poorly implemented, requiring this to be
    /// tracked at all times. Once type inferencing matures more, this annotation could possibly be
    /// moved into that system.
    type_annotation: String,
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

    /// A tracked type annotation code representation.
    /// This comes directly off the block when transforming into a `Step`.
    ///
    /// TODO: This implementation is currently pretty poorly implemented, requiring this to be
    /// tracked at all times. Once type inferencing matures more, this annotation could possibly be
    /// moved into that system.
    type_annotation: String,
}

type StepR = Result<(Value, Environment)>;

// ###### FUNCTIONS ############################################################

// ###### testing ##############################################################
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn structures_sizing() {
        use std::mem::size_of;

        // TODO review this sizing, maybe it can be reduced by boxing
        assert_eq!(size_of::<Argument>(), 232);
        assert_eq!(size_of::<Hold>(), 136);

        // Evaluator is quite large
        assert_eq!(size_of::<Evaluator>(), 128);
    }
}
