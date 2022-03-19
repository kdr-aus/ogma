//! Compilation and evaluation engine.

use crate::prelude::*;

mod annotate;
mod arg;
mod blk;
mod comp;
mod eval;
mod graphs;
mod hir;
mod step;
mod var;

type IndexSet = crate::HashSet<usize>;
type IndexMap<V> = crate::HashMap<usize, V>;
type LocalsMap = IndexMap<Locals>;

pub(crate) use self::{
    annotate::types as annotate_types,
    eval::{CodeInjector, DefImplEvaluator, Eval, Evaluator},
    hir::Context,
    var::{Environment, Local, Locals},
};

pub use self::comp::{compile, FullCompilation};

type Chgs<'a> = &'a mut Vec<graphs::Chg>;

// ###### ARGUMENT #############################################################
/// Compiled argument.
///
/// TODO: reduce the size of this, possibly by boxing the Hold??
/// TODO: Move into `arg` module.
#[derive(Debug, Clone)]
pub struct Argument {
    /// The argument tag.
    pub tag: Tag,
    in_ty: Type,
    out_ty: Type,
    hold: Hold,
}

// TODO move this into `arg` module??
#[derive(Debug, Clone)]
enum Hold {
    Lit(Value),
    // TODO -- this needs some thought,
    Var(Variable),
    // TODO -- this needs some thought,
    Expr(eval::Stack),
}

// ###### BLOCK ################################################################
/// A compilation unit for a single [`ast::Block`].
///
/// The block is foundational to the compilation engine.
/// It acts as the interface between the engine's internal mechanisms and the implementers,
/// exposing an API which is ergonomic, while handling all the typing and checking behind the
/// scenes.
pub struct Block<'a> {
    /// The OP node index from the compiler graphs.
    node: graphs::OpNode,

    // NOTE that the input type is not referenced via the TG.
    // This is done so that this block can be tested against differing input types for InferInput
    /// The block's input type.
    pub in_ty: Type,

    /// The block's flags.
    ///
    /// Must be empty upon finalisation, unused flags return error.
    ///
    /// > Stored in reverse order as a stack.
    flags: Vec<Tag>,
    /// The blocks arguments, stored as indices into the ast graph.
    ///
    /// Must be empty upon finalisation, unused args return error.
    ///
    /// > Stored in reverse order as a stack.
    args: Vec<graphs::ArgNode>,
    /// Counter of the arguments used.
    ///
    /// Only 255 arguments are supported.
    args_count: u8,

    /// The compiler's ast graph.
    ag: &'a graphs::astgraph::AstGraph,
    /// The compiler's type graph.
    tg: &'a graphs::tygraph::TypeGraph, // notice the immutability!
    /// The compiler's local's graph.
    lg: &'a graphs::locals_graph::LocalsGraph,
    /// The compiler's compiled expressions.
    compiled_exprs: &'a IndexMap<eval::Stack>,

    /// A list of changes to be made to the type graph.
    ///
    /// This is stored as a mutable reference since the block is usually passed by value to
    /// implementors.
    /// Any items here are actioned by the compiler to update the type graph, providing more
    /// information to conduct the type inferencing.
    /// This allows for block compilation to fail but the updates still be applied.
    chgs: &'a mut Vec<graphs::Chg>,

    /// Flag that this block's output should be inferred if getting to output inferencing phase.
    infer_output: &'a mut bool,

    // TODO is this removable??
    /// The definitions carried through.
    pub defs: &'a Definitions,

    /// Carry information about an asserted output type.
    /// Check this against upon finalisation to ensure it matches.
    /// Only available and checked in debug builds.
    #[cfg(debug_assertions)]
    output_ty: Option<Type>,
}

impl<'a> Block<'a> {
    /// Carry out checks of the block's state.
    fn finalise(&self, _out_ty: &Type) -> Result<()> {
        if !self.flags.is_empty() {
            Err(Error::unused_flags(self.flags.iter()))
        } else if !self.args.is_empty() {
            Err(Error::unused_args(
                self.args.iter().map(|a| self.ag[a.idx()].tag()),
            ))
        } else {
            #[cfg(debug_assertions)]
            match &self.output_ty {
                Some(t) => debug_assert_eq!(
                    t, _out_ty,
                    "asserted output type should match finalisation type"
                ),
                None => (), // no assertion, no failure
            };

            Ok(())
        }
    }
}

// ###### STEP #################################################################

pub trait Func<O>: Fn(Value, Context) -> O + Send + Sync + 'static {}
impl<T, O> Func<O> for T where T: Fn(Value, Context) -> O + Send + Sync + 'static {}

/// A compiled block, ready for evaluation.
pub struct Step {
    out_ty: Type,
    f: Arc<dyn Func<StepR>>,

    /// A tracked type annotation code representation.
    /// This comes directly off the block when transforming into a `Step`.
    ///
    /// TODO: This implementation is currently pretty poorly implemented, requiring this to be
    /// tracked at all times. Once type inferencing matures more, this annotation could possibly be
    /// moved into that system.
    type_annotation: String,
}

type StepR = Result<(Value, Environment)>;

// ###### VARIABLE #############################################################
#[derive(Debug, Clone)]
pub struct Variable {
    pub tag: Tag,
    ty: Type,
    env_idx: usize,
}

// ###### testing ##############################################################
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn structures_sizing() {
        use std::mem::size_of;

        // TODO review this sizing, maybe it can be reduced by boxing
        assert_eq!(size_of::<Argument>(), 192);
        assert_eq!(size_of::<Hold>(), 96);

        // Evaluator is quite large
        assert_eq!(size_of::<Evaluator>(), 128);
        assert_eq!(size_of::<Block>(), 144);
        assert_eq!(size_of::<arg::ArgBuilder>(), 96);
        assert_eq!(size_of::<Tag>(), 64);
    }
}
