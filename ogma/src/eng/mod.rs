//! Compilation and evaluation engine.

use crate::prelude::*;

mod annotate;
mod arg;
mod blk;
mod comp;
mod eval;
mod graphs;
mod step;
mod var;

type IndexSet = crate::HashSet<usize>;
type IndexMap<V> = crate::HashMap<usize, V>;

pub(crate) use self::{
    annotate::types as annotate_types,
    arg::Argument,
    eval::{CodeInjector, Context, Eval},
    var::{Environment, Local, Variable},
};

pub use self::comp::{compile, FullCompilation};

type Chgs<'a> = &'a mut Vec<graphs::Chg>;

// ###### COMPILER #############################################################
// TODO: check sizing, maybe box this??
#[derive(Clone)]
struct Compiler<'d> {
    defs: &'d Definitions,
    ag: graphs::astgraph::AstGraph,
    tg: graphs::tygraph::TypeGraph,
    lg: graphs::locals_graph::LocalsGraph,
    /// The edges in the `tg` that have been resolved and flowed.
    flowed_edges: IndexSet,
    /// A map of **Op** nodes which have succesfully compiled into a `Step`.
    compiled_ops: IndexMap<Step>,
    /// A map of **Expr** nodes which have succesfully compiled into an evaluation stack.
    compiled_exprs: IndexMap<eval::Stack>,
    /// A op node which has been flag for output inferrence.
    output_infer_opnode: Option<graphs::OpNode>,
    /// A map of **Def** nodes which have had their call site parameters prepared as variables.
    callsite_params: IndexMap<Vec<comp::CallsiteParam>>,
    /// Depth limit of inference to loop down to.
    inferrence_depth: u32,
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

    /// A _read-only_ compiler reference.
    compiler: &'a Compiler<'a>,

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

    /// Carry information about an asserted output type.
    /// Check this against upon finalisation to ensure it matches.
    /// Only available and checked in debug builds.
    #[cfg(debug_assertions)]
    output_ty: Option<Type>,
}

// ###### STEP #################################################################

/// Common function signature for evaluation, taking a `Value` and a `Context` and returning `O`.
pub trait Func<O>: Fn(Value, Context) -> O + Send + Sync + 'static {}
impl<T, O> Func<O> for T where T: Fn(Value, Context) -> O + Send + Sync + 'static {}

/// A compiled block, ready for evaluation.
pub struct Step {
    out_ty: Type,
    f: Arc<dyn Func<StepR>>,
}

type StepR = Result<(Value, Environment)>;

// ###### testing ##############################################################
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn structures_sizing() {
        use std::mem::size_of;

        // NOTE
        // Although block sizing is large, it would not really be a hot spot, and the cost of
        // refactoring somewhat outweighs any benefit, without doing any proper profiling to
        // support it.
        assert_eq!(size_of::<Block>(), 96 + size_of::<Option<Type>>()); // `output_ty` is only on debug builds
        assert_eq!(size_of::<Step>(), 32);
    }
}
