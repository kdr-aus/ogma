use super::*;

impl Step {
    pub fn compile(impls: &Implementations, mut block: Block) -> Result<Step> {
        let im = impls.get_impl(block.op_tag(), &block.in_ty)?;
        let step = match im {
            Implementation::Intrinsic { f, .. } => f(block),
            Implementation::Definition(def) => {
                // TODO This seems unnecessary, wrapping an evaluator in a step???
                DefImplEvaluator::build(&mut block, def).map(|evaluator| {
                    // the DefImplEvaluator::build will process the block
                    // this has the effect of updating the blocks type annotation
                    // NOTE that the evaluator's type annotation is the type annotation of the
                    // inner definition (which might be useful!)

                    Step {
                        out_ty: evaluator.ty().clone(),
                        f: Box::new(move |input, cx| evaluator.eval(input, cx)),
                        type_annotation: Default::default(),
                    }
                })
            }
        }?;

        Ok(step)
    }
}
