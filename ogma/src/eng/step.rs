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
                        f: Arc::new(move |input, cx| evaluator.eval(input, cx)),
                        type_annotation: Default::default(),
                    }
                })
            }
        }?;

        Ok(step)
    }

    pub fn def(params: Vec<(Variable, Argument)>, subexpr: eval::Stack, out_ty: Type) -> Self {
        let f = Arc::new(move |input: Value, mut cx: Context| {
            // resolve each callsite argument and set the variable
            for (var, arg) in &params {
                let v = arg.resolve(|| input.clone(), &cx)?;
                var.set_data(&mut cx.env, v);
            }

            // evalulate the sub-expr
            subexpr.eval(input, cx)
        });

        Self {
            out_ty,
            f,
            type_annotation: String::new(),
        }
    }
}

impl Clone for Step {
    fn clone(&self) -> Self {
        Step {
            out_ty: self.out_ty.clone(),
            f: Arc::clone(&self.f),
            type_annotation: self.type_annotation.clone(),
        }
    }
}
