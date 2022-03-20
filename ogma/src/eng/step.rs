use super::*;
use std::fmt;

impl Step {
    /// Build a step for a definition.
    ///
    /// This wraps the `subexpr`, _first resolving the `params` and setting the variable data_.
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
        }
    }

    /// Evaluate this step, invoking the stored closure with the given value and context.
    pub fn invoke(&self, input: Value, cx: Context) -> StepR {
        let r = (self.f)(input, cx);

        if cfg!(debug_assertions) {
            // we runtime check the step's output type with the eval type in debug mode.
            // this should help isolate pervasive typing bugs but won't impact release performance
            if let Ok((r, _)) = &r {
                assert!(
                    r.ty() == self.out_ty,
                    "the Step's specified output type does not match the evaluated type, one of the types is incorrect!
OUTPUT TYPE: {}
EVAL VALUE: {:?}", 
                    self.out_ty,
                    r,
                );
            }
        }

        r
    }
}

impl Clone for Step {
    fn clone(&self) -> Self {
        Step {
            out_ty: self.out_ty.clone(),
            f: Arc::clone(&self.f),
        }
    }
}

impl fmt::Debug for Step {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Step")
            .field("out_ty", &self.out_ty)
            .finish()
    }
}
