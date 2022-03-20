use super::*;

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
}

impl Clone for Step {
    fn clone(&self) -> Self {
        Step {
            out_ty: self.out_ty.clone(),
            f: Arc::clone(&self.f),
        }
    }
}
