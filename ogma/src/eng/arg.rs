use super::*;
use std::convert::TryInto;

impl Argument {
    /// The arguments input type.
    pub fn in_ty(&self) -> &Type {
        &self.in_ty
    }

    /// The arguments output type.
    pub fn out_ty(&self) -> &Type {
        &self.out_ty
    }

    /// If the argument was a literal _(as in something that is known before runtime, not a variable
    /// or expression)_, extract the [`Value`] and _cast_ into `&T`.
    ///
    /// This is useful for cases where a value needs to be known at the HIR phase rather than
    /// resolving at the eval phase.
    pub fn extract_literal<'a, T>(&'a self) -> Result<&'a T>
    where
        T: AsType,
        &'a Value: TryInto<&'a T>,
    {
        let tag = &self.tag;

        match &self.hold {
            Hold::Lit(x) => {
                let exp_ty = T::as_type();
                if exp_ty == self.out_ty {
                    Ok(x.try_into()
                        .map_err(|_| ())
                        .expect("tested types, should cnv fine"))
                } else {
                    Err(Error::unexp_arg_ty(&exp_ty, &self.out_ty, tag))
                }
            }
            Hold::Var(_) => Err(Error::unexp_arg_variant(tag, "variable")),
            Hold::Expr(_) => Err(Error::unexp_arg_variant(tag, "expression")),
        }
    }

    /// Asserts that the Argument returns the type `ty` once resolved.
    pub fn returns(self, ty: &Type) -> Result<Self> {
        if &self.out_ty == ty {
            Ok(self)
        } else {
            let mut err = Error::unexp_arg_ty(ty, &self.out_ty, &self.tag);
            if let Hold::Expr(e) = self.hold {
                err = err.add_trace(e.tag());
            };
            Err(err)
        }
    }

    /// Resolve the argument to its [`Value`]. This means passing a literal through, fetching a
    /// variable (and cloning), or evaluating an expression.
    ///
    /// **The input is only cloned if the argument is an expression**.
    pub fn resolve<F>(&self, input: F, cx: &Context) -> Result<Value>
    where
        F: FnOnce() -> Value,
    {
        match &self.hold {
            Hold::Lit(x) => Ok(x.clone()),
            Hold::Var(v) => Ok(v.fetch(&cx.env).clone()),
            Hold::Expr(e) => resolve_expr(e, &self.in_ty, input(), cx.clone()).map(|x| x.0),
        }
    }

    /// Transform this argument into a `resolve` function.
    ///
    /// This is preferred when argument is being used **as a repeat argument**. The reason is that
    /// the variable fetching is done once, hence making it slightly more performant. The caveat of
    /// this is that the expression no longer gets lazily invoked for the input, so probably should
    /// only be used when an owned `Value` already exists.
    ///
    /// If the resolving is happening once, `resolve` is preferred.
    pub fn resolver_sync<'a>(
        &'a self,
        cx: &'a Context<'a>,
    ) -> impl Fn(Value) -> Result<Value> + Sync + 'a {
        use std::borrow::Cow;
        enum R<'r> {
            V(Cow<'r, Value>),
            E(&'r Evaluator),
        }
        let r = match &self.hold {
            Hold::Lit(x) => R::V(Cow::Borrowed(x)),
            Hold::Var(x) => R::V(Cow::Owned(x.fetch(&cx.env).clone())),
            Hold::Expr(e) => R::E(e),
        };

        let inty = self.in_ty.clone();

        move |input| match &r {
            R::V(v) => Ok(v.as_ref().clone()),
            R::E(e) => resolve_expr(e, &inty, input, cx.clone()).map(|x| x.0),
        }
    }
}

fn resolve_expr(expr: &Evaluator, inty: &Type, input: Value, cx: Context) -> StepR {
    if cfg!(debug_assertions) {
        // runtime check the input type matches this type.
        // only do check in debug mode.
        let ity = input.ty();
        assert!(
            inty == &ity,
            "arguments expected input type does not match supplied input type.
expected input type: {}
supplied input type: {}",
            inty,
            ity
        );
    }
    expr.eval(input, cx)
}
