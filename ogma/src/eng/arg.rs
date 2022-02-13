use super::*;
use graphs::{
    tygraph::{Chg, Knowledge},
    *,
};
use std::convert::TryInto;

enum Kn {
    Unknown,
    Any,
    Ty(Type),
}

impl From<&Knowledge> for Kn {
    fn from(kn: &Knowledge) -> Self {
        match kn {
            Knowledge::Unknown => Kn::Unknown,
            Knowledge::Any => Kn::Any,
            Knowledge::Known(t) | Knowledge::Obliged(t) | Knowledge::Inferred(t) => {
                Kn::Ty(t.clone())
            }
        }
    }
}

pub struct ArgBuilder<'a, 'b> {
    blk: &'a mut Block<'b>,
    node: ArgNode,
    in_ty: Kn,
    out_ty: Kn,
}

impl<'a, 'b> ArgBuilder<'a, 'b> {
    /// The arguments tag.
    fn tag(&self) -> &Tag {
        self.blk.ag[self.node.idx()].tag()
    }

    /// Assert that this argument will be supplied an input of type `ty`.
    ///
    /// > Since the **blocks's** input type is used often, and trying to pass this through is
    /// > difficult with mutable aliasing, the type argument is an `Option`, where the `None`
    /// > variant represents _using the block's input type_.
    pub fn supplied<T: Into<Option<Type>>>(mut self, ty: T) -> Result<Self> {
        let ty = ty.into().unwrap_or_else(|| self.blk.in_ty.clone());

        if matches!(self.in_ty, Kn::Any) {
            self.in_ty = Kn::Ty(ty.clone());
        }

        match &self.in_ty {
            Kn::Ty(tg) if tg == &ty => {
                // The TG input type matches what is going to be supplied,
                // nothing needs to be done!
                Ok(self)
            }
            Kn::Ty(tg) => {
                // The TG input type DOES NOT match what is going to be supplied,
                // error out
                Err(Error::unexp_arg_input_ty(&ty, tg, self.tag()))
            }
            Kn::Unknown => {
                // There is currently no knowledge about the input type
                // add to the TG that this node will be supplied a type `ty`
                self.blk.tg_chgs.push(Chg::KnownInput(self.node.idx(), ty));
                Err(Error::unknown_arg_input_type(self.tag()))
            }
            Kn::Any => unreachable!("any is reset to Kn::Ty"),
        }
    }

    /// Assert that this argument returns a value of type `ty`.
    pub fn returns(self, ty: Type) -> Result<Self> {
        debug_assert!(
            !matches!(self.out_ty, Kn::Any),
            "logic error if output is Any type"
        );

        match &self.out_ty {
            Kn::Ty(tg) if tg == &ty => {
                // The TG output type matches what is going to be returned.
                // nothing needs to be done!
                Ok(self)
            }
            Kn::Ty(tg) => {
                // The TG output type DOES NOT match what is going to be supplied,
                // error out
                Err(Error::unexp_arg_output_ty(&ty, tg, self.tag()))
            }
            Kn::Unknown => {
                // There is currently no knowledge about the output type
                // add to the TG that this node is obliged to return the output type
                self.blk
                    .tg_chgs
                    .push(Chg::ObligeOutput(self.node.idx(), ty));
                Err(Error::unknown_arg_output_type(self.tag()))
            }
            Kn::Any => unreachable!("logic error if output is Any type"),
        }
    }

    /// Asserts that the arguments input and output types are known, and if so, returns a concrete
    /// [`Argument`] with the ability to evaluate.
    pub fn concrete(self) -> Result<Argument> {
        use Kn::*;

        let tag = self.tag().clone();

        let Self {
            blk,
            node,
            in_ty,
            out_ty,
        } = self;

        match (in_ty, out_ty) {
            (Unknown | Any, _) => Err(Error::unknown_arg_input_type(&tag)),
            (_, Unknown | Any) => Err(Error::unknown_arg_output_type(&tag)),
            (Ty(in_ty), Ty(out_ty)) => {
                let hold = Self::map_astnode_into_hold(blk, node)?;

                Ok(Argument {
                    tag,
                    in_ty,
                    out_ty,
                    hold,
                })
            }
        }
    }

    fn map_astnode_into_hold(blk: &Block, node: ArgNode) -> Result<Hold> {
        use astgraph::AstNode::*;

        match &blk.ag[node.idx()] {
            Op { op: _, blk: _ } => unreachable!("an argument cannot be an Op variant"),
            Flag(_) => unreachable!("an argument cannot be a Flag variant"),
            Intrinsic { .. } => unreachable!("an argument cannot be a Intrinsic variant"),
            Def { .. } => unreachable!("an argument cannot be a Def variant"),
            Ident(s) => Ok(Hold::Lit(Str::new(s.str()).into())),
            Num { val, tag: _ } => Ok(Hold::Lit((*val).into())),
            Pound { ch: 'n', tag: _ } => Ok(Hold::Lit(Value::Nil)),
            Pound { ch: 't', tag: _ } => Ok(Hold::Lit(true.into())),
            Pound { ch: 'f', tag: _ } => Ok(Hold::Lit(false.into())),
            Pound { ch, tag } => Err(Error::unknown_spec_literal(*ch, tag)),
            Var(tag) => blk
                .locals
                .as_ref()
                .ok_or_else(|| Error::locals_unavailable(tag))
                .and_then(|locals| {
                    locals
                        .get(tag.str())
                        .ok_or_else(|| Error::var_not_found(tag))
                })
                .map(|local| match local {
                    Local::Var(var) => Hold::Var(var.clone()),
                    Local::Param(arg) => {
                        dbg!(&arg);
                        // debug checking about types here
                        #[cfg(debug_assertions)]
                        {
                            let tys = &blk.tg[node.idx()];
                            assert_eq!(tys.output.ty(), Some(arg.out_ty()));
                            assert_eq!(tys.input.ty(), Some(arg.in_ty()));
                        }

                        arg.hold.clone()
                    }
                }),
            Expr(tag) => {
                dbg!(&tag);
                blk.compiled_exprs
                    .get(&node.index())
                    .cloned()
                    .map(Hold::Expr)
                    .ok_or_else(|| Error::incomplete_expr_compilation(tag))
            }
        }
    }

    /// Assert this argument is a variable and construct a reference to it.
    ///
    /// If the block does not contain a reference to an up-to-date locals, and error is returned.
    ///
    /// # Type safety
    /// The variable will be created expecting the type `ty`. `set_data` only validates types in
    /// debug builds, be sure that testing occurs of code path to avoid UB in release.
    pub fn create_var_ref(self, ty: Type) -> Result<Variable> {
        match (self.blk.locals.as_mut(), &self.blk.ag[self.node.idx()]) {
            (Some(locals), astgraph::AstNode::Var(var)) => {
                Ok(locals.add_new_var(Str::new(var.str()), ty, var.clone()))
            }
            (None, astgraph::AstNode::Var(var)) => Err(Error::locals_unavailable(var)),
            (_, x) => {
                todo!("this should error with unexp arg variant, but the span_arg needs to change signature");
                //                 let (x, y) = Error::span_arg(x.tag());
                //                 Err(Error::unexp_arg_variant(x, y))
            }
        }
    }
}

impl<'a> Block<'a> {
    fn pop_index(&mut self) -> Result<ArgNode> {
        let arg = self
            .args
            .pop()
            .ok_or_else(|| Error::insufficient_args(self.blk_tag(), self.args_count))?;
        self.args_count += 1;
        Ok(arg)
    }

    /// Get the [`Block`]'s next argument.
    ///
    /// The argument is agnostic to whether it is a variable, literal, or expression.
    /// The return type is an argument builder, which can be used to assert type information
    /// about the argument.
    /// Once the assertations are done, use `.concrete()` to resolve that the types are known and
    /// an [`Argument`] is produced.
    pub fn next_arg(&mut self) -> Result<ArgBuilder<'_, 'a>> {
        let node = self.pop_index()?;
        // see if the input and/or output types are known
        let tys = &self.tg[node.idx()]; // node should exist
        let in_ty = Kn::from(&tys.input);
        let out_ty = Kn::from(&tys.output);

        Ok(ArgBuilder {
            blk: self,
            node,
            in_ty,
            out_ty,
        })
    }
}

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
                    Err(Error::unexp_arg_output_ty(&exp_ty, &self.out_ty, tag))
                }
            }
            Hold::Var(_) => Err(Error::unexp_arg_variant(tag, "variable")),
            Hold::Expr(_) => Err(Error::unexp_arg_variant(tag, "expression")),
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
        todo!();
        //         match &self.hold {
        //             Hold::Lit(x) => Ok(x.clone()),
        //             Hold::Var(v) => Ok(v.fetch(&cx.env).clone()),
        //             Hold::Expr(e) => resolve_expr(e, &self.in_ty, input(), cx.clone()).map(|x| x.0),
        //         }
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
        todo!();

        use std::borrow::Cow;
        enum R<'r> {
            V(Cow<'r, Value>),
            E(&'r Evaluator),
        }
        let r = match &self.hold {
            Hold::Lit(x) => R::V(Cow::Borrowed(x)),
            Hold::Var(x) => R::V(Cow::Owned(x.fetch(&cx.env).clone())),
            Hold::Expr(e) => todo!(), //R::E(e),
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
