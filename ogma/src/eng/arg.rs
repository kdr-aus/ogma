use super::*;
use graphs::{astgraph::AstGraph, locals_graph::LocalsGraph, tygraph::Knowledge, *};
use std::convert::TryInto;

// ###### ARG BUILDER ##########################################################
pub struct ArgBuilder<'a> {
    node: ArgNode,
    in_ty: Kn,
    out_ty: Kn,

    // compiler references
    ag: &'a AstGraph,
    lg: &'a LocalsGraph,
    blk_in_ty: Option<Type>,
    chgs: Chgs<'a>,
    compiled_exprs: &'a IndexMap<eval::Stack>,

    #[cfg(debug_assertions)]
    tg: &'a tygraph::TypeGraph,
}

impl<'a> ArgBuilder<'a> {
    pub fn new(
        node: ArgNode,
        ag: &'a AstGraph,
        tg: &'a tygraph::TypeGraph,
        lg: &'a LocalsGraph,
        chgs: Chgs<'a>,
        blk_in_ty: Option<Type>,
        compiled_exprs: &'a IndexMap<eval::Stack>,
    ) -> Box<Self> {
        // see if the input and/or output types are known
        let tys = &tg[node.idx()]; // node should exist
        let in_ty = Kn::from(&tys.input);
        let out_ty = Kn::from(&tys.output);

        Box::new(ArgBuilder {
            node,
            in_ty,
            out_ty,
            ag,
            lg,
            chgs,
            blk_in_ty,
            compiled_exprs,
            tg,
        })
        .follow_local_arg_ptr()
    }

    fn follow_local_arg_ptr(mut self: Box<Self>) -> Box<Self> {
        let new_node = self.ag[self.node.idx()]
            .var()
            .and_then(|t| self.lg.get(self.node.idx(), t.str()))
            .and_then(|l| match l {
                Local::Ptr { to, tag: _ } => Some(to),
                _ => None,
            })
            .copied();

        if let Some(node) = new_node {
            self.node = node;
            self.follow_local_arg_ptr()
        } else {
            self
        }
    }

    /// The arguments tag.
    pub fn tag(&self) -> &Tag {
        self.ag[self.node.idx()].tag()
    }

    pub fn node(&self) -> ArgNode {
        self.node
    }

    /// Assert that this argument will be supplied an input of type `ty`.
    ///
    /// > Since the **blocks's** input type is used often, and trying to pass this through is
    /// > difficult with mutable aliasing, the type argument is an `Option`, where the `None`
    /// > variant represents _using the block's input type_.
    pub fn supplied<T: Into<Option<Type>>>(mut self: Box<Self>, ty: T) -> Result<Box<Self>> {
        let ty = match ty.into().or_else(|| self.blk_in_ty.clone()) {
            Some(ty) => ty,
            None => return Ok(self),
        };

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
                self.chgs
                    .push(tygraph::Chg::KnownInput(self.node.idx(), ty).into());
                Err(Error::unknown_arg_input_type(self.tag()))
            }
            Kn::Any => unreachable!("any is reset to Kn::Ty"),
        }
    }

    /// Assert that this argument returns a value of type `ty`.
    pub fn returns(self: Box<Self>, ty: Type) -> Result<Box<Self>> {
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
                self.chgs
                    .push(tygraph::Chg::ObligeOutput(self.node.idx(), ty).into());
                Err(Error::unknown_arg_output_type(self.tag()))
            }
            Kn::Any => unreachable!("logic error if output is Any type"),
        }
    }

    pub fn return_ty(&self) -> Option<&Type> {
        match &self.out_ty {
            Kn::Ty(t) => Some(t),
            Kn::Any | Kn::Unknown => None,
        }
    }

    /// Asserts that the arguments input and output types are known, and if so, returns a concrete
    /// [`Argument`] with the ability to evaluate.
    pub fn concrete(mut self: Box<Self>) -> Result<Argument> {
        // assert that if this is a variable type, the variable exists.
        // This is done to ensure sane errors are returned
        self.assert_var_exists()?;

        use Kn::*;

        let tag = self.tag().clone();

        let in_ty = self.in_ty.take();
        let out_ty = self.out_ty.take();

        match (in_ty, out_ty) {
            (Unknown | Any, _) => Err(Error::unknown_arg_input_type(&tag)),
            (_, Unknown | Any) => Err(Error::unknown_arg_output_type(&tag)),
            (Ty(in_ty), Ty(out_ty)) => {
                let hold = Box::new(self.map_astnode_into_hold()?);

                if hold.ty().as_ref() == &out_ty {
                    Ok(Argument {
                        tag,
                        in_ty,
                        out_ty,
                        hold,
                    })
                } else {
                    Err(Error::unexp_arg_output_ty(&out_ty, &hold.ty(), &tag))
                }
            }
        }
    }

    fn map_astnode_into_hold(self: Box<Self>) -> Result<Hold> {
        use astgraph::AstNode::*;

        match &self.ag[self.node.idx()] {
            Op { op: _, blk: _ } => unreachable!("an argument cannot be an Op variant"),
            Flag(_) => unreachable!("an argument cannot be a Flag variant"),
            Intrinsic { .. } => unreachable!("an argument cannot be a Intrinsic variant"),
            Def { .. } => unreachable!("an argument cannot be a Def variant"),
            Ident(s) => Ok(Hold::Lit(Str::new(s.str()).into())),
            Num { val, tag: _ } => Ok(Hold::Lit((*val).into())),
            Pound { ch: 'n', tag: _ } => Ok(Hold::Lit(Value::Nil)),
            Pound { ch: 't', tag: _ } => Ok(Hold::Lit(true.into())),
            Pound { ch: 'f', tag: _ } => Ok(Hold::Lit(false.into())),
            Pound { ch: 'i', tag: _ } => {
                // The input literal is a single step which takes the input and passes it straight
                // through
                let out_ty = self.tg[self.node.idx()]
                    .output
                    .ty()
                    .cloned()
                    .expect("output type should be known");
                let mut stack = eval::Stack::new(vec![Step {
                    out_ty,
                    f: Arc::new(|input, cx| cx.done(input)),
                }]);
                #[cfg(debug_assertions)]
                stack.add_types(&self.tg[self.node.idx()]);

                Ok(Hold::Expr(stack))
            }
            Pound { ch, tag } => Err(Error::unknown_spec_literal(*ch, tag)),
            Var(tag) => self
                .lg
                .get_checked(self.node.idx(), tag.str(), tag)
                .and_then(|local| match local {
                    Local::Var(var) => Ok(Hold::Var(var.clone())),
                    Local::Ptr { .. } => {
                        unreachable!("a param argument should shadow the referencer arg node")
                    }
                }),
            Expr(tag) => self
                .compiled_exprs
                .get(&self.node.index())
                .cloned()
                .map(Hold::Expr)
                .ok_or_else(|| Error::incomplete_expr_compilation(tag)),
        }
    }

    /// Checks if a variable variant exists in the locals.
    ///
    /// This is meant to be used as a sense check with a hard error if the variable name does not
    /// exist in the available locals. Since there are a few ways this function might not work, the
    /// return type encodes some of the states. The `Err` variant is reserved for the hard error
    /// case where the variable does not exist in the locals.
    ///
    /// - `Ok(None)`: This is not a variable variant,
    /// - `Ok(Some(false))`: `LocalsGraph` requires updating.
    /// - `Ok(Some(true))`: The variable exists in the locals,
    /// - `Err(_)`: The variable does not exist in the locals.
    pub fn assert_var_exists(&self) -> Result<Option<bool>> {
        match &self.ag[self.node.idx()] {
            astgraph::AstNode::Var(tag) => {
                self.lg
                    .get(self.node.idx(), tag.str())
                    // Ok(Some(true)) if variable exists
                    .map(|_| true)
                    // if NOT sealed, return Ok(Some(false)) -- lg should be updated
                    // NOTE we check the parent op for seal, not the argument itself.
                    .or_else(|| {
                        let sealed = self.lg.sealed(self.node.op(self.ag).idx());
                        (!sealed).then(|| false)
                    })
                    // Error with a HARD error
                    .ok_or_else(|| Error::var_not_found(tag))
                    .map(Some)
            }
            _ => Ok(None), // not a variable
        }
    }
}

#[derive(Debug)]
enum Kn {
    Unknown,
    Any,
    Ty(Type),
}

impl Kn {
    /// Replace this Kn with `Unknown` and return what was there.
    fn take(&mut self) -> Self {
        std::mem::replace(self, Kn::Unknown)
    }
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

// ###### ARGUMENT #############################################################
/// Compiled argument.
#[derive(Debug)]
pub struct Argument {
    /// The argument tag.
    pub tag: Tag,
    in_ty: Type,
    out_ty: Type,
    hold: Box<Hold>,
}

#[derive(Debug)]
enum Hold {
    Lit(Value),
    Var(Variable),
    Expr(eval::Stack),
}

pub fn pop(args: &mut Vec<ArgNode>, arg_count: u8, err_tag: &Tag) -> Result<ArgNode> {
    args.pop()
        .ok_or_else(|| Error::insufficient_args(err_tag, arg_count, None))
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

        match &*self.hold {
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
        let r = match &*self.hold {
            Hold::Lit(x) => Ok(x.clone()),
            Hold::Var(v) => Ok(v.fetch(&cx.env).clone()),
            Hold::Expr(stack) => stack.eval(input(), cx.clone()).map(|x| x.0),
        };

        if let Ok(v) = &r {
            self.assert_resolved_type(v);
        }

        r
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
            E(&'r eval::Stack),
        }
        let r = match &*self.hold {
            Hold::Lit(x) => R::V(Cow::Borrowed(x)),
            Hold::Var(x) => R::V(Cow::Owned(x.fetch(&cx.env).clone())),
            Hold::Expr(e) => R::E(e),
        };

        move |input| {
            let r = match &r {
                R::V(v) => Ok(v.as_ref().clone()),
                R::E(e) => e.eval(input, cx.clone()).map(|x| x.0),
            };

            if let Ok(v) = &r {
                self.assert_resolved_type(v);
            }

            r
        }
    }

    #[cfg(debug_assertions)]
    fn assert_resolved_type(&self, value: &Value) {
        let returned_ty = &value.ty();
        let exp_ty = &self.out_ty;

        assert_eq!(
            returned_ty, exp_ty,
            "the argument's output type does not match the expected type"
        );
    }
}

impl Hold {
    pub fn ty(&self) -> std::borrow::Cow<Type> {
        use std::borrow::Cow::*;
        match self {
            Hold::Lit(v) => Owned(v.ty()),
            Hold::Var(v) => Borrowed(v.ty()),
            Hold::Expr(s) => Borrowed(s.out_ty()),
        }
    }
}

impl<'a> Block<'a> {
    /// Get the [`Block`]'s next argument.
    ///
    /// The argument is agnostic to whether it is a variable, literal, or expression.
    /// The return type is an argument builder, which can be used to assert type information
    /// about the argument.
    /// Once the assertations are done, use `.concrete()` to resolve that the types are known and
    /// an [`Argument`] is produced.
    pub fn next_arg(&mut self) -> Result<Box<ArgBuilder>> {
        let btag = self.blk_tag().clone();
        let node = pop(&mut self.args, self.args_count, &btag)?;
        self.args_count += 1;

        let Block {
            ag,
            tg,
            lg,
            chgs,
            in_ty: blk_in_ty,
            compiled_exprs,
            ..
        } = self;

        let blk_in_ty = Some(blk_in_ty.clone());

        Ok(ArgBuilder::new(
            node,
            ag,
            tg,
            lg,
            chgs,
            blk_in_ty,
            compiled_exprs,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn structures_sizing() {
        use std::mem::size_of;

        // TODO review this sizing, maybe it can be reduced by boxing
        assert_eq!(size_of::<Argument>(), 48);
        assert_eq!(size_of::<Hold>(), 64);
        assert_eq!(size_of::<arg::ArgBuilder>(), 96);
    }
}
