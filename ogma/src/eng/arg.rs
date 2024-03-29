use super::*;
use graphs::{
    tygraph::{Knowledge, TypesSet},
    *,
};
use std::convert::TryInto;

// ###### ARG BUILDER ##########################################################
pub struct ArgBuilder<'a> {
    node: ArgNode,
    in_ty: Kn,
    out_ty: Kn,

    compiler: &'a Compiler<'a>,
    blk_in_ty: Option<Type>,
    chgs: &'a mut Chgs,
}

impl<'a> ArgBuilder<'a> {
    pub(super) fn new(
        node: ArgNode,
        compiler: &'a Compiler<'a>,
        chgs: &'a mut Chgs,
        blk_in_ty: Option<Type>,
    ) -> Box<Self> {
        // see if the input and/or output types are known
        let tys = &compiler.tg[node.idx()]; // node should exist
        let in_ty = Kn::from(&tys.input);
        let out_ty = Kn::from(&tys.output);

        Box::new(ArgBuilder {
            node,
            in_ty,
            out_ty,
            compiler,
            chgs,
            blk_in_ty,
        })
        .follow_local_arg_ptr()
    }

    fn follow_local_arg_ptr(mut self: Box<Self>) -> Box<Self> {
        let new_node = self.compiler.ag[self.node.idx()]
            .var()
            .and_then(|t| self.compiler.lg.get_opt(self.node.idx(), t.str()).1)
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
        self.compiler.ag[self.node.idx()].tag()
    }

    pub fn node(&self) -> ArgNode {
        self.node
    }

    /// Flag that this argument does not require it's parent op to be sealed for variable
    /// resolution.
    ///
    /// This method is only required when variables are being introduced, see
    /// [`Block::assert_adds_vars`] for more information and usage practices.
    pub fn decouple_op_seal(self: Box<Self>) -> Box<Self> {
        let arg = self.node();
        let op = arg.op(self.compiler.ag());
        self.chgs
            .chgs
            .push(locals_graph::Chg::BreakEdge { op, arg }.into());
        self
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
            Kn::Tys(ts) if ts.contains(&ty) => {
                // the set supports `ty`, so we tell the TG that this input can be upgraded
                debug_assert!(
                    ts.len() > 1,
                    "expecting TypesSet to not be empty or a single set"
                );
                self.chgs
                    .chgs
                    .push(tygraph::Chg::KnownInput(self.node.idx(), ty).into());
                Err(Error::unknown_arg_input_type(self.tag()))
            }
            Kn::Tys(_ts) => Err(Error::unknown_arg_input_type(self.tag())),
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
            Kn::Tys(ts) if ts.contains(&ty) => {
                // the set supports `ty`, so we tell the TG that this output can be upgraded
                debug_assert!(
                    ts.len() > 1,
                    "expecting TypesSet to not be empty or a single set"
                );
                self.chgs
                    .chgs
                    .push(tygraph::Chg::ObligeOutput(self.node.idx(), ty).into());
                Err(Error::unknown_arg_output_type(self.tag()))
            }
            Kn::Tys(_ts) => Err(Error::unknown_arg_output_type(self.tag())),
            Kn::Any => unreachable!("logic error if output is Any type"),
        }
    }

    pub fn return_ty(&self) -> Option<&Type> {
        match &self.out_ty {
            Kn::Ty(t) => Some(t),
            Kn::Tys(_) | Kn::Any => None,
        }
    }

    /// Asserts that the arguments input and output types are known, and if so, returns a concrete
    /// [`Argument`] with the ability to evaluate.
    pub fn concrete(self) -> Result<Argument> {
        // assert that if this is a variable type, the variable exists.
        // This is done to ensure sane errors are returned
        self.assert_var_exists()?;

        use Kn::*;

        let tag = self.tag().clone();

        let Self {
            node,
            in_ty,
            out_ty,
            compiler,
            ..
        } = self;

        match (in_ty, out_ty) {
            (Any | Tys(_), _) => Err(Error::unknown_arg_input_type(&tag)),
            (_, Any | Tys(_)) => Err(Error::unknown_arg_output_type(&tag)),
            (Ty(in_ty), Ty(out_ty)) => {
                let hold = Box::new(Self::map_astnode_into_hold(node, compiler)?);

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

    fn map_astnode_into_hold(node: ArgNode, compiler: &Compiler) -> Result<Hold> {
        use astgraph::AstNode::*;
        use astgraph::PoundTy as Pt;

        let Compiler {
            ag,
            tg,
            lg,
            compiled_exprs,
            ..
        } = compiler;

        match &ag[node.idx()] {
            Op { op: _, blk: _ } => unreachable!("an argument cannot be an Op variant"),
            Flag(_) => unreachable!("an argument cannot be a Flag variant"),
            Intrinsic { .. } => unreachable!("an argument cannot be a Intrinsic variant"),
            Def { .. } => unreachable!("an argument cannot be a Def variant"),

            Ident(s) => Ok(Hold::Lit(Str::new(s.str()).into())),
            Num { val, tag: _ } => Ok(Hold::Lit((*val).into())),
            Pound {
                ty: Pt::Nil,
                tag: _,
            } => Ok(Hold::Lit(Value::Nil)),
            Pound {
                ty: Pt::True,
                tag: _,
            } => Ok(Hold::Lit(true.into())),
            Pound {
                ty: Pt::False,
                tag: _,
            } => Ok(Hold::Lit(false.into())),
            Pound {
                ty: Pt::Newline,
                tag: _,
            } => Ok(Hold::Lit(Value::Str(Str::from('\n')))),
            Pound {
                ty: Pt::Input,
                tag: _,
            } => {
                // The input literal is a single step which takes the input and passes it straight
                // through
                let out_ty = tg[node.idx()]
                    .output
                    .ty()
                    .cloned()
                    .expect("output type should be known");
                #[allow(unused_mut)]
                let mut stack = eval::Stack::new(vec![Step {
                    out_ty,
                    f: Arc::new(|input, cx| cx.done(input)),
                }]);
                #[cfg(debug_assertions)]
                stack.add_types(&tg[node.idx()]);

                Ok(Hold::Expr(stack))
            }
            Var(tag) => lg
                .get(node.idx(), tag.str(), tag)
                .and_then(|local| match local {
                    Local::Var(var) => Ok(Hold::Var(var.clone())),
                    Local::Ptr { .. } => {
                        unreachable!("a param argument should shadow the referencer arg node")
                    }
                }),
            Expr(tag) => compiled_exprs
                .get(&node.index())
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
        match self.node.var(self.compiler.ag()) {
            Some(var) => match self.compiler.lg.get_opt(self.node.idx(), var.str()) {
                (true, Some(_)) => Ok(Some(true)),
                (true, None) => Err(Error::var_not_found(var)),
                (false, _) => Ok(Some(false)),
            },
            None => Ok(None), // not a variable
        }
    }
}

#[derive(Debug)]
enum Kn {
    Any,
    Ty(Type),
    Tys(TypesSet),
}

impl From<&Knowledge> for Kn {
    fn from(kn: &Knowledge) -> Self {
        match kn {
            Knowledge::Any => Kn::Any,
            Knowledge::Known(t) | Knowledge::Obliged(t) => Kn::Ty(t.clone()),
            Knowledge::Inferred(ts) => match ts.only() {
                Some(t) => Kn::Ty(t.clone()),
                None => Kn::Tys(ts.clone()),
            },
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

        #[cfg(debug_assertions)]
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

            #[cfg(debug_assertions)]
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

        let Block {
            chgs,
            in_ty,
            args,
            args_count,
            ..
        } = self;

        let node = pop(args, *args_count, &btag)?;
        *args_count += 1;

        Ok(ArgBuilder::new(
            node,
            self.compiler,
            chgs,
            Some(in_ty.clone()),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn structures_sizing() {
        use std::mem::size_of;

        assert_eq!(size_of::<Argument>(), 48);
        assert_eq!(size_of::<Hold>(), 64 - 8);
        assert_eq!(size_of::<arg::ArgBuilder>(), 88 - 16);
    }
}
