use std::{convert::TryInto, fmt};
use crate::prelude::*;
use ast::{Tag, Expression, DefinitionImpl, Term};
use crate::lang::var::{Locals, Environment};
use Type as Ty;

type StepR = Result<(Value, Environment)>;

pub fn handle_help(expr: &Expression, definitions: &Definitions) -> Result<()> {
    // rejig on new proc
    if let Some(block) = expr.blocks.get(0) {
        let help = definitions.impls().get_help(&block.op())?;
        if block
            .terms()
            .iter()
            .any(|x| matches!(x, Term::Flag(f) if f.str() == "help"))
        {
            Err(err::help_as_error(help))
        } else {
            Ok(())
        }
    } else {
        Ok(())
    }
}

pub fn construct_evaluator(
    in_ty: Type,
    expr: Expression,
    defs: &Definitions,
    mut variables: Locals,
) -> Result<ExprEvaluator> {
    let mut evaluator = ExprEvaluator::new(in_ty, expr.tag, expr.blocks.len());

    for block in expr.blocks {
        let im = defs.impls().get_impl(&block.op(), evaluator.ty())?;
        let mut block = Block::new(evaluator.ty().clone(), defs, &mut variables, block);
        let step = match im {
            Implementation::Intrinsic { f, .. } => f(block),
            Implementation::Definition(def) => {
                DefImplEvaluator::build(&mut block, def).map(|evaluator| Step {
                    out_ty: evaluator.ty().clone(),
                    f: Box::new(move |input, cx| evaluator.eval(input, cx)),
                })
            }
        }?;
        evaluator.push_step(step);
    }

    Ok(evaluator)
}

// ###### CONTEXT ##############################################################
#[derive(Clone)]
pub struct Context<'a> {
    pub env: Environment,
    pub root: &'a std::path::Path,
    pub wd: &'a std::path::Path,
}

impl<'a> Context<'a> {
    /// _Always_ returns `Ok`.
    pub fn done<V: Into<Value>>(self, value: V) -> StepR {
        Ok((value.into(), self.env))
    }

    /// _Always_ returns `Ok`.
    pub fn done_o<T>(self, value: T) -> Result<(T, Environment)> {
        Ok((value, self.env))
    }
}

// ###### BLOCK ################################################################
/// Much of this data structure is around producing quality error messages.
pub struct Block<'d, 'v> {
    in_ty: Type,
    pub blk_tag: Tag,
    pub op_tag: Tag,
    /// Definitions,
    pub defs: &'d Definitions,
    /// Variables tracking.
    vars: &'v mut Locals,
    /// Must be empty upon finalisation, unused flags return error.
    ///
    /// > Stored in reverse order as a stack.
    flags: Vec<Tag>,
    /// Does not include flags.
    /// Must be empty upon finalisation, unused args return error.
    ///
    /// > Stored in reverse order as a stack.
    args: Vec<ast::Argument>,
    /// Counter of the arguments used.
    args_count: usize,
}

impl<'d, 'v> Block<'d, 'v> {
    pub fn new(
        in_ty: Type,
        defs: &'d Definitions,
        vars: &'v mut Locals,
        block: ast::Block,
    ) -> Self {
        let blk_tag = block.block_tag();
        let (op_tag, terms) = block.parts();

        let mut flags = Vec::new();
        // most of the time it will just be args
        let mut args = Vec::with_capacity(terms.len());

        for t in terms {
            match t {
                Term::Flag(f) => flags.push(f),
                Term::Arg(a) => args.push(a),
            }
        }

        flags.reverse();
        args.reverse();

        Self {
            in_ty,
            defs,
            blk_tag,
            op_tag,
            flags,
            args,
            args_count: 0,
            vars,
        }
    }

    pub fn in_ty(&self) -> &Type {
        &self.in_ty
    }

    /// Returns the _number of arguments remaining_.
    pub fn args_len(&self) -> usize {
        self.args.len()
    }

    fn next_arg_raw(&mut self) -> Result<ast::Argument> {
        let arg = self
            .args
            .pop()
            .ok_or_else(|| Error::insufficient_args(&self.blk_tag, self.args_count))?;
        self.args_count += 1;
        Ok(arg)
    }

    /// Get the [`Block`]'s next argument.
    ///
    /// The argument is agnostic to the flavour of definition, if it is a literal or variable, the
    /// output type is set to what it is. If the argument is an expression, an evaluator is
    /// constructed given the input type. This drives the output type.
    ///
    /// ## Input type
    /// If no input type is specified (`None`), then the _blocks_ input type is used to feed into
    /// the expression. **It must be ensured that the correct [`Value`] type is supplied to the
    /// expression.**
    ///
    /// > For **input agnostic functions**, the `input_type` should be set to [`Type::Nil`] and the
    /// > input value passed through is [`Value::Nil`].
    pub fn next_arg<I: Into<Option<Type>>>(&mut self, input_type: I) -> Result<Argument> {
        let arg = self.next_arg_raw()?;
        self.arg_recursive(
            arg,
            input_type.into().unwrap_or_else(|| self.in_ty().clone()),
            self.vars,
        )
    }

    /// Works in the same fashion as [`Block::next_arg`], but **does not remove the argument from
    /// the argument stack**. This should not be used except in edge cases where the argument is
    /// required more than once.
    pub fn next_arg_do_not_remove<I: Into<Option<Type>>>(
        &mut self,
        input_type: I,
    ) -> Result<Argument> {
        let arg = self.next_arg_raw()?;
        self.args.push(arg.clone());
        self.args_count = self.args_count.saturating_sub(1);
        self.arg_recursive(
            arg,
            input_type.into().unwrap_or_else(|| self.in_ty().clone()),
            self.vars,
        )
    }

    fn arg_recursive(&self, arg: ast::Argument, in_ty: Type, locals: &Locals) -> Result<Argument> {
        use ast::Argument as A;

        fn make_input_pound_expr(in_ty: Type, tag: Tag) -> ExprEvaluator {
            ExprEvaluator {
                tag,
                out_ty: in_ty.clone(),
                steps: vec![Step {
                    out_ty: in_ty,
                    f: Box::new(|i, cx| cx.done(i)),
                }],
            }
        }

        let (hold, tag, out_ty) = match arg {
            A::Ident(ident) => (Hold::Lit(Str::new(ident.str()).into()), ident, Type::Str),
            A::Num(n, tag) => (Hold::Lit(n.into()), tag, Type::Num),
            A::Pound('t', tag) => (Hold::Lit(true.into()), tag, Type::Bool),
            A::Pound('f', tag) => (Hold::Lit(false.into()), tag, Type::Bool),
            A::Pound('n', tag) => (Hold::Lit(Value::Nil), tag, Type::Nil),
            A::Pound('i', tag) => (
                Hold::Expr(make_input_pound_expr(in_ty.clone(), tag.clone())),
                tag,
                in_ty.clone(),
            ),
            A::Pound(ch, tag) => return Err(Error::unknown_spec_literal(ch, &tag)),
            A::Var(var) => {
                match locals
                    .get(var.str())
                    .ok_or_else(|| Error::var_not_found(&var))?
                {
                    Local::Param(arg, locals) => {
                        // update result with the outside var (similar to Local::Var)
                        return self
                            .arg_recursive(arg.clone(), in_ty, locals)
                            .map_err(|e| e.add_trace(&var))
                            .map(|mut x| (x.tag = var, x).1);
                    }
                    Local::Var(v) => {
                        let mut v = v.clone();
                        // update the location of this var to give correct error reporting
                        v.tag = var.clone();
                        let ty = v.ty().clone();
                        (Hold::Var(v), var, ty)
                    }
                }
            }
            A::Expr(expr) => {
                let tag = expr.tag.clone();
                let eval = construct_evaluator(in_ty.clone(), expr, self.defs, locals.clone())
                    .map_err(|e| e.add_trace(&self.blk_tag))?;
                let out_ty = eval.out_ty.clone();
                (Hold::Expr(eval), tag, out_ty)
            }
        };

        Ok(Argument {
            tag,
            in_ty,
            out_ty,
            hold,
        })
    }

    /// Gets the flag that matches a given name.
    ///
    /// If no name is given with `None`, _the first flag first is returned, if there is one._
    ///
    /// > The flag is **removed** from the flag stack.
    pub fn get_flag<'a, N: Into<Option<&'a str>>>(&mut self, flag: N) -> Option<Tag> {
        match flag.into() {
            Some(name) => self
                .flags
                .iter()
                .position(|x| x.str() == name)
                .map(|i| self.flags.remove(i)),
            None => self.flags.pop(),
        }
    }

    /// Create a variable reference using the next argument.
    ///
    /// Returns an error if:
    /// 1. There is no next argument,
    /// 2. The next argument is _not_ a variable,
    ///
    /// # Type safety
    /// The variable will be created expecting the type `ty`. `set_data` only validates types in
    /// debug builds, be sure that testing occurs of code path to avoid UB in release.
    pub fn create_var_ref(&mut self, ty: Type) -> Result<Variable> {
        match self.next_arg_raw()? {
            ast::Argument::Var(var) => Ok(self.vars.add_new_var(Str::new(var.str()), ty, var)),
            x => {
                let (x, y) = Error::span_arg(&x);
                Err(Error::unexp_arg_variant(x, y))
            }
        }
    }

    /// Create a variable reference not off a specific argument, but by manually specifying the
    /// variable name.
    ///
    /// This is useful for expressions that need to supply more than just the input. For instance
    /// the `fold` command will supply the `$row` variable which is a track of the TableRow
    ///
    /// The tag is usually `blk.op_tag`.
    pub fn create_var_manually<N: Into<Str>>(&mut self, name: N, ty: Type, tag: Tag) -> Variable {
        self.vars.add_new_var(name.into(), ty, tag)
    }

    /// Most flexible evaluation option, but also most brittle.
    ///
    /// **BE EXTRA CAREFUL WITH THE `out_ty` THAT IT MATCHES THE EVAL VALUE.
    /// It is recommended to thoroughly test code paths through here to ensure type validity.**
    ///
    /// # Usage
    /// - Input value ([`Value`]) should be cast to expected input type (use `.try_into()?`).
    /// - Arguments can use this type if they are expecting the blocks input.
    ///
    /// ## Arguments
    /// Arguments **do not need to use blocks input**. If no input type is needed, the argument can
    /// be built with `Type::Nil` and `Value::Nil` can be passed on through!
    pub fn eval<F>(self, out_ty: Type, f: F) -> Result<Step>
    where
        F: Fn(Value, Context) -> StepR + Sync + 'static,
    {
        self.finalise()?;
        Ok(Step {
            out_ty,
            f: Box::new(f),
        })
    }

    /// Preferred way of creating a eval step.
    ///
    /// This supplies the [`Value`] input but uses type inference on `O` to get the output type.
    pub fn eval_o<F, O>(self, f: F) -> Result<Step>
    where
        F: Fn(Value, Context) -> Result<(O, Environment)> + Sync + 'static,
        O: AsType + Into<Value>,
    {
        self.eval(O::as_type(), move |v, c| {
            f(v, c).map(|(x, e)| (Into::into(x), e))
        })
    }

    fn finalise(&self) -> Result<()> {
        if let Some(flag) = self.flags.last() {
            Err(Error::unused_flag(flag))
        } else if let Some(arg) = self.args.get(0) {
            Err(Error::unused_arg(arg))
        } else {
            Ok(())
        }
    }
}

// ###### STEP #################################################################

pub struct Step {
    out_ty: Type,
    f: Box<dyn Fn(Value, Context) -> StepR + Sync>,
}

impl Step {
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

impl fmt::Debug for Step {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Step")
            .field("out_ty", &self.out_ty)
            .finish()
    }
}

// ###### EVALUATOR ############################################################
#[derive(Debug)]
pub struct ExprEvaluator {
    tag: Tag,
    /// This is the type that is the output of the previous block, and is the _input_ for the next
    /// block.
    out_ty: Type,
    /// Each block converted into a function.
    steps: Vec<Step>,
}

impl ExprEvaluator {
    fn new(in_ty: Type, tag: Tag, stepslen: usize) -> ExprEvaluator {
        ExprEvaluator {
            tag,
            out_ty: in_ty,
            steps: Vec::with_capacity(stepslen),
        }
    }

    /// Asserts that the expressions returns the type `ty` once resolved.
    pub fn returns(self, ty: &Type) -> Result<Self> {
        if &self.out_ty == ty {
            Ok(self)
        } else {
            Err(Error::unexp_arg_ty(ty, &self.out_ty, &self.tag))
        }
    }

    /// The output type of this expression.
    ///
    /// This updates when `push_step` is used to add another step. The output will become the
    /// output of [`Step`].
    pub fn ty(&self) -> &Type {
        &self.out_ty
    }

    pub fn tag(&self) -> &Tag {
        &self.tag
    }

    pub fn push_step(&mut self, step: Step) {
        self.out_ty = step.out_ty.clone();
        self.steps.push(step);
    }

    pub fn eval(&self, input: Value, cx: Context) -> StepR {
        let mut input = input;
        let Context { root, wd, mut env } = cx;
        for step in &self.steps {
            let (new_input, new_env) = step.invoke(input, Context { env, root, wd })?;
            input = new_input;
            env = new_env;
        }
        Ok((input, env))
    }
}

type ParamEval = (Variable, Argument);

/// This is similar to [`ExprEvaluator`] but has extra handling to greedily evaluate parameters,
/// assigning them to variables.
pub struct DefImplEvaluator {
    /// Parameters to be evaluated _before_ evaluating the expression.
    /// This sets the parameter values.
    params: Vec<ParamEval>,
    /// The evaluator of the definition expression.
    expr_eval: ExprEvaluator,
}

impl DefImplEvaluator {
    /// This is used by the main HIR routine for user defined impls, but it can also be used to inject
    /// an implementation 'on the fly' at the HIR phase from an _intrinsic_ impl.
    /// This is useful to keep HIR routine checking (such as using `eq` and `cmp` which might have user
    /// impls), but should be uesd with care as the [`DefinitionImpl`] must be defined on the fly and
    /// might not have the same checking as going through the regular parsing system.
    pub fn build(blk: &mut Block, def: &DefinitionImpl) -> Result<Self> {
        let defs = blk.defs;
        // calls into users defs should not have visibility of current variables, so we construct
        // a new variables map, where the known variables are the parameters
        let (vars, params) = Self::construct_params(blk, def)?;

        let in_ty = blk.in_ty().clone();
        let expr_eval = construct_evaluator(in_ty, def.expr.clone(), defs, vars)
            .map_err(|e| e.add_trace(&blk.blk_tag))?;

        Ok(Self { params, expr_eval })
    }

    /// The output type of this expression.
    pub fn ty(&self) -> &Type {
        self.expr_eval.ty()
    }

    /// Asserts that the expressions returns the type `ty` once resolved.
    pub fn returns(self, ty: &Type) -> Result<Self> {
        Ok(Self {
            expr_eval: self.expr_eval.returns(ty)?,
            ..self
        })
    }

    /// Resolves the parameters, then evals the expr.
    pub fn eval(&self, input: Value, mut cx: Context) -> StepR {
        for (var, arg) in &self.params {
            let v = arg.resolve(|| input.clone(), &cx)?;
            var.set_data(&mut cx.env, v);
        }

        self.expr_eval.eval(input, cx)
    }

    /// Construct a [`Locals`] environment which encapsulates the parameters as variables.
    /// The default position is to evaluate the parameters upon entry, store these in variables,
    /// and use the evaluated value.
    /// There exists an option to pass through an expr which is _not_ to be evaluated, which has
    /// use cases for passing through predicates and the like.
    /// This case requires some variable aliasing jiggery-pokery.
    fn construct_params(blk: &mut Block, def: &DefinitionImpl) -> Result<(Locals, Vec<ParamEval>)> {
        use ast::Argument as A;
        let mut locals = blk.vars.enter_impl();
        let mut params = Vec::with_capacity(def.params.len());

        for param in &def.params {
            let ast::Parameter { ident, ty } = param;
            let name = Str::new(ident.str());
            if ty.as_ref().map(|x| x.str() == "Expr").unwrap_or(false) {
                match blk.next_arg_raw()? {
                    A::Var(var) => match blk
                        .vars
                        .get(var.str())
                        .cloned()
                        .ok_or_else(|| Error::var_not_found(&var))?
                    {
                        Local::Var(v) => locals.add_var(name, v),
                        Local::Param(a, l) => locals.add_param(name, a, l),
                    },
                    x => locals.add_param(name, x, blk.vars.clone()),
                }
            } else {
                let arg = blk.next_arg(None)?;
                let arg = if let Some(ty) = ty {
                    let ty = blk.defs.types().get_using_tag(ty)?;
                    arg.returns(ty)?
                } else {
                    arg
                };
                let var = locals.add_new_var(name, arg.out_ty().clone(), ident.clone());
                params.push((var, arg));
            }
        }

        blk.finalise()?;

        Ok((locals, params))
    }
}

// ###### ARGUMENT #############################################################
pub struct Argument {
    pub tag: Tag,
    in_ty: Type,
    out_ty: Type,
    hold: Hold,
}

enum Hold {
    Lit(Value),
    Var(Variable),
    Expr(ExprEvaluator),
}

impl Argument {
    pub fn tag(&self) -> &Tag {
        &self.tag
    }

    pub fn in_ty(&self) -> &Type {
        &self.in_ty
    }

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
                err = err.add_trace(&e.tag);
            };
            Err(err)
        }
    }

    /// Resolve the argument to it's [`Value`]. This means passing a literal through, fetching a
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
            E(&'r ExprEvaluator),
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

fn resolve_expr(expr: &ExprEvaluator, inty: &Type, input: Value, cx: Context) -> StepR {
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

// ###### TESTS ################################################################
#[cfg(test)]
mod tests {
    use super::*;
    use lang::syntax::parse::expression;
    use ast::Location;

    #[test]
    fn no_cmd_defined() {
        let src = "undefined";
        let defs = &Definitions::new();
        let vars = Locals::default();
        let x = construct_evaluator(
            Type::Nil,
            expression(src, Location::Shell, defs).unwrap(),
            defs,
            vars,
        )
        .unwrap_err()
        .to_string();
        assert_eq!(
            &x,
            "Unknown Command: operation `undefined` not defined
--> shell:0
 | undefined
 | ^^^^^^^^^ `undefined` not found
--> help: view a list of definitions using `def --list`
"
        );

        // try nested one
        let src = "\\ file.csv | undefined";
        let x = construct_evaluator(
            Type::Nil,
            expression(src, Location::Shell, defs).unwrap(),
            defs,
            Locals::default(),
        )
        .unwrap_err()
        .to_string();
        assert_eq!(
            &x,
            r#"Unknown Command: operation `undefined` not defined
--> shell:13
 | \ file.csv | undefined
 |              ^^^^^^^^^ `undefined` not found
--> help: view a list of definitions using `def --list`
"#
        );
    }

    #[test]
    fn incorrect_input_syntax() {
        let src = "\\ file.csv | \\";
        let defs = &Definitions::new();
        let vars = Locals::default();
        let x = construct_evaluator(
            Type::Nil,
            expression(src, Location::Shell, defs).unwrap(),
            defs,
            vars,
        )
        .unwrap_err()
        .to_string();
        assert_eq!(
            &x,
            r#"Semantics Error: expecting more than 0 arguments
--> shell:13
 | \ file.csv | \
 |              ^ expecting additional argument(s)
--> help: try using the `--help` flag to view requirements
"#
        );
    }
}
