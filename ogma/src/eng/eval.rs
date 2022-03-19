//! Evaluation.

use super::*;

#[derive(Debug, Clone)]
pub struct Stack {
    #[cfg(debug_assertions)]
    in_ty: Type,

    #[cfg(debug_assertions)]
    out_ty: Type,

    /// Each block converted into a function.
    steps: Vec<Step>,
}

impl Stack {
    pub fn new(steps: Vec<Step>) -> Self {
        Self {
            steps,

            #[cfg(debug_assertions)]
            in_ty: Type::Nil,

            #[cfg(debug_assertions)]
            out_ty: Type::Nil,
        }
    }

    pub fn out_ty(&self) -> &Type {
        &self.steps.last().expect("at least one step").out_ty
    }

    pub fn eval(&self, value: Value, cx: Context) -> Result<(Value, Environment)> {
        debug_assert_eq!(
            value.ty(),
            self.in_ty,
            "expecting input value into Stack to match Stack's input type"
        );

        let Context { mut env, root, wd } = cx;

        let mut input = value;
        for step in &self.steps {
            let cx = Context { env, root, wd };
            let (output, new_env) = step.invoke(input, cx)?;
            input = output;
            env = new_env;
        }

        debug_assert_eq!(
            input.ty(),
            self.out_ty,
            "expecting the output value once evaluated to match Stack's output type"
        );

        Ok((input, env))
    }

    #[cfg(debug_assertions)]
    pub fn add_types(&mut self, tynode: &graphs::tygraph::Node) {
        self.in_ty = tynode
            .input
            .ty()
            .expect("expressions input type should be known at this point")
            .clone();
        self.out_ty = tynode
            .output
            .ty()
            .expect("expressions output type should be known at this point")
            .clone();
    }
}

impl From<Stack> for Step {
    fn from(stack: Stack) -> Step {
        let out_ty = stack
            .steps
            .last()
            .expect("at least one step")
            .out_ty
            .clone();
        let f = Arc::new(move |value: Value, cx: Context| stack.eval(value, cx));

        Step {
            out_ty,
            f,
            type_annotation: String::new(),
        }
    }
}

pub struct CodeInjector<T> {
    /// Map of block argument to an _injector's_ local variable.
    args: Vec<(Argument, Variable, Option<Value>)>,
    data: T,
}

pub struct Build {
    expr: ast::Expression,
    locals: var::SeedVars,
}
pub struct Eval {
    stack: Stack,
    env: Environment,
}

impl CodeInjector<Build> {
    pub fn new(code: impl Into<String>, defs: &Definitions) -> Result<Self> {
        let expr =
            lang::parse::expression(code.into(), ast::Location::Ogma, defs).map_err(|e| e.0)?;

        Ok(Self {
            args: Vec::new(),
            data: Build {
                expr,
                locals: Default::default(),
            },
        })
    }

    /// Map the **next** block argument to the specified variable `name`.
    /// Optionally specify a concrete input (think `Value::Nil`), or leave `None` to use the
    /// block's input.
    /// `returns` is the variable type.
    pub fn map_arg_to_var<N: Into<Str>>(
        &mut self,
        blk: &mut Block,
        name: N,
        input: Option<Value>,
        returns: Type,
    ) -> Result<()> {
        let arg = blk
            .next_arg()?
            .supplied(input.as_ref().map(|x| x.ty()))?
            .returns(returns)?
            .concrete()?;
        let ty = arg.out_ty().clone();
        // TODO is there a way to not use a default tag?
        let var = self.data.locals.add(name.into(), ty, Tag::default());
        self.args.push((arg, var, input));
        Ok(())
    }

    /// Create a new variable _scoped to the injected code_.
    /// **Be sure to `set_data` before an eval.**
    /// This is useful for creating variables that will be manually set, such as in `grp-by` and
    /// `sort-by`.
    pub fn new_var<N: Into<Str>>(&mut self, name: N, ty: Type) -> Variable {
        self.data.locals.add(name.into(), ty, Tag::default())
    }

    pub fn compile(self, in_ty: Type, defs: &Definitions) -> Result<CodeInjector<Eval>> {
        let CodeInjector {
            data: Build { expr, locals },
            args,
        } = self;

        let FullCompilation {
            eval_stack: stack,
            env,
        } = comp::compile_with_seed_vars(expr, defs, in_ty, locals)?;

        Ok(CodeInjector {
            args,
            data: Eval { stack, env },
        })
    }
}

impl CodeInjector<Eval> {
    pub fn out_ty(&self) -> &Type {
        self.data.stack.out_ty()
    }

    /// The injected code's local environment.
    ///
    /// **This is the environment that should be passed through to the eval calls**.
    pub fn env(&self) -> &Environment {
        &self.data.env
    }

    /// Evaluate the injected code.
    /// **Note that the `cx`'s env is not used, instead the local environment is used.
    ///
    /// > If variables are needing to be set, they should be set in a clone of the local
    /// environment and passed to `eval_with_env`. This is generally more performant when
    /// _multiple_ variables are being set in an eval, such as in `grp-by` or `sort-by`.
    pub fn eval(&self, input: Value, cx: &Context) -> Result<Value> {
        // build a local environment on each invocation
        let env = self.env().clone();
        self.eval_with_env(input, cx, env)
    }

    /// Use the supplied environment.
    pub fn eval_with_env(&self, input: Value, cx: &Context, mut env: Environment) -> Result<Value> {
        let CodeInjector {
            args,
            data: Eval { stack, env: _ },
        } = self;

        // evalulate any mapped args and set the variable
        // NOTE: this uses the outer_cx since it needs the caller's env
        for (arg, var, input2) in args {
            let v = arg.resolve(|| input2.as_ref().unwrap_or(&input).clone(), &cx)?;
            var.set_data(&mut env, v);
        }

        // evalulate the injected code
        stack
            .eval(
                input,
                Context {
                    env,
                    root: cx.root,
                    wd: cx.wd,
                },
            )
            .map(|x| x.0)
    }
}
