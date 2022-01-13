use super::*;

/// Evaluator of an expression.
#[derive(Debug)]
pub struct Evaluator {
    tag: Tag,
    /// This is the type that is the output of the previous block, and is the _input_ for the next
    /// block.
    out_ty: Type,
    /// Each block converted into a function.
    steps: Vec<Step>,

    /// A tracked type annotation code representation.
    ///
    /// TODO: This implementation is currently pretty poorly implemented, requiring this to be
    /// tracked at all times. Once type inferencing matures more, this annotation could possibly be
    /// moved into that system.
    type_annotation: String,
}

impl Evaluator {
    fn new(in_ty: Type, tag: Tag, stepslen: usize) -> Evaluator {
        Evaluator {
            tag,
            out_ty: in_ty,
            steps: Vec::with_capacity(stepslen),
            type_annotation: String::default(),
        }
    }

    pub fn construct(
        in_ty: Type,
        expr: ast::Expression,
        defs: &Definitions,
        mut variables: Locals,
    ) -> Result<Evaluator> {
        let type_annotation = String::from("{");

        let mut evaluator = Evaluator::new(in_ty, expr.tag, expr.blocks.len());

        evaluator.type_annotation = type_annotation;

        for block in expr.blocks {
            evaluator.type_annotation.push(':');
            evaluator.type_annotation.push_str(&evaluator.ty().fmt_annotation().to_string());

            let im = defs.impls().get_impl(&block.op(), evaluator.ty())?;
            let mut block = Block::new(evaluator.ty().clone(), defs, &mut variables, block);
            let step = match im {
                Implementation::Intrinsic { f, .. } => f(block),
                Implementation::Definition(def) => {
                    // TODO This seems unnecessary, wrapping an evaluator in a step???
                    DefImplEvaluator::build(&mut block, def).map(|evaluator| {
                        let type_annotation = evaluator.expr_eval.type_annotation.clone();
                        Step {
                        out_ty: evaluator.ty().clone(),
                        f: Box::new(move |input, cx| evaluator.eval(input, cx)),
                        type_annotation: Default::default(),
                    }})
                }
            }?;

            evaluator.type_annotation.push(' ');
            evaluator.type_annotation.push_str(&step.type_annotation);
            evaluator.type_annotation.push_str(" |");

            evaluator.push_step(step);
        }

        evaluator.type_annotation.pop();
        evaluator.type_annotation.push_str("}:");
        evaluator.type_annotation.push_str(&evaluator.ty().fmt_annotation().to_string());

        Ok(evaluator)
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

    /// The steps comprising this evaluator.
    pub fn steps(&self) -> &[Step] {
        &self.steps
    }

    pub fn type_annotation(&self) -> &str {
        &*self.type_annotation
    }

    /// Asserts that the expressions returns the type `ty` once resolved.
    pub fn returns(self, ty: &Type) -> Result<Self> {
        if &self.out_ty == ty {
            Ok(self)
        } else {
            Err(Error::unexp_arg_ty(ty, &self.out_ty, &self.tag))
        }
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

/// This is similar to [`Evaluator`] but has extra handling to greedily evaluate parameters,
/// assigning them to variables.
pub struct DefImplEvaluator {
    /// Parameters to be evaluated _before_ evaluating the expression.
    /// This sets the parameter values.
    params: Vec<ParamEval>,
    /// The evaluator of the definition expression.
    expr_eval: Evaluator,
}

impl DefImplEvaluator {
    /// This is used by the main HIR routine for user defined impls, but it can also be used to inject
    /// an implementation 'on the fly' at the HIR phase from an _intrinsic_ impl.
    /// This is useful to keep HIR routine checking (such as using `eq` and `cmp` which might have user
    /// impls), but should be uesd with care as the [`DefinitionImpl`] must be defined on the fly and
    /// might not have the same checking as going through the regular parsing system.
    pub fn build(blk: &mut Block, def: &ast::DefinitionImpl) -> Result<Self> {
        let defs = blk.defs;
        // calls into users defs should not have visibility of current variables, so we construct
        // a new variables map, where the known variables are the parameters
        let (vars, params) = Self::construct_params(blk, def)?;

        let in_ty = blk.in_ty().clone();
        let expr_eval = Evaluator::construct(in_ty, def.expr.clone(), defs, vars)
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
    fn construct_params(
        blk: &mut Block,
        def: &ast::DefinitionImpl,
    ) -> Result<(Locals, Vec<ParamEval>)> {
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

/// Makes an [`Evaluator`] which just passes then input to the output.
/// The input type is expected to match `in_ty`.
pub fn make_input_pound_expr(in_ty: Type, tag: Tag) -> Evaluator {
    let out_ty = in_ty;
    let tyan = format!("#i:{}", out_ty);
    Evaluator {
        tag,
        out_ty: out_ty.clone(),
        steps: vec![Step {
            out_ty,
            f: Box::new(|i, cx| cx.done(i)),
            type_annotation: tyan.clone(),
        }],
        type_annotation: tyan,
    }
}
