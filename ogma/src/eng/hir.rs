use super::*;
use ast::{Tag, Term};
use std::fmt;

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
impl<'a> Block<'a> {
    fn arg_recursive(&self, arg: ast::Argument, in_ty: Type, locals: &Locals) -> Result<Argument> {
        use ast::Argument as A;
        use eval::make_input_pound_expr;

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
                let eval = Evaluator::construct(in_ty.clone(), expr, self.defs, locals.clone())
                    .map_err(|e| e.add_trace(self.blk_tag()))?;
                let out_ty = eval.ty().clone();
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

    /// The input [`Type`] of the block.
    pub fn in_ty(&self) -> &Type {
        &self.in_ty
    }

    /// Returns the _number of arguments remaining_.
    pub fn args_len(&self) -> usize {
        self.args.len()
    }

    /// Works in the same fashion as [`Block::next_arg`], but **does not remove the argument from
    /// the argument stack**. This should not be used except in edge cases where the argument is
    /// required more than once.
    pub fn next_arg_do_not_remove<I: Into<Option<Type>>>(
        &mut self,
        input_type: I,
    ) -> Result<Argument> {
        todo!()
        //         let arg = self.next_arg_raw()?;
        //         self.args.push(arg.clone());
        //         self.args_count = self.args_count.saturating_sub(1);
        //         self.arg_recursive(
        //             arg,
        //             input_type.into().unwrap_or_else(|| self.in_ty().clone()),
        //             self.vars,
        //         )
    }

    /// Gets the flag that matches a given name.
    ///
    /// If no name is given with `None`, _the first flag first is returned, if there is one._
    ///
    /// > The flag is **removed** from the flag stack.
    pub fn get_flag<'b, N: Into<Option<&'b str>>>(&mut self, flag: N) -> Option<Tag> {
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
        todo!()
        //         match self.next_arg_raw()? {
        //             ast::Argument::Var(var) => Ok(self.vars.add_new_var(Str::new(var.str()), ty, var)),
        //             x => {
        //                 let (x, y) = Error::span_arg(&x);
        //                 Err(Error::unexp_arg_variant(x, y))
        //             }
        //         }
    }

    /// Create a variable reference not off a specific argument, but by manually specifying the
    /// variable name.
    ///
    /// This is useful for expressions that need to supply more than just the input. For instance
    /// the `fold` command will supply the `$row` variable which is a track of the TableRow
    ///
    /// The tag is usually `blk.op_tag`.
    pub fn create_var_manually<N: Into<Str>>(&mut self, name: N, ty: Type, tag: Tag) -> Variable {
        todo!()
        //         self.vars.add_new_var(name.into(), ty, tag)
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
        self.finalise(&out_ty)?;
        Ok(Step {
            out_ty,
            f: Box::new(f),
            type_annotation: String::new(),
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
}

// ###### STEP #################################################################

impl Step {
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

impl fmt::Debug for Step {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Step")
            .field("out_ty", &self.out_ty)
            .finish()
    }
}

// ###### TESTS ################################################################
#[cfg(test)]
mod tests {
    use super::*;
    use ast::Location;
    use lang::syntax::parse::expression;

    #[test]
    fn no_cmd_defined() {
        let src = "undefined";
        let defs = &Definitions::new();
        let vars = Locals::default();
        let x = Evaluator::construct(
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
        let x = Evaluator::construct(
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
        let x = Evaluator::construct(
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
