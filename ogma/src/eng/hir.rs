use super::*;
use crate::lang::var::{Environment, Locals};
use crate::prelude::*;
use ast::{DefinitionImpl, Expression, Tag, Term};
use std::{convert::TryInto, fmt};

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
}

// ###### STEP #################################################################

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
