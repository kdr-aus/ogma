use super::*;
use ast::Tag;
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
    /// The input [`Type`] of the block.
    pub fn in_ty(&self) -> &Type {
        &self.in_ty
    }

    /// Returns the _number of arguments remaining_.
    pub fn args_len(&self) -> usize {
        self.args.len()
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
        F: Fn(Value, Context) -> StepR,
        F: Func<StepR>,
    {
        self.finalise(&out_ty)?;
        Ok(Step {
            out_ty,
            f: Arc::new(f),
            type_annotation: String::new(),
        })
    }

    /// Preferred way of creating a eval step.
    ///
    /// This supplies the [`Value`] input but uses type inference on `O` to get the output type.
    pub fn eval_o<F, O>(self, f: F) -> Result<Step>
    where
        F: Fn(Value, Context) -> Result<(O, Environment)>,
        F: Func<Result<(O, Environment)>>,
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
