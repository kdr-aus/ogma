use super::*;
use ::libs::divvy::Str;
use graphs::ArgNode;
use std::sync::Arc;

// ###### VARIABLE #############################################################
#[derive(Debug, Clone)]
pub enum Local {
    Var(Variable),
    Ptr { to: ArgNode, tag: Tag },
}

/// A location in memory.
#[derive(Debug, Clone)]
pub struct Variable {
    /// The tag.
    pub tag: Tag,
    ty: Type,
    env_idx: usize,
}

#[derive(Debug, Clone)]
pub struct Environment(Arc<[Value]>);

impl Environment {
    pub fn new(lg: &graphs::locals_graph::LocalsGraph) -> Self {
        Environment(vec![Value::Nil; lg.var_count()].into())
    }

    fn make_mut(&mut self) -> &mut [Value] {
        let arc: &mut Arc<_> = &mut self.0;

        // we can't just use get_mut since using `return` seems to not work with lifetimes
        // instead, we check the counts outselves.
        // we use the assumption that counts of one would be unique along this thread, and since
        // there cannot be another Arc on another thread without having counts > 1, this arc is
        // unique

        let uniq = Arc::weak_count(arc) == 1 && Arc::strong_count(arc) == 1;

        if !uniq {
            // replace the arc with a new clone
            // NOTE: we use the FromIterator implementation on Arc since it would make one less
            // allocation
            *arc = arc.as_ref().iter().cloned().collect();
        }

        Arc::get_mut(arc).expect("checked one count, or just replaced with clone")
    }
}

/// Module scoped constructor.
impl Variable {
    pub(super) fn new(tag: Tag, ty: Type, env_idx: usize) -> Self {
        Self { tag, ty, env_idx }
    }
}

impl Variable {
    /// The variables type.
    pub fn ty(&self) -> &Type {
        &self.ty
    }

    /// The index into the environment.
    pub fn idx(&self) -> usize {
        self.env_idx
    }

    /// Fetch the value found in the memory location, in the environment.
    pub fn fetch<'a>(&self, env: &'a Environment) -> &'a Value {
        debug_assert!(
            !self.is_noop(),
            "tried fetching a value from a NOOP variable"
        );

        let val = env
            .0
            .get(self.env_idx)
            .expect("environment should have variable at location");

        debug_assert!(
            self.ty == val.ty(),
            "trying to get a variable with type `{}` but the variable is of type `{}`. possibly it has not been set yet?",
            val.ty(),
            self.ty,
        );

        val
    }

    /// Populate the location in memory (within the `env`ironment) with `val`ue.
    pub fn set_data(&self, env: &mut Environment, val: Value) {
        debug_assert!(
            self.ty == val.ty(),
            "trying to set a variable with type `{}` but the variable is of type `{}`",
            val.ty(),
            self.ty
        );

        if self.is_noop() {
            return;
        }

        *env.make_mut()
            .get_mut(self.env_idx)
            .expect("environment should have variable at location") = val;
    }

    /// Create a no op variable.
    ///
    /// This variable is usually used when there is a variable being create but it is _unable_ to
    /// be consumed, usually because it will be used in a literal.
    ///
    /// # Panics
    /// Using a noop can cause runtime panics if trying to fetch from the variable.
    pub fn noop(tag: Tag, ty: Type) -> Self {
        Self {
            tag,
            ty,
            env_idx: usize::MAX,
        }
    }

    fn is_noop(&self) -> bool {
        self.env_idx == usize::MAX
    }
}

// ###### SEED VARS ############################################################
#[derive(Default, Debug)]
pub struct SeedVars(Vec<(Str, Variable)>);

impl SeedVars {
    pub fn add(&mut self, name: Str, ty: Type, tag: Tag) -> Variable {
        let env_idx = self.0.len();
        let var = Variable { tag, ty, env_idx };
        self.0.push((name, var.clone()));

        var
    }

    pub fn drain(self) -> impl ExactSizeIterator<Item = (Str, Variable)> {
        self.0.into_iter()
    }
}
