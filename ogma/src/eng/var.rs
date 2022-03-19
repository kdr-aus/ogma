use super::*;
use ::libs::divvy::Str;
use graphs::ArgNode;
use std::{cell::*, rc::Rc, sync::Arc};

// ###### VARIABLE #############################################################
#[derive(Debug, Clone)]
pub enum Local {
    Var(Variable),
    Ptr { to: ArgNode, tag: Tag },
}

// TODO can this be Arc<[Value]>???
#[derive(Debug, Clone)]
#[allow(clippy::rc_buffer)]
pub struct Environment(Arc<Vec<Value>>);

impl Environment {
    pub fn new(lg: &graphs::locals_graph::LocalsGraph) -> Self {
        Environment(Arc::new(vec![Value::Nil; lg.var_count()]))
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

        *Arc::make_mut(&mut env.0)
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

// ###### LOCALS ###############################################################
#[derive(Debug)]
struct LocalEntry {
    // TODO remove this???
    _defined_depth: u32,
    // TODO remove this???
    _local: Local,
}

/// A map of available variables based on an string name.
///
/// Locals is easily shareable and Cow for the variables maps. It also stores a **shared** counter
/// which increments _everytime_ an entry is made into the variable map.
/// This counter, along with the variable storing an index into the environment, makes this system
/// fairly robust.
///
/// Scoping is done by _not_ passing along an altered map. For instance, a block will pass on its
/// locals to the next block, so any changes to the map are available. For an expression, the map
/// is not passed along, instead the changes are local to the expression.
#[derive(Debug, Default)]
pub struct Locals {
    vars: Rc<HashMap<Str, Local>>,
    count: Rc<Cell<usize>>,
}

/// Equality is done by reference.
impl PartialEq for Locals {
    fn eq(&self, o: &Self) -> bool {
        Rc::ptr_eq(&self.vars, &o.vars) && Rc::ptr_eq(&self.count, &o.count)
    }
}
/// Equality is done by reference.
impl Eq for Locals {}

impl Locals {
    /// Enter a new impl environment where it does not have access to the caller scope.
    ///
    /// This is used for impls where it _should not have access to caller scope_. Any _new_ locals
    /// will be forgotten once scope ends.
    pub fn enter_impl(&self) -> Self {
        Self {
            vars: Default::default(),
            count: Rc::clone(&self.count),
        }
    }

    /// Get a local by name.
    pub fn get(&self, name: &str) -> Option<&Local> {
        self.vars.get(name)
    }

    /// Add an already existent variable aliased under the given name in the local environment.
    pub fn add_var(&mut self, name: Str, var: Variable) {
        let vars = Rc::make_mut(&mut self.vars);
        vars.insert(name, Local::Var(var));
    }

    /// Add a parameter mapped to this name.
    pub fn add_param(&mut self, name: Str, arg: Argument) {
        todo!()
        //         let vars = Rc::make_mut(&mut self.vars);
        //         vars.insert(name, Local::Param(arg));
    }

    /// Add a **new** variable (a new memory location) into the environment.
    pub fn add_new_var(&mut self, name: Str, ty: Type, tag: Tag) -> Variable {
        todo!();
        //         // increment place location
        //         let var = Variable {
        //             tag,
        //             ty,
        //             env_idx: self.count.get(),
        //         };
        //         self.count.set(var.env_idx + 1);
        //         self.add_var(name, var.clone());
        //         var
    }
}

impl Clone for Locals {
    fn clone(&self) -> Self {
        Self {
            vars: Rc::clone(&self.vars),
            count: Rc::clone(&self.count),
        }
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
