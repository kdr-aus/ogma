use super::{
    ast::{Argument, Tag},
    types::{Type, Value},
    HashMap,
};
use ::libs::divvy::Str;
use std::{cell::*, rc::Rc, sync::Arc};

// ###### VARIABLE #############################################################
#[derive(Debug, Clone)]
pub struct Variable {
    pub tag: Tag,
    ty: Type,
    env_idx: usize,
}

#[derive(Debug, Clone)]
pub enum Local {
    Param(Argument, Locals),
    Var(Variable),
}

#[derive(Clone)]
#[allow(clippy::rc_buffer)]
pub struct Environment(Arc<Vec<Value>>);

impl Environment {
    pub fn new(locals: Locals) -> Self {
        Environment(Arc::new(vec![Value::Nil; locals.count.get()]))
    }
}

impl Variable {
    pub fn ty(&self) -> &Type {
        &self.ty
    }

    pub fn fetch<'a>(&self, env: &'a Environment) -> &'a Value {
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

    pub fn set_data(&self, env: &mut Environment, val: Value) {
        debug_assert!(
            self.ty == val.ty(),
            "trying to set a variable with type `{}` but the variable is of type `{}`",
            val.ty(),
            self.ty
        );

        *Arc::make_mut(&mut env.0)
            .get_mut(self.env_idx)
            .expect("environment should have variable at location") = val;
    }
}

// ###### LOCALS ###############################################################
#[allow(dead_code)]
#[derive(Debug)]
struct LocalEntry {
    defined_depth: u32,
    local: Local,
}

#[derive(Debug, Default)]
pub struct Locals {
    vars: Rc<HashMap<Str, Local>>,
    count: Rc<Cell<usize>>,
}

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

    /// Get the deepest local matching the name and optional depth. If no depth is specified, will
    /// get the deepest.
    pub fn get(&self, name: &str) -> Option<&Local> {
        self.vars.get(name)
    }

    /// Add an already existent variable aliased under the given name in the local environment.
    pub fn add_var(&mut self, name: Str, var: Variable) {
        let vars = Rc::make_mut(&mut self.vars);
        vars.insert(name, Local::Var(var));
    }

    /// Add a parameter with the given name in the local environment.
    /// Capture a locals environment that is associated with this parameter, usually the caller's
    /// environment.
    pub fn add_param(&mut self, name: Str, arg: Argument, locals: Locals) {
        let vars = Rc::make_mut(&mut self.vars);
        vars.insert(name, Local::Param(arg, locals));
    }

    /// Add a **new** variable (a new memory location) into the environment.
    pub fn add_new_var(&mut self, name: Str, ty: Type, tag: Tag) -> Variable {
        // increment place location
        let var = Variable {
            tag,
            ty,
            env_idx: self.count.get(),
        };
        self.count.set(var.env_idx + 1);
        self.add_var(name, var.clone());
        var
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
