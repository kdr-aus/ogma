//! Language characteristics.

pub(crate) mod defs;
pub(crate) mod help;
pub(crate) mod impls;
pub(crate) mod syntax;
pub(crate) mod types;

// Public API

pub use defs::{construct_def_table, process_definition, recognise_definition, Definitions};
pub use syntax::{ast, parse};
pub use types::{AsType, OgmaData, Table, Type, Value};
