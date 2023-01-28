//! Language characteristics.

pub(crate) mod defs;
#[allow(dead_code)] // TODO remove once changed over
pub(crate) mod defs2;
pub(crate) mod help;
pub(crate) mod impls;
pub(crate) mod syntax;
pub(crate) mod types;

// Public API

pub use defs::{construct_def_table, process_definition, recognise_definition};
pub use defs2::Definitions;
pub use impls::ImplEntry;
pub use syntax::{ast, parse};
pub use types::{AsType, OgmaData, Table, Type, Value};
