//! Language characteristics.

pub(crate) mod defs;
pub(crate) mod help;
pub(crate) mod impls;
pub(crate) mod syntax;
pub(crate) mod types;

// Public API

pub use defs::{process_definition, recognise_definition, Definitions};
pub use syntax::{ast, parse};
pub use types::Value;
