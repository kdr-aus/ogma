//! Output handling, primarily about printing to terminal.

pub(crate) mod print;

// Public API

pub use print::{print_error, print_ogma_data, print_table};
