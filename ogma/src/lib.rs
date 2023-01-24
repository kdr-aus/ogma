//! Table expression system.
#![warn(missing_docs)]

#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

pub mod common;
pub mod eng;
pub mod lang;
pub mod output;
pub mod rt;

pub use common::err::Error;

type HashMap<K, V> = libs::rustc_hash::FxHashMap<K, V>;
type HashSet<T> = libs::rustc_hash::FxHashSet<T>;
type Result<T> = std::result::Result<T, Error>;
type Mutex<T> = libs::parking_lot::Mutex<T>;

mod prelude {
    pub(crate) use super::common::err::{self, Error};
    pub(crate) use super::eng;
    pub(crate) use super::lang::{
        self,
        defs::Definitions,
        impls::{Implementation, Implementations},
        syntax::ast::{self, Tag},
        types::{self, AsType, OgmaData, Table, TableRow, Tuple, Type, Value},
    };
    pub(crate) use super::output::print;
    pub(crate) use super::rt;
    pub(crate) use super::{HashMap, HashSet, Result};

    pub(crate) use ::libs::divvy::Str;
    pub(crate) use ::table::Entry;
    pub(crate) use std::sync::Arc;

    /// Use `format_args!` as parameter.
    #[cfg(debug_assertions)]
    pub(crate) fn _counts_line(args: std::fmt::Arguments) {
        use std::io::Write;

        let mut file = std::fs::File::options()
            .create(true)
            .append(true)
            .open("./counts.entries")
            .unwrap();
        writeln!(&mut file, "{}", args).unwrap();
    }
}
