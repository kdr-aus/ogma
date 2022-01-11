//! Table expression system.
#![warn(missing_docs)]

pub mod common;
pub mod eng;
pub mod lang;
pub mod output;
pub mod rt;
#[cfg(test)]
mod tests;

pub use common::err::Error;

type HashMap<K, V> = libs::fxhash::FxHashMap<K, V>;
type HashSet<T> = libs::fxhash::FxHashSet<T>;
type Result<T> = std::result::Result<T, Error>;
type Mutex<T> = libs::parking_lot::Mutex<T>;

mod prelude {
    pub(crate) use super::common::{
        self,
        err::{self, Error},
    };
    pub(crate) use super::eng;
    pub(crate) use super::lang::{
        self,
        defs::Definitions,
        impls::{Implementation, Implementations},
        syntax::ast::{self, Tag},
        types::{self, AsType, OgmaData, Table, TableRow, Tuple, Type, Types, Value},
        var::{self, Local, Variable},
    };
    pub(crate) use super::output::{self, print};
    pub(crate) use super::rt;
    pub(crate) use super::{HashMap, HashSet, Result};

    pub(crate) use ::libs::divvy::Str;
    pub(crate) use ::table::Entry;
    pub(crate) use std::sync::Arc;
}
