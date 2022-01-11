//! Table expression system.
#![warn(missing_docs)]

mod common;
#[cfg(test)]
mod tests;
mod lang;
mod eng;
pub mod rt;
mod output;

type HashMap<K, V> = libs::fxhash::FxHashMap<K, V>;
type HashSet<T> = libs::fxhash::FxHashSet<T>;
type Result<T> = std::result::Result<T, common::err::Error>;
type Mutex<T> = libs::parking_lot::Mutex<T>;

mod prelude {
    pub(crate) use super::{HashMap, HashSet, Result};
    pub(crate) use super::lang::{
        self,
        syntax::ast::{self, Tag},
        defs::{Definitions},
        impls::{Implementations, Implementation},
        types::{self, TableRow, Table, OgmaData, AsType, Value, Type, Tuple, Types},
        var::{self, Variable, Local},
    };
    pub(crate) use super::common::err::{self, Error};
    pub(crate) use super::output::print;
    pub(crate) use super::eng;
    pub(crate) use super::rt;

    pub(crate) use ::table::Entry;
    pub(crate) use ::libs::divvy::Str;
    pub(crate) use std::sync::Arc;
}
