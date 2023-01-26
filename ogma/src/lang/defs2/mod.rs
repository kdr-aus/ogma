//! This handles definitions (fns, structs, enums)
use crate::prelude::*;
use ast::Location;
use lang::parse::File;
use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
};

mod partitions;
#[cfg(test)]
mod tests;

use partitions::*;

pub struct Definitions {
    partitions: Partitions,
    impls: HashMap<ImplNode, ()>,
    types: HashMap<TypeNode, ()>,
}

impl Definitions {
    pub fn new() -> Self {
        Self {
            partitions: Partitions::new(),
            impls: HashMap::default(),
            types: HashMap::default(),
        }
    }

    pub fn impls(&self) -> Impls {
        Impls(self)
    }

    pub fn types(&self) -> Types {
        Types(self)
    }
}

type FsMap = BTreeMap<PathBuf, Vec<File>>;

fn build_fs_map(root: &Path) -> Result<FsMap> {
    fn ioerr(e: std::io::Error) -> Error {
        Error {
            cat: err::Category::Parsing,
            desc: format!("IO error: {e}"),
            ..Default::default()
        }
    }

    let mut map1 = FsMap::default();
    let mut dirs = Vec::new();

    // do adjacent .ogma files first
    for e in root.read_dir().map_err(ioerr)? {
        let e = e.map_err(ioerr)?;
        let path = e.path();
        if path.extension().map(|e| e == "ogma").unwrap_or_default() && path.is_file() {
            let pt = path
                .strip_prefix(root)
                .expect("to be prefixed with root")
                .with_extension("");
            let file = parse_file(path.clone())?;
            assert!(map1.insert(pt, vec![file]).is_none());
        } else if path.is_dir() {
            dirs.push(path);
        }
    }

    // do the directories and subdirs
    while let Some(dir) = dirs.pop() {
        let pt = dir
            .strip_prefix(root)
            .expect("to be prefixed with root")
            .to_path_buf();
        if map1.contains_key(&pt) {
            return Err(Error {
                cat: err::Category::Parsing,
                desc: format!(
                    "the partition '{}' is defined adjacent and as a directory",
                    pt.display()
                ),
                ..Default::default()
            });
        }

        let mut v = Vec::new();
        for e in dir.read_dir().map_err(ioerr)? {
            let e = e.map_err(ioerr)?;
            let path = e.path();
            if path.extension().map(|e| e == "ogma").unwrap_or_default() && path.is_file() {
                v.push(parse_file(path)?);
            } else if path.is_dir() {
                dirs.push(path);
            }
        }

        if !v.is_empty() {
            assert!(map1.insert(pt, v).is_none());
        }
    }

    Ok(map1)
}

fn parse_file(file: PathBuf) -> Result<File> {
    let s = std::fs::read_to_string(&file).map_err(|e| Error {
        cat: err::Category::Parsing,
        desc: format!("failed to read '{}' as string: {e}", file.display()),
        hard: true,
        ..Default::default()
    })?;
    let loc = Location::File(file.into(), 0);
    lang::parse::file(&s, loc)
}

/// A trait for polymorphic fallible return values when getting from a data structure.
///
/// The trait is intended to be used where a result return is only able to be made when the key has
/// enough information to build an `Error`.
///
/// For now, the trait is concrete in a few types since it is designed for use with the
/// [`Definitions`].
///
/// The `R` specifies the wrapped success value.
///
/// A blanket implementation would look for all `R` is advised.
pub trait PolyGet<R> {
    /// The output type (ie `Option<R>` or `Result<R, Error>`).
    type Output;

    /// There needs to be a common key which is used.
    fn key(&self) -> &str;

    /// Wrap a successful get.
    fn success(r: R) -> Self::Output;

    /// On unsuccessful get, if a `&Tag` can be provided, an `Error`
    /// can be built. Since the `Error` is contextual from the function,
    /// a closure is supplied as the builder.
    /// The implementor decides whether to invoke the function or not.
    fn fail<E>(e: E) -> Self::Output
    where
        E: FnOnce(&Tag) -> Error;
}

/// Consistent access API of definition items.
pub trait DefItems {
    type Item;
    type Iter: Iterator;

    /// Contains the item under key.
    fn contains(&self, key: &str) -> bool;

    /// Get the item under key.
    fn get<'a, K>(&'a self, key: &K) -> K::Output
    where
        K: PolyGet<&'a Self::Item>;

    /// Get the item's help under key.
    fn help<K>(&self, key: &K) -> K::Output
    where
        K: PolyGet<Error>;

    /// Return an iterator over all the items.
    fn iter(&self) -> Self::Iter;
}

pub struct Impls<'a>(&'a Definitions);

pub struct Types<'a>(&'a Definitions);

impl<'a> DefItems for Impls<'a> {
    type Item = Implementation;
    type Iter = ImplsIter;

    fn contains(&self, key: &str) -> bool {
        todo!()
    }

    fn get<'b, K>(&'b self, key: &K) -> K::Output
    where
        K: PolyGet<&'b Self::Item>,
    {
        todo!()
    }

    fn help<K>(&self, key: &K) -> K::Output
    where
        K: PolyGet<Error>,
    {
        todo!()
    }

    fn iter(&self) -> Self::Iter {
        todo!()
    }
}

impl<'a> DefItems for Types<'a> {
    type Item = Type;
    type Iter = TypesIter;

    fn contains(&self, key: &str) -> bool {
        todo!()
    }

    fn get<'b, K>(&'b self, key: &K) -> K::Output
    where
        K: PolyGet<&'b Self::Item>,
    {
        todo!()
    }

    fn help<K>(&self, key: &K) -> K::Output
    where
        K: PolyGet<Error>,
    {
        todo!()
    }

    fn iter(&self) -> Self::Iter {
        todo!()
    }
}

pub struct ImplsIter {}

pub struct TypesIter {}

impl Iterator for ImplsIter {
    type Item = ();

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl Iterator for TypesIter {
    type Item = ();

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}
