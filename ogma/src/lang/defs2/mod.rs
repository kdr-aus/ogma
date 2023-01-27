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

pub const ROOT: BoundaryNode = BoundaryNode(0);

pub struct Definitions {
    partitions: Partitions,
    impls: HashMap<ImplNode, (Option<Type>, Implementation)>,
    types: HashMap<TypeNode, Type>,
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
    type Meta: ?Sized;

    /// There needs to be a common key which is used.
    fn key(&self) -> &str;

    /// Retrieve the meta data.
    fn meta(&self) -> &Self::Meta;

    /// Wrap a successful get.
    fn success(r: R) -> Self::Output;

    /// On unsuccessful get, if a `&Tag` can be provided, an `Error`
    /// can be built. Since the `Error` is contextual from the function,
    /// a closure is supplied as the builder.
    /// The implementor decides whether to invoke the function or not.
    fn fail<E>(&self, e: E) -> Self::Output
    where
        E: FnOnce(&Tag) -> Error;
}

/// Consistent access API of definition items.
pub trait DefItems<Key> {
    type Item;
    type Iter: Iterator;

    /// Contains the item under key.
    ///
    /// If `within` is not known, the search can be conducted from the root node using [`ROOT`].
    fn contains<N: Into<Id>>(&self, key: &str, within: N) -> bool;

    /// Get the item under key.
    ///
    /// If `within` is not known, the search can be conducted from the root node using [`ROOT`].
    fn get<'a, K, N: Into<Id>>(&'a self, key: &K, within: N) -> K::Output
    where
        K: PolyGet<&'a Self::Item, Meta = Key>,
        K: ?Sized;

    /// Get the item's help under key.
    fn help<K>(&self, key: &K) -> K::Output
    where
        K: PolyGet<Error>;

    /// Return an iterator over all the items.
    fn iter(&self) -> Self::Iter;
}

pub struct Impls<'a>(&'a Definitions);

pub struct Types<'a>(&'a Definitions);

impl<'a> DefItems<Type> for Impls<'a> {
    type Item = Implementation;
    type Iter = ImplsIter;

    fn contains<N: Into<Id>>(&self, key: &str, within: N) -> bool {
        let (bnd, imports) = self.0.partitions.bnd_and_imports(within);
        self.0
            .partitions
            .find_impls(bnd, imports, key)
            .any(|_| true)
    }

    fn get<'b, K, N: Into<Id>>(&'b self, key: &K, within: N) -> K::Output
    where
        K: PolyGet<&'b Self::Item, Meta = Type>,
        K: ?Sized,
    {
        let (bnd, imports) = self.0.partitions.bnd_and_imports(within);

        let mut ambig = None;
        let mut found = None;
        let chk_ty = key.meta();
        let key_ = key.key();
        for n in self.0.partitions.find_impls(bnd, imports, key_) {
            let (ty, impl_) = self
                .0
                .impls
                .get(&n)
                .expect("implementation should be defined in map");
            match ty {
                Some(ty) if ty == chk_ty => match found {
                    Some(_) => {
                        return key.fail(|tag| {
                            Error {
                cat: err::Category::Definitions,
                desc: "ambiguous operation reference".to_string(),
                traces: err::trace(tag, format!("{tag} references multiple definitions")),
                help_msg: "check your imports for ambiguity\nconsider using fully qualified path syntax".to_string().into(),
                hard: true,
                    }
                        })
                    }
                    None => found = Some(impl_),
                },
                Some(_) => (), // skip, type doesn't match
                None => match ambig {
                    Some(_) => {
                        return key.fail(|tag| {
                            Error {
                cat: err::Category::Definitions,
                desc: "ambiguous operation reference".to_string(),
                traces: err::trace(tag, format!("{tag} references multiple definitions")),
                help_msg: "check your imports for ambiguity\nconsider using fully qualified path syntax".to_string().into(),
                hard: true,
                    }
                        });
                    }
                    None => ambig = Some(impl_),
                },
            }
        }

        match (found, ambig) {
            (Some(x), _) | (None, Some(x)) => K::success(x),
            (None, None) => key.fail(|tag| Error::impl_not_found(tag, chk_ty)),
        }
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

impl<'a> DefItems<()> for Types<'a> {
    type Item = Type;
    type Iter = TypesIter;

    fn contains<N: Into<Id>>(&self, key: &str, within: N) -> bool {
        let (bnd, imports) = self.0.partitions.bnd_and_imports(within);
        self.0
            .partitions
            .find_types(bnd, imports, key)
            .any(|_| true)
    }

    fn get<'b, K, N: Into<Id>>(&'b self, key: &K, within: N) -> K::Output
    where
        K: PolyGet<&'b Self::Item>,
        K: ?Sized,
    {
        let (bnd, imports) = self.0.partitions.bnd_and_imports(within);

        let mut x = self.0.partitions.find_types(bnd, imports, key.key());
        let y = x.next();

        if x.next().is_some() {
            return key.fail(|tag| Error {
                cat: err::Category::Definitions,
                desc: "ambiguous type reference".to_string(),
                traces: err::trace(tag, format!("{tag} references multiple definitions")),
                help_msg:
                    "check your imports for ambiguity\nconsider using fully qualified path syntax"
                        .to_string()
                        .into(),
                hard: true,
            });
        }

        match y {
            Some(x) => K::success(
                self.0
                    .types
                    .get(&x)
                    .expect("Type should be initialised within map"),
            ),
            None => key.fail(Error::type_not_found),
        }
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

impl<T> PolyGet<T> for str {
    type Output = Option<T>;
    type Meta = ();

    fn key(&self) -> &str {
        self
    }

    fn meta(&self) -> &Self::Meta {
        &()
    }

    fn success(r: T) -> Self::Output {
        Some(r)
    }

    fn fail<E>(&self, _e: E) -> Self::Output
    where
        E: FnOnce(&Tag) -> Error,
    {
        None
    }
}

impl<T> PolyGet<T> for Tag {
    type Output = Result<T>;
    type Meta = ();

    fn key(&self) -> &str {
        self.str()
    }

    fn meta(&self) -> &Self::Meta {
        &()
    }

    fn success(r: T) -> Self::Output {
        Ok(r)
    }

    fn fail<E>(&self, e: E) -> Self::Output
    where
        E: FnOnce(&Tag) -> Error,
    {
        Err(e(self))
    }
}

impl<T> PolyGet<T> for (&str, &Type) {
    type Output = Option<T>;
    type Meta = Type;

    fn key(&self) -> &str {
        self.0
    }

    fn meta(&self) -> &Self::Meta {
        self.1
    }

    fn success(r: T) -> Self::Output {
        Some(r)
    }

    fn fail<E>(&self, _e: E) -> Self::Output
    where
        E: FnOnce(&Tag) -> Error,
    {
        None
    }
}

impl<T> PolyGet<T> for (&Tag, &Type) {
    type Output = Result<T>;
    type Meta = Type;

    fn key(&self) -> &str {
        self.0.str()
    }

    fn meta(&self) -> &Self::Meta {
        self.1
    }

    fn success(r: T) -> Self::Output {
        Ok(r)
    }

    fn fail<E>(&self, e: E) -> Self::Output
    where
        E: FnOnce(&Tag) -> Error,
    {
        Err(e(self.0))
    }
}
