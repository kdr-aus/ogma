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

pub trait AsKey<K> {
    fn as_key(&self) -> K;
}

/// Consistent access API of definition items.
pub trait DefItems<'a, Key: 'a> {
    type Item;
    type Iter: Iterator;

    /// Contains the item under key.
    fn contains<K>(&self, key: K) -> bool
    where
        K: AsKey<Key>;

    /// Get the item under key.
    fn get<K>(&self, key: K) -> K::Output
    where
        K: PolyGet<Self::Item> + AsKey<Key>;

    /// Get the item's help under key.
    fn help<K>(&self, key: K) -> K::Output
    where
        K: PolyGet<Error> + AsKey<Key>;

    /// Return an iterator over all the items.
    fn iter(&self) -> Self::Iter;
}

pub struct Impls<'a>(&'a Definitions);

pub struct Types<'a>(&'a Definitions);

impl<'a> Impls<'a> {
    pub fn within<N: Into<Id>>(self, partition: N) -> ImplsIn<'a> {
        ImplsIn {
            impls: self,
            partition: partition.into(),
        }
    }

    /// Does not check for type matching, see [`contains`] instead.
    pub fn contains_op(&self, key: &str, within: Id) -> bool {
        let (bnd, imports) = self.0.partitions.bnd_and_imports(within);
        self.0
            .partitions
            .find_impls(bnd, imports, key)
            .any(|_| true)
    }

    fn contains_(&self, key: &str, ty: &Type, within: Id) -> bool {
        let (bnd, imports) = self.0.partitions.bnd_and_imports(within);
        self.0
            .partitions
            .find_impls(bnd, imports, key)
            .any(|x| self.0.impls[&x].0.as_ref() == Some(ty))
    }

    fn get_<K>(&self, key: &str, ty: &Type, within: Id, k_: K) -> K::Output
    where
        K: PolyGet<&'a Implementation>
    {
        let (bnd, imports) = self.0.partitions.bnd_and_imports(within);

        let chk_ty = ty;
        let mut ambig = None;
        let mut found = None;
        for n in self.0.partitions.find_impls(bnd, imports, key) {
            let (ty, impl_) = self
                .0
                .impls
                .get(&n)
                .expect("implementation should be defined in map");
            match ty {
                Some(ty) if ty == chk_ty => match found {
                    Some(_) => {
                        return k_.fail(|tag| {
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
                        return k_.fail(|tag| {
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
            (None, None) => k_.fail(|tag| Error::impl_not_found(tag, chk_ty)),
        }
    }
}

impl<'a> Types<'a> {
    pub fn within<N: Into<Id>>(self, partition: N) -> TypesIn<'a> {
        TypesIn {
            types: self,
            partition: partition.into(),
        }
    }

    fn contains_(&self, key: &str, within: Id) -> bool {
        let (bnd, imports) = self.0.partitions.bnd_and_imports(within);
        self.0
            .partitions
            .find_types(bnd, imports, key)
            .any(|_| true)
    }

    fn get_<S, F, O>(&self, key: &str, within: Id, succeed: S, fail: F) -> O
    where
        F: FnOnce(fn(&Tag) -> Error) -> O,
        S: FnOnce(&'a Type) -> O,
    {
        let (bnd, imports) = self.0.partitions.bnd_and_imports(within);

        let mut x = self.0.partitions.find_types(bnd, imports, key);
        let y = x.next();

        if x.next().is_some() {
            return fail(|tag| Error {
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
            Some(x) => succeed(
                self.0
                    .types
                    .get(&x)
                    .expect("Type should be initialised within map"),
            ),
            None => fail(Error::type_not_found),
        }
    }
}

impl<'a, 'd> DefItems<'a, (&'a str, &'a Type, Id)> for Impls<'d> {
    type Item = &'d Implementation;
    type Iter = ImplsIter;

    fn contains<K>(&self, key: K) -> bool
    where
        K: AsKey<(&'a str, &'a Type, Id)>,
    {
        let (k, t, w) = key.as_key();
        self.contains_(k, t, w)
    }

    fn get<K>(&self, key: K) -> K::Output
    where
        K: PolyGet<Self::Item>,
        K: AsKey<(&'a str, &'a Type, Id)>,
    {
        let (key_, chk_ty, within) = key.as_key();
        self.get_(key_, chk_ty, within, key)
    }

    fn help<K>(&self, _key: K) -> K::Output
    where
        K: PolyGet<Error> + AsKey<(&'a str, &'a Type, Id)>,
    {
        todo!()
    }

    fn iter(&self) -> Self::Iter {
        todo!()
    }
}

impl<'a, 'd> DefItems<'a, (&'a str, Id)> for Types<'d> {
    type Item = &'d Type;
    type Iter = TypesIter;

    fn contains<K>(&self, key: K) -> bool
    where
        K: AsKey<(&'a str, Id)>,
    {
        let (k, w) = key.as_key();
        self.contains_(k, w)
    }

    fn get<K>(&self, key: K) -> K::Output
    where
        K: PolyGet<Self::Item>,
        K: AsKey<(&'a str, Id)>,
    {
        let (key_, within) = key.as_key();
        self.get_(key_, within, K::success, |f| key.fail(f))
    }

    fn help<K>(&self, _key: K) -> K::Output
    where
        K: PolyGet<Error> + AsKey<(&'a str, Id)>,
    {
        todo!()
    }

    fn iter(&self) -> Self::Iter {
        todo!()
    }
}

pub struct ImplsIn<'a> {
    pub impls: Impls<'a>,
    pub partition: Id,
}

pub struct TypesIn<'a> {
    pub types: Types<'a>,
    pub partition: Id,
}

impl<'a, 'd> DefItems<'a, (&'a str, &'a Type)> for ImplsIn<'d> {
    type Item = &'d Implementation;
    type Iter = ImplsIter;

    fn contains<K>(&self, key: K) -> bool
    where
        K: AsKey<(&'a str, &'a Type)>,
    {
        let (k, t) = key.as_key();
        self.impls.contains_(k, t, self.partition)
    }

    fn get<K>(&self, key: K) -> K::Output
    where
        K: PolyGet<Self::Item>,
        K: AsKey<(&'a str, &'a Type)>,
    {
        let (key_, ty) = key.as_key();
        self.impls
            .get_(key_, ty, self.partition, key)
    }

    fn help<K>(&self, _key: K) -> K::Output
    where
        K: PolyGet<Error> + AsKey<(&'a str, &'a Type)>,
    {
        todo!()
    }

    fn iter(&self) -> Self::Iter {
        todo!()
    }
}

impl<'a, 'd> DefItems<'a, &'a str> for TypesIn<'d> {
    type Item = &'d Type;
    type Iter = TypesIter;

    fn contains<K>(&self, key: K) -> bool
    where
        K: AsKey<&'a str>,
    {
        self.types.contains_(key.as_key(), self.partition)
    }

    fn get<K>(&self, key: K) -> K::Output
    where
        K: PolyGet<Self::Item>,
        K: AsKey<&'a str>,
    {
        self.types
            .get_(key.as_key(), self.partition, K::success, |f| key.fail(f))
    }

    fn help<K>(&self, _key: K) -> K::Output
    where
        K: PolyGet<Error> + AsKey<&'a str>,
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

macro_rules! key_impl {
    ($($k:ty => $v:ident),*) => {
        trait __GetTag {
            fn __get_tag(&self) -> &Tag;
        }
        impl __GetTag for &Tag {
            fn __get_tag(&self) -> &Tag { self }
        }
        impl<B> __GetTag for (&Tag, B) {
            fn __get_tag(&self) -> &Tag { self.0 }
        }
        impl<B, C> __GetTag for (&Tag, B, C) {
            fn __get_tag(&self) -> &Tag { self.0 }
        }

        $(
        key_impl!($v, $k, Id);
        key_impl!($v, $k, BoundaryNode);
        key_impl!($v, $k, TypeNode);
        key_impl!($v, $k, ImplNode);

        // polyget without id
        key_impl!($v &$k);
        key_impl!($v (&$k, &Type));
        key_impl!(@askey 1, $k);
        )*
    };
    ($v:ident, $k:ty, $id:ty) => {
        // polyget with id
        key_impl!($v (&$k, $id));
        key_impl!($v (&$k, &Type, $id));
        key_impl!(@askey 2, $k, $id);
    };
    (opt $t:ty) => {
        impl<T> PolyGet<T> for $t {
            type Output = Option<T>;

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
    };
    (res $t:ty) => {
        impl<T> PolyGet<T> for $t {
            type Output = Result<T>;

            fn success(r: T) -> Self::Output {
                Ok(r)
            }

            fn fail<E>(&self, e: E) -> Self::Output
            where
                E: FnOnce(&Tag) -> Error,
            {
                Err(e(__GetTag::__get_tag(self)))
            }
        }
    };
    (@askey 1, $k:ty) => {
        impl<'a> AsKey<&'a str> for &'a $k {
            fn as_key(&self) -> &'a str {
                (*self).as_ref()
            }
        }
        impl<'a, 'b> AsKey<(&'a str, &'b Type)> for (&'a $k, &'b Type) {
            fn as_key(&self) -> (&'a str, &'b Type) {
                let (a,b) = *self;
                (a.as_ref(), b)
            }
        }
    };
    (@askey 2, $k:ty, $id:ty) => {
        impl<'a> AsKey<(&'a str, Id)> for (&'a $k, $id) {
            fn as_key(&self) -> (&'a str, Id) {
                let (a,b) = *self;
                (a.as_ref(), Id::from(b))
            }
        }
        impl<'a, 'b> AsKey<(&'a str, &'b Type, Id)> for (&'a $k, &'b Type, $id) {
            fn as_key(&self) -> (&'a str, &'b Type, Id) {
                let (a,b,c) = *self;
                (a.as_ref(), b, Id::from(c))
            }
        }
    };
}

key_impl!(str => opt, Tag => res);
