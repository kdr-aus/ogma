//! This handles definitions (fns, structs, enums)
use crate::prelude::*;
use ast::Location;
use lang::parse::{File, Import};
use std::{
    collections::BTreeMap,
    fmt,
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

impl Definitions {}

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
