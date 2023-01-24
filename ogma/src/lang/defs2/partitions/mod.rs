use crate::prelude::*;
use lang::parse::{File, Import, Prefix};
use std::{fmt, ops::Index, path::Path};

mod item;
mod node;
mod partset;
#[cfg(test)]
mod tests;

use partset::PartSet;

type Id = u32;

#[derive(Debug, Clone)]
pub struct Node {
    name: Str,
    parent: Option<BoundaryNode>,
    item: Item,
}

#[derive(Debug, Clone)]
enum Item {
    Boundary { exports: PartSet, children: Vec<Id> },
    Type { imports: PartSet },
    Impl { imports: PartSet },
}

// Partitions are stored as a flat list of nodes
// Each node has a tree like structure, an optional parent and optional children
// There is no way to remove nodes, so node indices are stable
// There are 3 root nodes, [root, shell, plugins]

#[derive(Debug)]
pub struct Partitions(Vec<Node>);

macro_rules! node_wrapper {
    ($($n:ident)*) => {
        $(
#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub struct $n(pub Id);
impl $n {
    pub fn id(self) -> Id {
        self.0
    }
}
impl From<$n> for Id {
    fn from(n: $n) -> Self {
        n.id()
    }
}
impl fmt::Display for $n {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
        )*
    }
}

node_wrapper! { BoundaryNode TypeNode ImplNode }

impl Partitions {
    pub fn new() -> Self {
        let root = Node {
            name: "<root>".into(),
            parent: None,
            item: Item::empty_boundary(),
        };
        let shell = Node {
            name: "<shell>".into(),
            parent: None,
            item: Item::empty_boundary(),
        };
        let plugins = Node {
            name: "<plugins>".into(),
            parent: None,
            item: Item::empty_boundary(),
        };

        Partitions(vec![root, shell, plugins])
    }

    pub fn root(&self) -> (BoundaryNode, &Node) {
        (BoundaryNode(0), &self.0[0])
    }

    pub fn shell(&self) -> (BoundaryNode, &Node) {
        (BoundaryNode(1), &self.0[1])
    }

    pub fn plugins(&self) -> (BoundaryNode, &Node) {
        (BoundaryNode(2), &self.0[2])
    }

    pub fn extend_root(mut self, fsmap: super::FsMap) -> Result<Self> {
        // Phase 1: Create the structure of the graph given the map
        //          - we avoid the looking at the imports/exports for now
        //          - since we destruct the File, the remaining parts need to be stored for later

        let mut exports_map = <HashMap<_, Vec<_>>>::default();
        let mut imports_col = Vec::new();

        let root = self.root().0;
        for (p, files) in fsmap {
            let bnd = self.get_or_create_boundary_path(&p, root)?;

            for file in files {
                // deconstruct the file
                let File {
                    doc: _,
                    directives,
                    types,
                    impls,
                    exprs: _,
                } = file;

                // deconstruct the imports and exports
                let (imports, exports) =
                    directives
                        .into_iter()
                        .fold((Vec::new(), Vec::new()), |(mut i, mut e), x| {
                            match x {
                                lang::parse::Directive::Import(x) => i.extend(x),
                                lang::parse::Directive::Export(x) => e.extend(x),
                                lang::parse::Directive::FailFast
                                | lang::parse::Directive::NoParallelise => (),
                            }
                            (i, e)
                        });

                // extend the export map with the listed exports from this file,
                // note that we do not check for names yet, despite knowing the defs
                if !exports.is_empty() {
                    exports_map.entry(bnd).or_default().extend(exports);
                }

                // construct a nodes list which imports will be mapped to
                let mut ns = Vec::with_capacity(types.len() + impls.len());

                for (n, _) in &types {
                    ns.push(self.add_type(bnd, n)?.id());
                }

                for (n, _) in &impls {
                    ns.push(self.add_impl(bnd, n)?.id());
                }

                if !ns.is_empty() && !imports.is_empty() {
                    imports_col.push((bnd, imports, ns));
                }
            }
        }

        // Phase 2: Populate the boundary exports list
        //          - This list will be required for the imports resolution
        //          - We also check that all exports exist
        for (bnd, exports) in exports_map {
            self.add_exports(bnd, exports)?;
        }

        // Phase 3: Populate each item's import list
        for (bnd, imports, nodes) in imports_col {
            self.add_imports(bnd, imports, nodes)?;
        }

        Ok(self)
    }

    /// General adding of a node.
    ///
    /// Since all the nodes must have a parent (the root nodes are initialised), this handles
    /// linking the child and the parent. Returns the id of the new child.
    fn add_node<N>(&mut self, parent: BoundaryNode, name: N, item: Item) -> Id
    where
        N: Into<Str>,
    {
        let child = self.0.len() as Id;
        self.0.push(Node {
            name: name.into(),
            parent: Some(parent),
            item,
        });
        if let Item::Boundary { children, .. } = &mut self.get_mut(parent).item {
            children.push(child);
        }

        child
    }

    /// # Panics
    /// Panics if `node` is not within `self`.
    ///
    /// There is no optional way to get something by index, so leave this function private.
    fn get_mut<I: Into<Id>>(&mut self, node: I) -> &mut Node {
        &mut self.0[node.into() as usize]
    }

    fn get_or_create_boundary_path(
        &mut self,
        path: &Path,
        root: BoundaryNode,
    ) -> Result<BoundaryNode> {
        let mut a = root;
        for p in path.iter() {
            let b = self.children(a).find(|&n| self[n].eq_boundary(p));
            let b = match b {
                Some(b) => b,
                None => {
                    let name = p.to_str().map(Str::new).unwrap_or_default();
                    is_valid_part_name(&name)?;
                    self.add_node(a, name, Item::empty_boundary())
                }
            };

            a = BoundaryNode(b); // next node
        }

        Ok(a)
    }

    fn children(&self, bnd: BoundaryNode) -> impl ExactSizeIterator<Item = Id> + '_ {
        match &self[bnd].item {
            Item::Boundary { children, .. } => children.iter().copied(),
            _ => panic!("{bnd} is not a boundary node"),
        }
    }

    fn add_type<N: Into<Str>>(&mut self, parent: BoundaryNode, name: N) -> Result<TypeNode> {
        let name = name.into();
        let exists = self.children(parent).any(|n| self[n].eq_type(&name));

        if exists {
            return Err(item_already_defined("type", &name));
        }

        Ok(TypeNode(self.add_node(
            parent,
            name,
            Item::Type {
                imports: partset::EMPTY.clone(),
            },
        )))
    }

    fn add_impl<N: Into<Str>>(&mut self, parent: BoundaryNode, name: N) -> Result<ImplNode> {
        let name = name.into();
        let exists = self.children(parent).any(|n| self[n].eq_impl(&name));

        if exists {
            return Err(item_already_defined("impl", &name));
        }

        Ok(ImplNode(self.add_node(
            parent,
            name,
            Item::Impl {
                imports: partset::EMPTY.clone(),
            },
        )))
    }

    fn add_exports(&mut self, boundary: BoundaryNode, exports: Vec<Tag>) -> Result<()> {
        if exports.is_empty() {
            return Ok(());
        }

        let mut xs = if let Item::Boundary { exports, .. } = &self[boundary].item {
            exports.to_vec()
        } else {
            panic!("`boundary` is not a BoundaryNode");
        };

        for e in exports {
            let l = xs.len();

            xs.extend(
                self.glob_find(boundary, &e)?
                    .filter_map(|(n, node)| (!node.is_boundary()).then_some(n)),
            );

            if xs.len() == l {
                return Err(Error {
                    cat: err::Category::Definitions,
                    desc: format!("export glob '{e}' does not match any items"),
                    traces: err::trace(&e, "exports here".to_string()),
                    ..Error::default()
                });
            }
        }

        let xs = PartSet::from_vec(xs, self);

        if let Item::Boundary { exports, .. } = &mut self.get_mut(boundary).item {
            *exports = xs;
        };

        Ok(())
    }

    fn add_imports(
        &mut self,
        boundary: BoundaryNode,
        imports: Vec<Import>,
        to: Vec<Id>,
    ) -> Result<()> {
        if imports.is_empty() {
            return Ok(());
        }

        let xs = self.resolve_imports(boundary, imports.iter())?;
        let xs = PartSet::from_vec(xs, self);

        for n in to {
            match &mut self.get_mut(n).item {
                Item::Boundary { .. } => (),
                Item::Type { imports } => *imports = xs.clone(),
                Item::Impl { imports } => *imports = xs.clone(),
            }
        }

        Ok(())
    }

    fn resolve_imports<'a, I>(&self, from: BoundaryNode, imports: I) -> Result<Vec<Id>>
    where
        I: IntoIterator<Item = &'a Import>,
    {
        imports.into_iter().try_fold(Vec::new(), |mut v, import| {
            let x = self.resolve_import(from, import)?;

            let l = v.len();
            v.extend(x);

            if v.len() == l {
                Err(Error {
                    cat: err::Category::Definitions,
                    desc: "import directive resulted in no imports".to_string(),
                    traces: err::trace(&import.tag(), "this import".to_string()),
                    help_msg: Some("remove the import since it does not do anything".into()),
                    ..Error::default()
                })
            } else {
                Ok(v)
            }
        })
    }

    fn resolve_import(
        &self,
        from: BoundaryNode,
        import: &Import,
    ) -> Result<impl Iterator<Item = Id> + '_> {
        let Import { prefix, path, glob } = import;
        let this = from;
        let from = match prefix {
            Prefix::None => from,
            Prefix::Root => self.root().0,
            Prefix::Plugins => self.plugins().0,
        };
        let bnd = self.find_boundary(from, path)?;
        let exports = self.exports(bnd);
        Ok(self
            .glob_find(bnd, glob)?
            // do not include the self partition
            .filter(move |(x, _)| *x != this.id())
            .filter_map(|(x, n)| {
                // always import a boundary reference
                (n.is_boundary() ||
            // only import if the node is exposed via `export`
                exports.contains_id(x))
                .then_some(x)
            }))
    }

    pub fn find_boundary<'a, P>(&self, from: BoundaryNode, path: P) -> Result<BoundaryNode>
    where
        P: IntoIterator<Item = &'a Tag>,
    {
        let mut a = from;

        for p in path {
            if p == ".." {
                // go up a level
                a = match self[a].parent {
                    Some(x) => x,
                    None => {
                        return Err(Error {
                            cat: err::Category::Definitions,
                            desc: "import path goes beyond root".to_string(),
                            traces: err::trace(p, "this goes beyond the root partiton".to_string()),
                            ..Error::default()
                        });
                    }
                };
                continue;
            }

            match self.children(a).find(|&n| self[n].eq_boundary(p)) {
                Some(b) => a = BoundaryNode(b),
                None => {
                    let mut e = Error {
                        cat: err::Category::Definitions,
                        desc: format!("{p} does not match any partitions"),
                        traces: err::trace(p, None),
                        help_msg: None,
                        hard: true,
                    };

                    let x = self
                        .fuzzy_find(a, p)
                        .filter_map(|(_, n)| n.is_boundary().then(|| n.name().as_str()))
                        .collect::<Vec<_>>();

                    if !x.is_empty() {
                        let m = "Did you mean any of these? ".to_string() + &x.join(", ");
                        e.help_msg = m.into();
                    }

                    return Err(e);
                }
            }
        }

        Ok(a)
    }

    fn fuzzy_find<P: AsRef<str>>(
        &self,
        parent: BoundaryNode,
        n: P,
    ) -> impl Iterator<Item = (Id, &Node)> {
        let mut e = simsearch::SimSearch::new();
        for n in self.children(parent) {
            e.insert(n, self[n].name())
        }

        e.search(n.as_ref()).into_iter().map(|n| (n, &self[n]))
    }

    pub fn glob_find(
        &self,
        parent: BoundaryNode,
        pattern: &Tag,
    ) -> Result<impl Iterator<Item = (Id, &Node)>> {
        let pat = globset::Glob::new(pattern.str())
            .map_err(|e| Error {
                cat: err::Category::Parsing,
                desc: "invalid glob pattern".into(),
                traces: err::trace(pattern, format!("{e}")),
                help_msg: None,
                hard: true,
            })?
            .compile_matcher();

        Ok(self.children(parent).filter_map(move |n| {
            let node = &self[n];
            pat.is_match(node.name().as_str()).then_some((n, node))
        }))
    }

    pub fn exports(&self, bnd: BoundaryNode) -> &PartSet {
        self[bnd].item.exports().expect("boundary node")
    }
}

impl Index<BoundaryNode> for Partitions {
    type Output = Node;

    fn index(&self, i: BoundaryNode) -> &Node {
        let x = &self.0[i.id() as usize];
        assert!(x.is_boundary());
        x
    }
}

impl Index<TypeNode> for Partitions {
    type Output = Node;

    fn index(&self, i: TypeNode) -> &Node {
        let x = &self.0[i.id() as usize];
        assert!(x.is_type());
        x
    }
}

impl Index<ImplNode> for Partitions {
    type Output = Node;

    fn index(&self, i: ImplNode) -> &Node {
        let x = &self.0[i.id() as usize];
        assert!(x.is_impl());
        x
    }
}

impl Index<Id> for Partitions {
    type Output = Node;

    fn index(&self, i: Id) -> &Node {
        &self.0[i as usize]
    }
}

fn item_already_defined(ty: &str, name: &str) -> Error {
    use crate::prelude::err::*;

    Error {
        cat: Category::Definitions,
        desc: format!("the {ty} '{name}' is already defined"),
        hard: true,
        ..Error::default()
    }
}

fn is_valid_part_name(name: &str) -> Result<()> {
    use err::*;

    if name.is_empty() {
        Err(Error {
            cat: Category::Definitions,
            desc: "partition boundary names cannot be empty".into(),
            ..Default::default()
        })
    } else {
        let mut cs = name.chars();

        let f = cs.next().unwrap();

        if f == '_' || f.is_ascii_alphabetic() {
            if cs.all(|c| c == '-' || c == '_' || c.is_ascii_alphanumeric()) {
                Ok(())
            } else {
                Err(Error {
                cat: Category::Definitions,
                desc: format!("partition name '{name}' is invalid, it contains a character outside of _,-,a-z,A-Z,0-9"),
                ..Default::default()
            })
            }
        } else {
            Err(Error {
                cat: Category::Definitions,
                desc: format!("partition name '{name}' is invalid, must start with _,a-z,A-Z"),
                ..Default::default()
            })
        }
    }
}
