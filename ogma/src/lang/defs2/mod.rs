//! This handles definitions (fns, structs, enums)
use crate::prelude::*;
use std::fmt;

mod partitions;

use partitions::*;

pub struct Definitions {
    partitions: Partitions,
    impls: HashMap<ImplNode, ()>,
    types: HashMap<TypeNode, ()>,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub struct BoundaryNode(pub petgraph::prelude::NodeIndex);
impl BoundaryNode {
    pub fn idx(self) -> petgraph::prelude::NodeIndex {
        self.0
    }
    pub fn index(self) -> usize {
        self.0.index()
    }
}
impl From<BoundaryNode> for petgraph::prelude::NodeIndex {
    fn from(n: BoundaryNode) -> Self {
        n.idx()
    }
}
impl fmt::Display for BoundaryNode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.index())
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub struct TypeNode(pub petgraph::prelude::NodeIndex);
impl TypeNode {
    pub fn idx(self) -> petgraph::prelude::NodeIndex {
        self.0
    }
    pub fn index(self) -> usize {
        self.0.index()
    }
}
impl From<TypeNode> for petgraph::prelude::NodeIndex {
    fn from(n: TypeNode) -> Self {
        n.idx()
    }
}
impl fmt::Display for TypeNode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.index())
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub struct ImplNode(pub petgraph::prelude::NodeIndex);
impl ImplNode {
    pub fn idx(self) -> petgraph::prelude::NodeIndex {
        self.0
    }
    pub fn index(self) -> usize {
        self.0.index()
    }
}
impl From<ImplNode> for petgraph::prelude::NodeIndex {
    fn from(n: ImplNode) -> Self {
        n.idx()
    }
}
impl fmt::Display for ImplNode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.index())
    }
}
