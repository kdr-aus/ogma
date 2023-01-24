use super::{partset, Item, PartSet};
use Item::*;

impl Item {
    pub fn empty_boundary() -> Self {
        Boundary {
            exports: partset::EMPTY.clone(),
            children: Vec::new(),
        }
    }

    pub fn is_boundary(&self) -> bool {
        matches!(self, Boundary { .. })
    }

    pub fn is_type(&self) -> bool {
        matches!(self, Type { .. })
    }

    pub fn is_impl(&self) -> bool {
        matches!(self, Impl { .. })
    }

    pub fn exports(&self) -> Option<&PartSet> {
        if let Boundary { exports, .. } = self {
            Some(exports)
        } else {
            None
        }
    }

    pub fn imports(&self) -> Option<&PartSet> {
        match self {
            Boundary { .. } => None,
            Type { imports } => Some(imports),
            Impl { imports } => Some(imports),
        }
    }
}
