use super::{partset, Item};

impl Item {
    pub fn empty_boundary() -> Self {
        Item::Boundary {
            exports: partset::EMPTY.clone(),
            children: Vec::new(),
        }
    }

    pub fn is_boundary(&self) -> bool {
        matches!(self, Item::Boundary { .. })
    }

    pub fn is_type(&self) -> bool {
        matches!(self, Item::Type { .. })
    }

    pub fn is_impl(&self) -> bool {
        matches!(self, Item::Impl { .. })
    }
}
