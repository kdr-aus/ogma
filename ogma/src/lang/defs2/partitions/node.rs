use super::*;

impl Node {
    pub fn name(&self) -> &Str {
        &self.name
    }

    pub fn item(&self) -> Option<&PItem> {
        match &self.item {
            Item::Boundary { .. } => None,
            Item::Type { item, .. } | Item::Impl { item, .. } => item.as_ref(),
        }
    }

    pub fn is_boundary(&self) -> bool {
        self.item.is_boundary()
    }

    pub fn is_type(&self) -> bool {
        self.item.is_type()
    }

    pub fn is_impl(&self) -> bool {
        self.item.is_impl()
    }

    pub fn eq_boundary<N: PartialEq<str> + ?Sized>(&self, name: &N) -> bool {
        self.is_boundary() && name.eq(self.name.as_str())
    }

    pub fn eq_type<N: PartialEq<str> + ?Sized>(&self, name: &N) -> bool {
        self.is_type() && name.eq(self.name.as_str())
    }

    pub fn eq_impl<N: PartialEq<str> + ?Sized>(&self, name: &N) -> bool {
        self.is_impl() && name.eq(self.name.as_str())
    }
}
