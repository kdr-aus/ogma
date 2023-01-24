use super::*;
use std::cmp::Ordering;

lazy_static::lazy_static! {
    pub static ref EMPTY: PartSet = PartSet(Arc::new([]));
}

/// A partition set of nodes, with specific structure for fast lookup on names.
///
/// The nodes are stored as a vector of IDs.
/// The ordering is determined by [`node_cmp`].
/// Retrieval is done through a binary search.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PartSet(Arc<[Id]>);

impl PartSet {
    pub fn from_vec(mut ids: Vec<Id>, parts: &Partitions) -> Self {
        ids.sort(); // first sort by Id to deduplicate
        ids.dedup(); // remove duplicate ids
        ids.sort_by(|&a, &b| node_cmp(&parts[a], &parts[b])); // sort for retrieval

        PartSet(Arc::from(ids))
    }

    pub fn to_vec(&self) -> Vec<Id> {
        self.0.to_vec()
    }
}

/// Total ordering for two nodes.
///
/// We order by name first, then by the type.
fn node_cmp(a: &Node, b: &Node) -> Ordering {
    use Item::*;

    let x = a.name.cmp(&b.name);
    if let Ordering::Equal = x {
        match (&a.item, &b.item) {
            (Boundary { .. }, Boundary { .. }) => Ordering::Equal,
            (Boundary { .. }, _) => Ordering::Less,
            (_, Boundary { .. }) => Ordering::Greater,

            (Type { .. }, Type { .. }) => Ordering::Equal,
            (Type { .. }, _) => Ordering::Less,
            (_, Type { .. }) => Ordering::Greater,

            (Impl { .. }, Impl { .. }) => Ordering::Equal,
        }
    } else {
        x
    }
}

#[cfg(test)]
mod tests {
    use partset::EMPTY;
    use super::*;
    use quickcheck::{Arbitrary, Gen};

    impl Arbitrary for Node {
        fn arbitrary(g: &mut Gen) -> Self {
            let item = match u8::arbitrary(g) % 3 {
                0 => Item::empty_boundary(),
                1 => Item::Type { imports: EMPTY.clone() },
                2 => Item::Impl { imports: EMPTY.clone() },
                _ => unreachable!(),
            };
            Node {
                name: String::arbitrary(g).into(),
                parent: None,
                item,
            }
        }
    }

    #[quickcheck]
    fn node_total_cmp(a: Node, b: Node) -> bool {
        let x = node_cmp(&a, &b);
        let y = node_cmp(&b, &a);
        x == y.reverse()
    }

    #[quickcheck]
    fn node_name_cmp(a: Node, b: Node) -> bool {
        match a.name.cmp(&b.name) {
            Ordering::Equal => true,
            x => x == node_cmp(&a, &b),
        }
    }
}
