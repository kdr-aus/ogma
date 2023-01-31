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
    /// A cheap static empty partition set.
    pub fn empty() -> &'static PartSet {
        &EMPTY
    }

    pub fn from_vec(mut ids: Vec<Id>, parts: &Partitions) -> Self {
        if ids.is_empty() {
            EMPTY.clone()
        } else {
            ids.sort(); // first sort by Id to deduplicate
            ids.dedup(); // remove duplicate ids
            ids.sort_by(|&a, &b| node_cmp(&parts[a], &parts[b])); // sort for retrieval

            PartSet(Arc::from(ids))
        }
    }

    pub fn to_vec(&self) -> Vec<Id> {
        self.0.to_vec()
    }

    /// Does a linear search for an id match.
    pub fn contains_id(&self, id: Id) -> bool {
        self.0.contains(&id)
    }

    /// Does an efficient search for all [`Id`]s that use `name`.
    pub fn find(&self, name: &str, parts: &Partitions) -> impl ExactSizeIterator<Item = Id> + '_ {
        // [T]::partition_point works by assuming a partitioned slice on the predicate
        // since array is ordered on `node_cmp`, we can leverage this to get a range that matches
        // `name`.
        // There are few important notes:
        // - slice is assumed partitioned where `true` is on _left_ of partition point
        // - since node_cmp orders by name first, anything < `name` should be at the start
        // - to get the upr point, the partition point will be when it **stops equaling `name`**
        let lwr = self.0.partition_point(|&i| parts[i].name() < name);
        let upr = self.0.partition_point(|&i| parts[i].name() <= name);

        self.0[lwr..upr].iter().copied()
    }

    pub fn iter(&self) -> impl Iterator<Item = Id> + '_ {
        self.0.iter().copied()
    }

    #[cfg(test)]
    pub fn eq_names(&self, parts: &Partitions, names: &[&str]) -> bool {
        let names_ = self
            .0
            .iter()
            .map(|&x| parts[x].name().as_str())
            .collect::<Vec<_>>();

        dbg!(names_).eq(names)
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
    use super::*;
    use partset::EMPTY;
    use quickcheck::{Arbitrary, Gen};

    impl Arbitrary for Node {
        fn arbitrary(g: &mut Gen) -> Self {
            let item = match u8::arbitrary(g) % 3 {
                0 => Item::empty_boundary(),
                1 => Item::Type {
                    imports: EMPTY.clone(),
                    item: None,
                },
                2 => Item::Impl {
                    imports: EMPTY.clone(),
                    item: None,
                },
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
