
use super::*;

macro_rules! describe {
        ($part:expr => $nl:literal:{$($ns:tt)*} $el:literal:[$($es:tt)*]) => {{
            assert_eq!($part.graph.node_count(), $nl);
            assert_eq!($part.graph.edge_count(), $el);
            describe!(@node $part, $($ns)*);
            describe!(@edge $part, $($es)*);
        }};
        (@node $part:expr, $($idx:literal : $t:ident $name:literal,)*) => {{
            $(describe!(@node1 $t $part, $idx, $name);)*
        }};
        (@node1 B $part:expr, $idx:literal, $name:literal) => {{
            let n = $part.graph.node_weight(NodeIndex::from($idx))
                .expect(&format!("node with index {}", $idx));
            match n {
                Node::Boundary { name , .. } => assert_eq!(name, $name),
                x => panic!("expecting Boundary node at {}, found: {x:?}", $idx),
            };
        }};
        (@node1 T $part:expr, $idx:literal, $name:literal) => {{
            let n = $part.graph.node_weight(NodeIndex::from($idx))
                .expect(&format!("node with index {}", $idx));
            match n {
                Node::Type { name , .. } => assert_eq!(name, $name),
                x => panic!("expecting Type node at {}, found: {x:?}", $idx),
            };
        }};
        (@node1 I $part:expr, $idx:literal, $name:literal) => {{
            let n = $part.graph.node_weight(NodeIndex::from($idx))
                .expect(&format!("node with index {}", $idx));
            match n {
                Node::Impl { name , .. } => assert_eq!(name, $name),
                x => panic!("expecting Boundary node at {}, found: {x:?}", $idx),
            };
        }};
        (@edge $part:expr, $($a:literal -> $b:literal ,)*) => {{
            $(
                assert!($part.graph.contains_edge(
                    NodeIndex::from($a), NodeIndex::from($b)));
            )*
        }};
    }

fn mkmap<I>(iter: I) -> super::super::FsMap
where
    I: IntoIterator<
        Item = (
            &'static str,
            Vec<std::result::Result<&'static str, &'static str>>,
        ),
    >,
{
    use lang::parse::Item;
    iter.into_iter()
        .map(|(p, f)| {
            let f = f
                .into_iter()
                .map(|f| {
                    let mut file = lang::parse::File::empty();
                    match f {
                        Ok(x) => file.types.push((x.to_string(), Item::dummy())),
                        Err(x) => file.impls.push((x.to_string(), Item::dummy())),
                    }
                    file
                })
                .collect();
            (std::path::PathBuf::from(p), f)
        })
        .collect()
}

#[test]
fn extending_partition_graph_with_fsmap() {
    let p = Partitions::new();

    describe! { p =>
        3:{0: B "<root>", 1: B "<shell>", 2: B "<plugins>",}
        0:[]
    };

    let p = p.extend_root(Default::default()).unwrap();

    describe! { p =>
        3:{0: B "<root>", 1: B "<shell>", 2: B "<plugins>",}
        0:[]
    };

    let p = p.extend_root(mkmap([("foo", vec![])])).unwrap();

    describe! { p =>
        4:{0: B "<root>", 1: B "<shell>", 2: B "<plugins>", 3: B "foo",}
        1:[0 -> 3,]
    };

    let p = p
        .extend_root(mkmap([("foo", vec![Ok("TypeA"), Err("impl-a")])]))
        .unwrap();

    describe! { p =>
        6:{0: B "<root>", 1: B "<shell>", 2: B "<plugins>", 3: B "foo",
           4: T "TypeA", 5: I "impl-a", }
        3:[0->3, 3->4, 3->5,]
    };

    let p = p
        .extend_root(mkmap([("foo/bar/zog", vec![Ok("TypeA"), Err("impl-a")])]))
        .unwrap();

    describe! { p =>
        10:{0: B "<root>", 1: B "<shell>", 2: B "<plugins>", 3: B "foo",
            4: T "TypeA", 5: I "impl-a",
            6: B "bar", 7: B "zog", 8: T "TypeA", 9: I "impl-a",}
        7:[0->3,3->4,3->5,3->6,6->7,7->8,7->9,]
    };
}

#[test]
fn extending_fails() {
    let x = Partitions::new()
        .extend_root(mkmap([("foo", vec![Ok("TypeA"), Ok("TypeA")])]))
        .unwrap_err();

    assert_eq!(
        &x.to_string(),
        "Definition Error: the type 'TypeA' is already defined
"
    );

    let x = Partitions::new()
        .extend_root(mkmap([
            ("foo", vec![Err("impl-a")]),
            ("foo/bar", vec![Ok("TypeA")]),
        ]))
        .unwrap()
        .extend_root(mkmap([("foo", vec![Err("impl-b"), Err("impl-a")])]))
        .unwrap_err();

    assert_eq!(
        &x.to_string(),
        "Definition Error: the impl 'impl-a' is already defined
"
    );
}

#[test]
fn valid_partition_naming() {
    // empty path does not iterate
    assert!(Partitions::new().extend_root(mkmap([("", vec![])])).is_ok());

    let x = Partitions::new()
        .extend_root(mkmap([("🌏", vec![])]))
        .unwrap_err();

    assert_eq!(
        &x.to_string(),
        "Definition Error: partition name '🌏' is invalid, must start with _,a-z,A-Z
"
    );

    let x = Partitions::new()
        .extend_root(mkmap([(" foo", vec![])]))
        .unwrap_err();

    assert_eq!(
        &x.to_string(),
        "Definition Error: partition name ' foo' is invalid, must start with _,a-z,A-Z
"
    );

    let x = Partitions::new()
        .extend_root(mkmap([("1234", vec![])]))
        .unwrap_err();

    assert_eq!(
        &x.to_string(),
        "Definition Error: partition name '1234' is invalid, must start with _,a-z,A-Z
"
    );

    let x = Partitions::new()
        .extend_root(mkmap([("Hello, 🌏", vec![])]))
        .unwrap_err();

    assert_eq!(&x.to_string(), "Definition Error: partition name 'Hello, 🌏' is invalid, it contains a character outside of _,-,a-z,A-Z,0-9
");
}
