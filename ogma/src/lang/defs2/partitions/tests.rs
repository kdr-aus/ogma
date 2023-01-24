use super::*;

macro_rules! describe {
        ($part:expr => $nl:literal:{$($ns:tt)*} [$($es:tt)*]) => {{
            assert_eq!($part.0.len(), $nl);
            describe!(@node $part, $($ns)*);
            describe!(@edge $part, $($es)*);
        }};
        (@node $part:expr, $($idx:literal : $t:ident $name:literal,)*) => {{
            $(describe!(@node1 $t $part, $idx, $name);)*
        }};
        (@node1 B $part:expr, $idx:literal, $name:literal) => {{
            let n = $part.0.get($idx).expect(&format!("node with index {}", $idx));
            assert_eq!(n.name(), $name);
            assert!(n.is_boundary(), "expecting Boundary node at {}", $idx);
        }};
        (@node1 T $part:expr, $idx:literal, $name:literal) => {{
            let n = $part.0.get($idx).expect(&format!("node with index {}", $idx));
            assert_eq!(n.name(), $name);
            assert!(n.is_type(), "expecting Type node at {}", $idx);
        }};
        (@node1 I $part:expr, $idx:literal, $name:literal) => {{
            let n = $part.0.get($idx).expect(&format!("node with index {}", $idx));
            assert_eq!(n.name(), $name);
            assert!(n.is_impl(), "expecting Impl node at {}", $idx);
        }};
        (@edge $part:expr, $($a:literal -> $b:literal ,)*) => {{
            $(
                assert!($part.children(BoundaryNode($a)).any(|n| n == $b));
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
fn assert_root_nodes() {
    let p = Partitions::new();
    let (a, b) = p.root();
    assert_eq!(a, BoundaryNode(0));
    assert_eq!(b.name(), "<root>");

    let (a, b) = p.shell();
    assert_eq!(a, BoundaryNode(1));
    assert_eq!(b.name(), "<shell>");

    let (a, b) = p.plugins();
    assert_eq!(a, BoundaryNode(2));
    assert_eq!(b.name(), "<plugins>");
}

#[test]
fn extending_partition_graph_with_fsmap() {
    let p = Partitions::new();

    describe! { p =>
        3:{0: B "<root>", 1: B "<shell>", 2: B "<plugins>",}
        []
    };

    let p = p.extend_root(Default::default()).unwrap();

    describe! { p =>
        3:{0: B "<root>", 1: B "<shell>", 2: B "<plugins>",}
        []
    };

    let p = p.extend_root(mkmap([("foo", vec![])])).unwrap();

    describe! { p =>
        4:{0: B "<root>", 1: B "<shell>", 2: B "<plugins>", 3: B "foo",}
        [0 -> 3,]
    };

    let p = p
        .extend_root(mkmap([("foo", vec![Ok("TypeA"), Err("impl-a")])]))
        .unwrap();

    dbg!(&p);
    describe! { p =>
        6:{0: B "<root>", 1: B "<shell>", 2: B "<plugins>", 3: B "foo",
           4: T "TypeA", 5: I "impl-a", }
        [0->3, 3->4, 3->5,]
    };

    let p = p
        .extend_root(mkmap([("foo/bar/zog", vec![Ok("TypeA"), Err("impl-a")])]))
        .unwrap();

    describe! { p =>
        10:{0: B "<root>", 1: B "<shell>", 2: B "<plugins>", 3: B "foo",
            4: T "TypeA", 5: I "impl-a",
            6: B "bar", 7: B "zog", 8: T "TypeA", 9: I "impl-a",}
        [0->3,3->4,3->5,3->6,6->7,7->8,7->9,]
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
