use super::*;
use lang::parse::*;
use std::{collections::BTreeMap, path::PathBuf};

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
        .extend_root(mkmap([("foo", vec![Err("impl-b"), Err("impl-a")])]));

    assert!(x.is_ok()); // duplicate impls allowed (to allow for type input variance)
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

fn file(s: &str) -> File {
    lang::parse::file(s, ast::Location::Shell).unwrap()
}

#[test]
fn imports_and_exports_smoke_test() {
    let mut map = BTreeMap::from_iter([(
        PathBuf::from("bar"),
        vec![file(
            "[export(fin)]

def fin () { }",
        )],
    )]);

    let p = Partitions::new().extend_root(map.clone()).unwrap();
    assert!(p.exports(BoundaryNode(3)).eq_names(&p, &["fin"]));

    map.extend([(
        PathBuf::from("foo"),
        vec![file(
            "[export(*og)]

def zog () {}

def-ty Zog { }",
        )],
    )]);

    let p = Partitions::new().extend_root(map.clone()).unwrap();
    assert!(p.exports(BoundaryNode(3)).eq_names(&p, &["fin"]));
    assert!(dbg!(p.exports(BoundaryNode(5))).eq_names(&p, &["Zog", "zog"]));

    // test that export does not export boundary
    map.extend([(
        PathBuf::from("foo/fog"),
        vec![file(
            "
def zog () {}

def-ty Zog { }",
        )],
    )]);

    let p = Partitions::new().extend_root(map.clone()).unwrap();
    assert!(p.exports(BoundaryNode(3)).eq_names(&p, &["fin"]));
    assert!(dbg!(p.exports(BoundaryNode(5))).eq_names(&p, &["Zog", "zog"]));

    // test that the export doesn't exist errors
    let mut err = map.clone();
    err.extend([(
        PathBuf::from("foo/foo"),
        vec![file(
            "[export(reg)]

def-ty erg { }",
        )],
    )]);

    let p = Partitions::new().extend_root(err).unwrap_err().to_string();
    println!("{p}");
    assert_eq!(
        &p,
        "Definition Error: export glob 'reg' does not match any items
--> shell:8
 | [export(reg)]
 |         ^^^ exports here
"
    );

    // test successful imports
    map.extend([
        (
            PathBuf::from("foo/bar"),
            vec![file(
                "[import(/bar/*in)]
[import(../*)]
[import(inner/*)]

def cool () {}",
            )],
        ),
        (
            PathBuf::from("foo/bar/inner"),
            vec![file(
                "[export(za)]

def za () { }

def zb () { }",
            )],
        ),
    ]);

    let p = Partitions::new().extend_root(map.clone()).unwrap();
    assert!(p.exports(BoundaryNode(3)).eq_names(&p, &["fin"]));
    assert!(dbg!(p.exports(BoundaryNode(5))).eq_names(&p, &["Zog", "zog"]));
    assert!(dbg!(&p[9])
        .item
        .imports()
        .unwrap()
        .eq_names(&p, &["Zog", "fin", "fog", "za", "zog"]));
    // notice that foo/fog (boundary) gets imported!

    // test that no import matches results in an error
    let mut err = map.clone();
    err.extend([(
        PathBuf::from("foo/bar"),
        vec![file(
            "[import(../fog/zog)]
    
def-ty erg { }",
        )],
    )]);

    let p = Partitions::new().extend_root(err).unwrap_err().to_string();
    println!("{p}");
    assert_eq!(
        &p,
        "Definition Error: import directive resulted in no imports
--> shell:8
 | [import(../fog/zog)]
 |         ^^^^^^^^^^ this import
--> help: remove the import since it does not do anything
"
    );

    // test that import path goes beyond root fails
    let mut err = map.clone();
    err.extend([(
        PathBuf::from("foo/bar"),
        vec![file(
            "[import(/../foo)]
    
def-ty erg { }

def erg { }",
        )],
    )]);

    let p = Partitions::new().extend_root(err).unwrap_err().to_string();
    println!("{p}");
    assert_eq!(
        &p,
        "Definition Error: import path goes beyond root
--> shell:9
 | [import(/../foo)]
 |          ^^ this goes beyond the root partiton
"
    );
}

#[test]
fn duplicate_defs_on_types_work() {
    let p = Partitions::new()
        .extend_root(FromIterator::from_iter([(
            PathBuf::from("foo"),
            vec![
                file("def foo () { }"),
                file(
                    "def foo Num () { }

def foo Str () { }",
                ),
            ],
        )]))
        .unwrap();

    describe! { p =>
        7:{0: B "<root>", 1: B "<shell>", 2: B "<plugins>"
          ,3: B "foo", 4: I "foo", 5: I "foo", 6: I "foo"
          ,}
        []
    };
}

#[test]
fn assert_partset_find_characteristics() {
    let p = Partitions::new()
        .extend_root(FromIterator::from_iter([
            (
                PathBuf::from("foo"),
                vec![file(
                    "def foo () { }

def-ty Foo () { }",
                )],
            ),
            (
                PathBuf::from("foo/bar"),
                vec![file(
                    "
def foo () { }

def bar () { }

def zog () { }

def zog () { }",
                )],
            ),
        ]))
        .unwrap();

    describe! { p =>
        11:{0: B "<root>", 1: B "<shell>", 2: B "<plugins>"
          ,3: B "foo", 4: T "Foo", 5: I "foo"
          ,6: B "bar", 7: I "foo", 8: I "bar", 9: I "zog", 10: I "zog"
          ,}
        []
    };

    let ps = PartSet::from_vec(vec![], &p);

    assert!(ps.find("", &p).collect::<Vec<u32>>().is_empty());
    assert!(ps.find("zog", &p).collect::<Vec<u32>>().is_empty());

    let ps = PartSet::from_vec(vec![3, 7], &p);

    assert!(ps.find("", &p).collect::<Vec<u32>>().is_empty());
    assert!(ps.find("zog", &p).collect::<Vec<u32>>().is_empty());
    assert!(ps.find("bar", &p).collect::<Vec<u32>>().is_empty());
    assert_eq!(ps.find("foo", &p).collect::<Vec<u32>>(), vec![3, 7]);

    let ps = PartSet::from_vec(vec![3, 7, 4, 9], &p);

    assert!(ps.find("", &p).collect::<Vec<u32>>().is_empty());
    assert_eq!(ps.find("zog", &p).collect::<Vec<u32>>(), vec![9]);
    assert!(ps.find("bar", &p).collect::<Vec<u32>>().is_empty());
    assert_eq!(ps.find("foo", &p).collect::<Vec<u32>>(), vec![3, 7]);
    assert_eq!(ps.find("Foo", &p).collect::<Vec<u32>>(), vec![4]);

    let ps = PartSet::from_vec((0..11).collect(), &p);

    assert!(ps.find("", &p).collect::<Vec<u32>>().is_empty());
    assert!(ps.find("as", &p).collect::<Vec<u32>>().is_empty());
    assert_eq!(ps.find("foo", &p).collect::<Vec<u32>>(), vec![3, 5, 7]);
    assert_eq!(ps.find("Foo", &p).collect::<Vec<u32>>(), vec![4]);
    assert_eq!(ps.find("bar", &p).collect::<Vec<u32>>(), vec![6, 8]);
    assert_eq!(ps.find("zog", &p).collect::<Vec<u32>>(), vec![9, 10]);
}

#[test]
fn assert_find_characteristics() {
    let p = Partitions::new()
        .extend_root(FromIterator::from_iter([
            (
                PathBuf::from("foo"),
                vec![file(
                    "def foo () { }

def-ty Foo () { }",
                )],
            ),
            (
                PathBuf::from("foo/bar"),
                vec![file(
                    "
def foo () { }

def bar () { }

def zog () { }

def zog () { }",
                )],
            ),
        ]))
        .unwrap();

    describe! { p =>
        11:{0: B "<root>", 1: B "<shell>", 2: B "<plugins>"
          ,3: B "foo", 4: T "Foo", 5: I "foo"
          ,6: B "bar", 7: I "foo", 8: I "bar", 9: I "zog", 10: I "zog"
          ,}
        [0->3,3->4,3->5,
         3->6,6->7,6->8,6->9,6->10,
        ]
    };

    assert!(p.find(p.root().0, PartSet::empty(), "zog").is_empty());
    assert!(p.find(p.root().0, PartSet::empty(), "foo/zog").is_empty());
    assert!(p.find(p.root().0, PartSet::empty(), "..").is_empty());
    assert!(p.find(p.root().0, PartSet::empty(), "../foo").is_empty());

    assert_eq!(
        p.find(p.root().0, PartSet::empty(), "foo/bar/zog"),
        vec![9, 10]
    );
    assert_eq!(
        p.find(p.root().0, &PartSet::from_vec(vec![3], &p), "foo/bar/zog"),
        vec![9, 10]
    );
    assert_eq!(
        p.find(p.root().0, &PartSet::from_vec(vec![6], &p), "bar/zog"),
        vec![9, 10]
    );
    assert_eq!(
        p.find(p.root().0, &PartSet::from_vec(vec![6], &p), "bar/../Foo"),
        vec![4]
    );
    assert_eq!(
        p.find(p.root().0, &PartSet::from_vec(vec![3], &p), "foo/foo"),
        vec![5]
    );
    assert_eq!(
        p.find(p.root().0, &PartSet::from_vec(vec![3, 6], &p), "foo/foo"),
        vec![5]
    );
    assert_eq!(p.find(BoundaryNode(6), PartSet::empty(), "../Foo"), vec![4]);
    assert_eq!(
        p.find(BoundaryNode(6), PartSet::empty(), "../../foo"),
        vec![3]
    );
}
