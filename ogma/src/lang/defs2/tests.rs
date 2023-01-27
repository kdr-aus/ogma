use super::*;

#[test]
fn fs_structure_building() {
    fn keys(i: Vec<&str>) -> Vec<PathBuf> {
        i.into_iter().map(PathBuf::from).collect()
    }

    let m = build_fs_map(Path::new("partitions-structure-tests/test01")).unwrap();
    assert_eq!(m.keys().cloned().collect::<Vec<_>>(), keys(vec![]));

    let m = build_fs_map(Path::new("partitions-structure-tests/test02")).unwrap();
    assert_eq!(
        m.keys().cloned().collect::<Vec<_>>(),
        keys(vec!["bar", "foo"])
    );
    assert_eq!(m.values().map(Vec::len).collect::<Vec<_>>(), vec![1, 1]);

    let m = build_fs_map(Path::new("partitions-structure-tests/test03")).unwrap();
    assert_eq!(
        m.keys().cloned().collect::<Vec<_>>(),
        keys(vec!["bar", "foo", "zog"])
    );
    assert_eq!(m.values().map(Vec::len).collect::<Vec<_>>(), vec![1, 1, 2]);

    let m = build_fs_map(Path::new("partitions-structure-tests/test04")).unwrap();
    assert_eq!(
        m.keys().cloned().collect::<Vec<_>>(),
        keys(vec!["bar/foo", "foo", "foo/bar", "foo/foo"])
    );
    assert_eq!(
        m.values().map(Vec::len).collect::<Vec<_>>(),
        vec![2, 2, 1, 2]
    );

    let x = build_fs_map(Path::new("partitions-structure-tests/test05"))
        .unwrap_err()
        .to_string();
    println!("{x}");
    assert_eq!(
        &x,
        "Parsing Error: the partition 'foo' is defined adjacent and as a directory\n"
    );
}

#[test]
fn ensure_unit_root() {
    let p = Partitions::new();
    assert_eq!(ROOT, p.root().0);
}

#[test]
fn api_smoke_test() {
    let d = Definitions::new();

    let k = String::from("foo");

    let _: Option<_> = d.types().get(k.as_str(), ROOT);

    let _: Option<_> = d.impls().get(&(k.as_str(), &Type::Nil), ROOT);

    drop(k); // ensure d outlives k

    let k = Tag::from(ast::Tag_ {
        line: "foo".into(),
        start: 0,
        end: 3,
        anchor: ast::Location::Shell,
    });

    let _: Result<_> = d.types().get(&k, ROOT);

    let _: Result<_> = d.impls().get(&(&k, &Type::Nil), ROOT);

    drop(k); // ensure d outlives k
}
