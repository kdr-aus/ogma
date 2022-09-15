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
