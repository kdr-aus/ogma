use super::*;

// ------ Ls -------------------------------------------------------------------
#[test]
fn ls_help_msg() {
    let src = "ls --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `ls`
--> shell:0
 | list out aspects of the input
 | input is Nil; outputs the filesystem contents in the current working dir
 | input is Table; outputs the headers as a table
 | 
 | Usage:
 |  => ls [path]
 | 
 | Examples:
 |  list the current working directory items
 |  => ls
 | 
 |  list directory items in `path`
 |  => ls path/to
 | 
 |  list headers in table
 |  => open table.csv | ls
"
    );
}

#[test]
fn ls_test() {
    let defs = &Definitions::new();
    let x = process_w_nil("ls", defs);
    if let Ok(Value::Tab(x)) = x {
        assert!(x
            .rows()
            .any(|mut r| matches!(r.nth(0).unwrap(), Entry::Obj(Value::Str(x)) if x == "ls-test")));
    } else {
        panic!()
    }

    // check it goes into folders
    let x = process_w_nil(
        "ls ls-test | filter name --Str != 'test-bom.csv' | pick name type size ext",
        defs,
    );
    // can't test modified on ci =/
    let t = vec![
        vec![o("name"), o("type"), o("size"), o("ext")],
        vec![o("0.txt"), o("file"), n(60), o("txt")],
        vec![o("a.txt"), o("file"), n(0), o("txt")],
        vec![o("b.txt"), o("file"), n(13), o("txt")],
        vec![o("test-file.csv"), o("file"), n(7), o("csv")],
    ];
    check_is_table(x, t);
}

#[test]
fn ls_table_test() {
    let defs = &Definitions::new();
    let x = process_w_table("ls", defs);
    let exp = vec![
        vec![o("header")],
        vec![o("first")],
        vec![o("snd")],
        vec![o("Heading 3")],
    ];
    check_is_table(x, exp);
}

#[test]
fn ls_err() {
    let def = &Definitions::new();
    let x = process_w_nil("ls noope", def).unwrap_err().to_string();
    println!("{}", x);
    if cfg!(windows) {
        assert_eq!(
        &x,
        "Evaluation Error: an io error occurred: The system cannot find the path specified. (os error 3)
--> shell:0
 | ls noope
 | ^^^^^^^^ within this block
"
    );
    } else {
        assert_eq!(
            &x,
            "Evaluation Error: an io error occurred: No such file or directory (os error 2)
--> shell:0
 | ls noope
 | ^^^^^^^^ within this block
"
        );
    }
}
