use super::*;

// ------ Typify ---------------------------------------------------------------
#[test]
fn typify_help_msg() {
    let src = "typify --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `typify`
--> shell:0
 | output an expanded, type annotated, string of the argument
 | 
 | Usage:
 |  => typify argument
 | 
 | Examples:
 |  output the types of the ls command
 |  => typify ls
 | 
 |  output the types of an expression
 |  => typify { ls | filter size > 3 }
"
    );
}

#[test]
fn typify_test_raw() {
    let defs = &Definitions::new();

    let s = |s: &str| Ok(Value::Str(Str::new(s)));

    // Ident
    let x = process_w_nil("typify foo-bar", defs);
    assert_eq!(x, s("foo-bar:Str"));
    let x = process_w_nil("typify 'foo-bar'", defs);
    assert_eq!(x, s("foo-bar:Str"));
    let x = process_w_nil("typify ''", defs);
    assert_eq!(x, s("'':Str"));

    // Number
    let x = process_w_nil("typify 3.14e3", defs);
    assert_eq!(x, s("3.14e3:Num"));

    // Literals
    let x = process_w_nil("typify #t", defs);
    assert_eq!(x, s("#t:Bool"));
    let x = process_w_nil("typify #f", defs);
    assert_eq!(x, s("#f:Bool"));
    let x = process_w_nil("typify #n", defs);
    assert_eq!(x, s("#n:Nil"));
    let x = process_w_nil("typify #i", defs);
    assert_eq!(x, s("#i:Nil"));
    let x = process_w_table("typify #i", defs);
    assert_eq!(x, s("#i:Table"));
}

#[test]
fn typify_test_vars() {
    let defs = &Definitions::new();

    let s = |s: &str| Ok(Value::Str(Str::new(s)));

    let x = process_w_nil("let $x | typify $x", defs);
    assert_eq!(x, s("$x:Nil"));
    let x = process_w_num("let $x | typify $x", defs);
    assert_eq!(x, s("$x:Num"));
}

#[test]
fn typify_test_expressions() {
    let defs = &Definitions::new();

    let s = |s: &str| Ok(Value::Str(Str::new(s)));

    let x = process_w_nil("typify ls", defs);
    assert_eq!(x, s("{:Nil ls }:Table"));

    let x = process_w_nil("typify { ls | filter foo < 3 }", defs);
    assert_eq!(
        x,
        s("{:Nil ls |:Table filter foo:Str {:Num < 3:Num }:Bool }:Table")
    );

    let x = process_w_nil(
        "typify { ls | fold '' + { \\$row | get foo --Str } | = bar }",
        defs,
    );
    assert_eq!(x, s("{:Nil ls |:Table fold '':Str {:Str + {:Str \\ $row:TableRow |:TableRow get foo:Str }:Str }:Str |:Str = bar:Str }:Bool"));
}
