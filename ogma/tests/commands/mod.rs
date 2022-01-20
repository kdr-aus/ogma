use libs::divvy::Str;
use ogma::{
    eng::*,
    lang::{ast::*, *},
    output::*,
    parse::expression,
    rt::*,
};
use std::{path::Path, sync::Arc};
use table::Entry;

type Result<T> = std::result::Result<T, ogma::Error>;

mod arithmetic;
mod cmp;
mod diagnostics;
mod io;
mod logic;
mod morphism;
mod pipeline;
mod types;

fn n<N: Into<::kserd::Number>>(n: N) -> Entry<Value> {
    Entry::Num(n.into())
}
fn o(s: &str) -> Entry<Value> {
    Entry::Obj(Value::Str(Str::new(s)))
}

fn process<T>(data: T, src: &str, defs: &Definitions) -> Result<Value>
where
    T: AsType + Into<Value> + 'static,
{
    let (root, wd) = paths();
    process_expression(data, src, Location::Shell, defs, root, wd)
}

fn paths() -> (&'static Path, &'static Path) {
    (Path::new("."), Path::new("../ogma"))
}

fn process_w_nil(src: &str, defs: &Definitions) -> Result<Value> {
    process((), src, defs)
}

fn process_w_num(src: &str, defs: &Definitions) -> Result<Value> {
    process(::kserd::Number::from(3), src, defs)
}

fn process_w_str(src: &str, defs: &Definitions) -> Result<Value> {
    process(Str::from("Hello"), src, defs)
}

fn process_w_table(src: &str, defs: &Definitions) -> Result<Value> {
    process(test_table(), src, defs)
}

fn test_table() -> Table {
    ::table::Table::from(vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ])
    .into()
}

fn check_is_table(r: Result<Value>, table: Vec<Vec<Entry<Value>>>) {
    match r {
        Ok(Value::Tab(tab)) => {
            assert_eq!(tab, Table::from(::table::Table::from(table)));
        }
        Err(e) => {
            println!("{}", e);
            panic!("returned err: {:?}", e)
        }
        x => panic!("not a table: {:?}", x),
    }
}

fn print_help(src: &str, defs: &Definitions) -> String {
    let x = eng::handle_help(&expression(src, Location::Shell, defs).unwrap(), defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    x
}

// ------ Multiline Expressions ------------------------------------------------
#[test]
fn multiline_expr() {
    let d = &Definitions::new();

    let x = process_w_nil(
        "
* 3 4 |
if {= 36}
    #f
    #t
| not",
        d,
    );
    assert_eq!(x, Ok(Value::Bool(false)));

    let x = process_w_num(
        "
* 3 4 |
if {= 36}
    #f
    #t
| not",
        d,
    );
    assert_eq!(x, Ok(Value::Bool(true)));

    let x = process_w_table(
        "
filter 'first' >= 0 |
append { get snd | 
    + 100 |
    * 200
} | map 'first' { + 1 }",
        d,
    );
    check_is_table(
        x,
        vec![
            vec![o("first"), o("snd"), o("Heading 3"), o("_append1")],
            vec![n(1), n(3), o("a"), n(20600)],
            vec![n(2), n(20), o("b"), n(24000)],
        ],
    );
}

#[test]
fn multiline_defs() {
    let d = &mut Definitions::new();

    let x = process_definition(
        "def foo Num (x y) {
    + $x $y |
    if {= 3}
        1
        0
}",
        Location::Shell,
        None,
        d,
    );
    assert!(x.is_ok());

    let x = process_definition(
        "def-ty Ord2 ::
        Lt {
            foo:Num bar:Num
        } |
        Eq { what:Str } |
        Gt",
        Location::Shell,
        None,
        d,
    );
    assert!(x.is_ok());
}

#[test]
fn multiline_errs() {
    let d = &Definitions::new();

    let x = process_w_nil(
        "* 3 4 |
    * 'foo'",
        d,
    )
    .unwrap_err()
    .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Semantics Error: expecting argument with type `Number`, found `String`
--> shell:7
 |     * 'foo'
 |        ^^^ this argument returns type `String`
--> help: commands may require specific argument types, use `--help` to view requirements
"
    );

    let x = process_w_nil(
        "filter {
    get snd | + 1
}",
        d,
    )
    .unwrap_err()
    .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Semantics Error: `filter` does not support `Nil` input data
--> shell:0
 | filter {
 | ^^^^^^
--> help: use `filter --help` to view requirements. consider implementing `def filter`
"
    );

    let x = process_w_table(
        "filter {
    get snd | + 1
}",
        d,
    )
    .unwrap_err()
    .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Semantics Error: expecting argument with type `Bool`, found `Number`
--> shell:7
 | filter {
 |     get snd | + 1
 | }
 | ^^^^^^^^^^^^^^^^^ this argument returns type `Number`
--> shell:7
 | filter {
 |     get snd | + 1
 | }
 | ^^^^^^^^^^^^^^^^^ invoked here
--> help: commands may require specific argument types, use `--help` to view requirements
"
    );

    let x = process_w_table(
        "filter 'snd'
{ + 1 |
    - 2 }",
        d,
    )
    .unwrap_err()
    .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Semantics Error: expecting argument with type `Bool`, found `Number`
--> shell:0
 | { + 1 |
 |     - 2 }
 | ^^^^^^^^^ this argument returns type `Number`
--> shell:0
 | { + 1 |
 |     - 2 }
 | ^^^^^^^^^ invoked here
--> help: commands may require specific argument types, use `--help` to view requirements
"
    );

    let x = process_w_table(
        "filter 'foo'
{ + 1 |
    - 2 |
    eq 3 }",
        d,
    )
    .unwrap_err()
    .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Evaluation Error: header `foo` not found in table
--> shell:8
 | filter 'foo'
 |         ^^^ `foo` resolves to `foo`
"
    );
}

// ------ Miscellaneous --------------------------------------------------------
#[test]
fn too_many_flags() {
    let def = &Definitions::new();
    let x = process_w_nil("\\ 5 --foo --bar", def)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        r#"Semantics Error: not expecting `foo` flag
--> shell:6
 | \ 5 --foo --bar
 |       ^^^ flag not supported
--> help: try using the `--help` flag to view requirements
"#
    );
}

#[test]
fn err_wrong_return_type() {
    let def = &Definitions::new();
    let x = process_w_table("filter { \\ 5 }", def)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        r#"Semantics Error: expecting argument with type `Bool`, found `Number`
--> shell:7
 | filter { \ 5 }
 |        ^^^^^^^ this argument returns type `Number`
--> shell:7
 | filter { \ 5 }
 |        ^^^^^^^ invoked here
--> help: commands may require specific argument types, use `--help` to view requirements
"#
    );
}

#[test]
fn unused_arg_test() {
    let def = &Definitions::new();
    let x = process_w_nil("\\ 5 { testing 2 { foo  bar } }", def)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        r#"Semantics Error: too many arguments supplied
--> shell:4
 | \ 5 { testing 2 { foo  bar } }
 |     ^^^^^^^^^^^^^^^^^^^^^^^^^^ expression argument is unnecessary
--> help: the command does not require or support additional arguments
"#
    );
}

#[test]
fn fs_caching_removes_changed_files() {
    let defs = &Definitions::new();

    std::fs::write("ls-test/test-file.csv", "a,b\n1,2").unwrap();
    let x = process_w_nil("open 'ls-test/test-file.csv'", defs);
    let exp = vec![vec![o("a"), o("b")], vec![n(1), n(2)]];
    let table = match &x {
        Ok(Value::Tab(table)) => table.clone(),
        _ => unreachable!("should be a table"),
    };
    check_is_table(x, exp.clone());

    let x = process_w_nil("open 'ls-test/test-file.csv'", defs);
    let table2 = match &x {
        Ok(Value::Tab(table)) => table.clone(),
        _ => unreachable!("should be a table"),
    };
    assert!(Arc::ptr_eq(&table.0, &table2.0));

    std::fs::write("ls-test/test-file.csv", "a,c\n1,3").unwrap();
    let x = process_w_nil("open 'ls-test/test-file.csv'", defs);
    let exp = vec![vec![o("a"), o("c")], vec![n(1), n(3)]];
    check_is_table(x, exp.clone());
}

// ------ General Bugs ---------------------------------------------------------
#[test]
fn gt_should_resolve_as_bool_return_type() {
    // This tests that the greater than op, which diverts to cmp, will properly register as
    // returning a Type::Bool
    let defs = &Definitions::new();

    let x = process_w_num("eq 3", defs);
    assert_eq!(x, Ok(Value::Bool(true)));

    let x = process_w_num("cmp 5 | eq Ord::Gt", defs);
    assert_eq!(x, Ok(Value::Bool(false)));

    let x = process_w_num("> 5", defs);
    assert_eq!(x, Ok(Value::Bool(false)));

    let x = process_w_table("filter { \\ 3 | > 5 }", defs);
    check_is_table(x, vec![vec![o("first"), o("snd"), o("Heading 3")]]);
}

#[test]
fn forbid_recursion() {
    let defs = &mut Definitions::new();
    let x = process_definition(
        "def test-recursion () { test-recursion }",
        Location::Shell,
        None,
        defs,
    )
    .unwrap_err()
    .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Unknown Command: operation `test-recursion` not defined
--> shell:24
 | def test-recursion () { test-recursion }
 |                         ^^^^^^^^^^^^^^ `test-recursion` not found
--> help: view a list of definitions using `def --list`
"
    );
}

#[test]
fn transitive_args_in_defs() {
    let defs = &mut Definitions::new();
    process_definition(
        "def col-gt10 (col) { get $col | > 10 }",
        Location::Shell,
        None,
        defs,
    )
    .unwrap();
    process_definition(
        "def filter-col-gt10 (col) { filter $col > 10 }",
        Location::Shell,
        None,
        defs,
    )
    .unwrap();

    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];

    let x = process_w_table("filter col-gt10 snd", defs);
    check_is_table(x, exp.clone());

    let x = process_w_table("filter-col-gt10 snd", defs);
    check_is_table(x, exp);

    let x = process_w_table("filter col-gt10 not-here", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Evaluation Error: header `not-here` not found in table
--> shell:26
 | def col-gt10 (col) { get $col | > 10 }
 |                           ^^^ `col` resolves to `not-here`
"
    );

    let x = process_w_table("filter-col-gt10 not-here", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Evaluation Error: header `not-here` not found in table
--> shell:36
 | def filter-col-gt10 (col) { filter $col > 10 }
 |                                     ^^^ `col` resolves to `not-here`
"
    );
}

#[test]
fn invalid_def_impl_err() {
    let defs = &mut Definitions::new();
    process_definition(
        "def wrong-filter (col) { filter > $col }",
        Location::Shell,
        None,
        defs,
    )
    .unwrap();
    let x = process_w_table("wrong-filter not-here", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Semantics Error: `cmp` does not support `TableRow` input data
--> <ogma>:14
 | def > (rhs) { cmp $rhs | = Ord::Gt }
 |               ^^^
--> shell:32
 | def wrong-filter (col) { filter > $col }
 |                                 ^^^^^^ invoked here
--> shell:25
 | def wrong-filter (col) { filter > $col }
 |                          ^^^^^^^^^^^^^^ invoked here
--> shell:0
 | wrong-filter not-here
 | ^^^^^^^^^^^^^^^^^^^^^ invoked here
--> help: use `cmp --help` to view requirements. consider implementing `def cmp`
"
    );
}

#[test]
fn nested_accumulation_soundness() {
    let defs = &Definitions::new();
    let x = process_w_nil(
        "range 1 10 | append { range 1 11 | fold 0 { + $row.i } }",
        defs,
    );
    let mut exp = vec![vec![o("i"), o("_append1")]];
    exp.extend((1..10).map(|i| vec![n(i), n(55)]).collect::<Vec<_>>());
    check_is_table(x, exp);
}

#[test]
fn parallelised_variable_soundness() {
    let defs = &Definitions::new();
    let x = process_w_nil("range 1 50 | append { get i | let $x | + $x $x }", defs);
    let mut exp = vec![vec![o("i"), o("_append1")]];
    exp.extend((1..50).map(|i| vec![n(i), n(i * 3)]).collect::<Vec<_>>());
    check_is_table(x, exp);
}

#[test]
fn no_padding() {
    let d = &mut Definitions::default();
    let f = |s| process_w_table(s, d);
    assert_eq!(
        f("filter { get first | eq 1 }"),
        f("filter {get first|eq 1}")
    );
    assert_eq!(
        f("append { get first | if { = 0 } { + 100 } { - 100 } }"),
        f("append{get first|if{= 0}{+ 100}{- 100}}")
    );

    let mut f = |s| process_definition(s, Location::Shell, None, d).is_ok();
    assert!(f("def-ty Point {x:Num y:Num}"));
    assert!(f("def-ty Ord2::Lt|Eq{x:Num y:Num}|Gt"));
    assert!(f("def ls-files(){ls|filter type > f}"));
}

#[test]
fn def_argument_resolving_soundness() {
    let defs = &mut Definitions::new();
    process_definition("def foo (x) { \\ 5 | + $x }", Location::Shell, None, defs).unwrap();

    let x = process_w_nil("\\ 1 | foo {+ 1}", defs);
    assert_eq!(x, Ok(Value::Num(7.into())));

    let x = process_w_nil("\\ 1 | let $x | \\ 2 | foo { \\ $x | + 1 } ", defs);
    assert_eq!(x, Ok(Value::Num(7.into())));

    process_definition(
        "def foo (x:Expr) { \\ 5 | + $x }",
        Location::Shell,
        None,
        defs,
    )
    .unwrap();
    let x = process_w_nil("\\ 1 | foo {+ 1}", defs);
    assert_eq!(x, Ok(Value::Num(11.into())));
}

#[test]
fn def_argument_resolving_soundness2() {
    let defs = &mut Definitions::new();
    process_definition(
        "def foo (x:Expr) { \\ 5 | + $x }",
        Location::Shell,
        None,
        defs,
    )
    .unwrap();
    let x = process_w_nil("\\ 1 | let $x | \\ 2 | foo {\\ $x | + 1}", defs);
    assert_eq!(x, Ok(Value::Num(7.into())));
    let x = process_w_nil("\\ 1 | let $a | \\ 2 | foo {\\ $a | + 1}", defs);
    assert_eq!(x, Ok(Value::Num(7.into())));

    process_definition(
        "def foo (c x:Expr) { filter $c $x }",
        Location::Shell,
        None,
        defs,
    )
    .unwrap();
    let x = process_w_table("let $x | \\ 0 | let $n | \\ $x | foo 'first' > $n", defs);
    check_is_table(
        x,
        vec![
            vec![o("first"), o("snd"), o("Heading 3")],
            vec![n(1), n(20), o("b")],
        ],
    );
}
