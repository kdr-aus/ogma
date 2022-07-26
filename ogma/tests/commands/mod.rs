use libs::divvy::Str;
use ogma::{
    lang::{ast::*, *},
    output::*,
    rt::*,
    *,
};
use std::{path::Path, sync::Arc};
use table::Entry::{self, Nil};

type Result<T> = std::result::Result<T, ogma::Error>;

mod annotation;
mod arithmetic;
mod cmp;
mod definitions;
mod diagnostics;
mod errs;
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
    let x = rt::handle_help(
        &lang::parse::expression(src, Location::Shell, defs).unwrap(),
        defs,
    )
    .unwrap_err()
    .to_string();
    println!("{}", x);
    x
}

fn with_dummy_defs() -> Definitions {
    let mut defs = Definitions::new();
    assert_eq!(
        process_definition("def num5 () { \\ 5 }", Location::Shell, None, &mut defs),
        Ok((Value::Nil, None))
    );
    assert_eq!(
        process_definition(
            "def gt10 (n) { get $n | > 10 }",
            Location::file("some/file", 12),
            None,
            &mut defs
        ),
        Ok((Value::Nil, None))
    );
    assert_eq!(
        process_definition(
            "def pos-tab () { filter first > 0 }",
            Location::file("source-file", 101),
            None,
            &mut defs
        ),
        Ok((Value::Nil, None))
    );
    assert_eq!(
        process_definition(
            "def-ty Point { x:Num y:Num }",
            Location::Shell,
            None,
            &mut defs,
        ),
        Ok((Value::Nil, None))
    );
    assert_eq!(
        process_definition(
            "def ls-files () { ls | filter type > f }",
            Location::Shell,
            None,
            &mut defs
        ),
        Ok((Value::Nil, None))
    );

    defs
}

fn is_ord(res: Result<Value>, s: &'static str, idx: usize) {
    if let Err(e) = &res {
        println!("{}", e);
    }
    let res = res.unwrap();
    assert!(
        matches!(res, Value::Ogma(y) if y.variant_idx() == idx),
        "{}",
        s
    );
}
fn is_lt(res: Result<Value>) {
    is_ord(res, "expecting Ord::Lt", 0);
}
fn is_eq(res: Result<Value>) {
    is_ord(res, "expecting Ord::Eq", 1);
}
fn is_gt(res: Result<Value>) {
    is_ord(res, "expecting Ord::Gt", 2);
}

// ------ Multiline Expressions ------------------------------------------------
#[test]
fn multiline_expr() {
    let d = &Definitions::new();

    let x = process_w_nil(
        "
\\ 3 | * 4 |
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
        "\\ 3 | * 4 |
    * 'foo'",
        d,
    )
    .unwrap_err()
    .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Semantics Error: expecting argument with output type `Number`, found `String`
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
        "Typing Error: Type resolution failed. Conflicting inferred type
--> shell:0
 | filter {
 |     get snd | + 1
 | }
 | ^^^^^^^^^^^^^^^^^ this node has input type `Nil`
--> shell:0
 | filter {
 | ^^^^^^ but this node is inferred to use inputs: Table String
",
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
        "Typing Error: Type resolution failed. Conflicting obligation type
--> shell:14
 |     get snd | + 1
 |               ^ this node returns a `Number`
--> shell:7
 | filter {
 |     get snd | + 1
 | }
 | ^^^^^^^^^^^^^^^^^ but this node is obliged to return `Bool`
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
        "Typing Error: Type resolution failed. Conflicting obligation type
--> shell:4
 |     - 2 }
 |     ^ this node returns a `Number`
--> shell:0
 | { + 1 |
 |     - 2 }
 | ^^^^^^^^^ but this node is obliged to return `Bool`
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
        r#"Semantics Error: not expecting flags: `foo`, `bar`
--> shell:6
 | \ 5 --foo --bar
 |       ^^^ flag not supported
--> shell:12
 | \ 5 --foo --bar
 |             ^^^ flag not supported
--> help: try using the `--help` flag to view requirements
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
        r#"Unknown Command: operation `testing` not defined
--> shell:6
 | \ 5 { testing 2 { foo  bar } }
 |       ^^^^^^^ `testing` not defined for input `<any>`
--> help: view a list of definitions using `def --list`
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

#[test]
fn incorrect_input_syntax() {
    let defs = &Definitions::new();

    let x = process_w_nil("\\ file.csv | \\", defs)
        .unwrap_err()
        .to_string();
    assert_eq!(
        &x,
        r#"Semantics Error: expecting more than 0 arguments
--> shell:13
 | \ file.csv | \
 |              ^ expecting additional argument(s)
--> help: try using the `--help` flag to view requirements
"#
    );
}

#[test]
fn no_cmd_defined() {
    let defs = &Definitions::new();

    let x = process_w_table("undefined", defs).unwrap_err().to_string();
    assert_eq!(
        &x,
        "Unknown Command: operation `undefined` not defined
--> shell:0
 | undefined
 | ^^^^^^^^^ `undefined` not defined for input `<any>`
--> help: view a list of definitions using `def --list`
"
    );

    // try nested one
    let x = process_w_table("\\ file.csv | undefined", defs)
        .unwrap_err()
        .to_string();
    assert_eq!(
        &x,
        r#"Unknown Command: operation `undefined` not defined
--> shell:13
 | \ file.csv | undefined
 |              ^^^^^^^^^ `undefined` not defined for input `<any>`
--> help: view a list of definitions using `def --list`
"#
    );
}

#[test]
fn variables_not_existing() {
    let defs = &Definitions::new();

    let x = process_w_table("\\ $t", defs).unwrap_err().to_string();
    println!("{x}");
    assert_eq!(
        &x,
        r#"Semantics Error: variable `t` does not exist
--> shell:3
 | \ $t
 |    ^ `t` not in scope
--> help: variables must be in scope
          variables can be defined using the `let` command
"#
    );

    let x = process_w_table("let $a | \\ $t", defs).unwrap_err().to_string();
    println!("{x}");
    assert_eq!(
        &x,
        r#"Semantics Error: variable `t` does not exist
--> shell:12
 | let $a | \ $t
 |             ^ `t` not in scope
--> help: variables must be in scope
          variables can be defined using the `let` command
"#
    );

    let x = process_w_table("append { get $col }", defs).unwrap_err().to_string();
    println!("{x}");
    assert_eq!(
        &x,
        "Semantics Error: variable `col` does not exist
--> shell:14
 | append { get $col }
 |               ^^^ `col` not in scope
--> help: variables must be in scope
          variables can be defined using the `let` command
"
    );

    let x = process_w_table("append { let $a | get $col }", defs).unwrap_err().to_string();
    println!("{x}");
    assert_eq!(
        &x,
        "Semantics Error: variable `col` does not exist
--> shell:23
 | append { let $a | get $col }
 |                        ^^^ `col` not in scope
--> help: variables must be in scope
          variables can be defined using the `let` command
"
    );
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
 |                         ^^^^^^^^^^^^^^ `test-recursion` not defined for input `<any>`
--> help: recursion is not supported.
          for alternatives, please see <https://daedalus.report/d/docs/ogma.book/11%20(no)%20recursion.md?pwd-raw=docs>
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
    let x = process_w_nil(
        "range 1 50 | append { get i --Num | let $x | + $x $x }",
        defs,
    );
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
        "def foo (c x:Expr) { filter --Num $c $x }",
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

#[test]
fn unrecognised_literal() {
    let x = process_w_nil("\\ #z", &Definitions::new())
        .unwrap_err()
        .to_string();
    println!("{}", x);

    assert_eq!(
        &x,
        "Semantics Error: special literal `z` not supported
--> shell:2
 | \\ #z
 |   ^^ `z` not supported
"
    );
}

#[test]
fn get_output_inference_be_smarter() {
    let x = process_w_table("append { get first | * 2 }", &Definitions::new());

    check_is_table(
        x,
        vec![
            vec![o("first"), o("snd"), o("Heading 3"), o("_append1")],
            vec![n(0), n(3), o("a"), n(0)],
            vec![n(1), n(20), o("b"), n(2)],
            vec![n(-30), n(100), o("z"), n(-60)],
        ],
    );
}

#[test]
fn locals_graph_change_bug() {
    let x = process_w_table(
        "skip 1 | append --value { get:Num first | * 1e6 | let $n | \\ 'mkt-cap ' | + $v }",
        &Definitions::new(),
    )
    .unwrap_err()
    .to_string();
    println!("{}", x);

    assert_eq!(
        &x,
        "Semantics Error: variable `v` does not exist
--> shell:77
 | skip 1 | append --value { get:Num first | * 1e6 | let $n | \\ 'mkt-cap ' | + $v }
 |                                                                              ^ `v` not in scope
--> help: variables must be in scope
          variables can be defined using the `let` command
"
    );
}

#[test]
fn def_locals_not_type_resolving() {
    let defs = &mut Definitions::new();

    process_definition(
        "def foo (n:Num) { \\ $n | + 2 }",
        Location::Shell,
        None,
        defs,
    )
    .unwrap();

    let x = process_w_nil("\\ 3 | let $n | foo $n", defs);
    assert_eq!(x, Ok(Value::Num(5.into())));

    let x = process_w_nil("\\ 'a' | let $n | foo $n", defs)
        .unwrap_err()
        .to_string();
    println!("{x}");
    assert_eq!(
        &x,
        "Semantics Error: expecting argument with output type `Number`, found `String`
--> shell:22
 | \\ 'a' | let $n | foo $n
 |                       ^ this argument returns type `String`
--> help: commands may require specific argument types, use `--help` to view requirements
"
    );

    // Check bug #80
    process_definition("def foo (bar:Str) { \\ #t }", Location::Shell, None, defs).unwrap();

    let x = process_w_nil("foo { \\ 'foo' | + 'zog' }", defs);
    assert_eq!(x, Ok(Value::Bool(true)));
}

#[test]
fn type_resolution_failure() {
    let x = process_w_nil(
        "ls | let {nth 0 get:Num size} $start {last get:Num size} $end | \\ #t",
        &Definitions::new(),
    );
    if let Err(e) = &x {
        println!("{e}");
    }
    assert_eq!(x, Ok(Value::Bool(true)));
}
