use super::*;
use ogma::common::err::*;

#[test]
fn defs_help_msg() {
    let src = "def --help";
    let defs = &mut Definitions::new();
    let x = process_definition(src, Location::Shell, None, defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Help: `def`
--> shell:0
 | ---- Input Type: <any> ----
 | define a command that encapsulates an expression
 | def has specialised syntax which takes variable params: ( )
 | 
 | Usage:
 |  => def name [Ty] ([param1[:Ty|Expr]] [param2[:Ty|Expr]] ...) { expr }
 | 
 | Flags:
 |  --list: list the definitions as a table
 |  --load: load persistent definitions from files in daedalus folder
 |  --clear: clear all user defined definitions
 | 
 | Examples:
 |  define a command that returns the number 5
 |  => def num5 () { \\ 5 }
 | 
 |  list directory items that match a type
 |  => def list (ty) { ls | filter = type $ty }
 | 
 |  use types to better define use
 |  => def sum Table (seed:Num value:Expr) { fold $seed + $acc $value }
"
    );
}

#[test]
fn user_def_help_msg() {
    let defs = &with_dummy_defs();

    let src = "num5 --help";
    let x = print_help(src, defs);
    assert_eq!(
        &x,
        "Help: `num5`
--> shell:0
 | ---- Input Type: <any> ----
 | user defined implementation in shell
 | `def num5 () { \\ 5 }`
 | 
 | Usage:
 |  => num5
"
    );

    let src = "gt10 --help";
    let x = print_help(src, defs);
    assert_eq!(
        &x,
        "Help: `gt10`
--> shell:0
 | ---- Input Type: <any> ----
 | user defined implementation in 'some/file' - line 12
 | `def gt10 (n) { get $n | > 10 }`
 | 
 | Usage:
 |  => gt10 n
"
    );
}

#[test]
fn usr_def_table() {
    let defs = &with_dummy_defs();
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(1), n(20), o("b")],
    ];
    let x = process_w_table("pos-tab", defs);
    check_is_table(x, exp);
}

#[test]
fn usr_def_gt10() {
    let defs = &with_dummy_defs();
    let x = process_w_table("filter gt10 test", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Evaluation Error: header `test` not found in table
--> 'some/file' - line 12:20
 | def gt10 (n) { get $n | > 10 }
 |                     ^ `n` resolves to `test`
"
    );
}

#[test]
fn list_defs() {
    let defs = &mut with_dummy_defs();
    let x = process_definition("def --list", Location::Shell, None, defs);

    if let Ok((Value::Tab(x), _)) = &x {
        let mut buf = Vec::new();
        print_table(x, &mut buf).unwrap();
        let s = std::str::from_utf8(&buf).unwrap();
        println!("{}", s);

        assert_eq!(
            s,
            "┌────────────────┬─────────────┬────────┬──────────┬──────┬────────────────────────────┐
│ name           ┆ category    ┆ input  ┆ location ┆ line ┆ code                       │
╞════════════════╪═════════════╪════════╪══════════╪══════╪════════════════════════════╡
│ !=             ┆ cmp         ┆ -      ┆ <ogma>   ┆ -    ┆ != (rhs) { eq $rhs | not } │
│ *              ┆ arithmetic  ┆ Number ┆ <ogma>   ┆ -    ┆ -                          │
│ +              ┆ arithmetic  ┆ Number ┆ <ogma>   ┆ -    ┆ -                          │
│ +              ┆ arithmetic  ┆ String ┆ <ogma>   ┆ -    ┆ -                          │
│ +              ┆ arithmetic  ┆ Table  ┆ <ogma>   ┆ -    ┆ -                          │
│ 68 rows elided ┆ ...         ┆ ...    ┆ ...      ┆ ...  ┆ ...                        │
│ take           ┆ morphism    ┆ -      ┆ <ogma>   ┆ -    ┆ -                          │
│ to-str         ┆ pipeline    ┆ -      ┆ <ogma>   ┆ -    ┆ -                          │
│ typify         ┆ diagnostics ┆ -      ┆ <ogma>   ┆ -    ┆ -                          │
│ ×              ┆ arithmetic  ┆ Number ┆ <ogma>   ┆ -    ┆ -                          │
│ ÷              ┆ arithmetic  ┆ Number ┆ <ogma>   ┆ -    ┆ -                          │
└────────────────┴─────────────┴────────┴──────────┴──────┴────────────────────────────┘
"
        );
    } else {
        panic!("table printing failed");
    }
}

#[test]
fn add_from_str_and_clearing() {
    use lang::construct_def_table;

    let mut defs = with_dummy_defs();
    let mut tab = construct_def_table(&defs);

    let s = "
 def z1 () { ls }

# This is a
#multi-line comment
def z2 () { ls }";
    let t = tab.make_mut();
    // we insert just above the math symbols, as these have higher values in ordering
    let mathlen = 2;
    t.insert_row(
        t.rows_len() - mathlen,
        vec![
            o("z1"),
            o("user-defined"),
            Nil,
            o("hello"),
            n(2),
            o("z1 () { ls }"),
        ]
        .into_iter(),
    );
    t.insert_row(
        t.rows_len() - mathlen,
        vec![
            o("z2"),
            o("user-defined"),
            Nil,
            o("hello"),
            n(6),
            o("z2 () { ls }"),
        ]
        .into_iter(),
    );

    defs.add_from_str(s, Path::new("hello")).unwrap();

    // test that z2 has a doc comment
    let x = process_w_nil("z2 --help", &defs).unwrap_err().to_string();
    assert_eq!(
        &x,
        "Help: `z2`
--> shell:0
 | ---- Input Type: <any> ----
 | user defined implementation in 'hello' - line 6
 | `def z2 () { ls }`
 | 
 | This is a
 | multi-line comment
 | 
 | Usage:
 |  => z2
"
    );

    assert_eq!(tab, construct_def_table(&defs));

    // clearing all will get back to basic defs
    defs.clear(false);
    assert_eq!(
        construct_def_table(&defs),
        construct_def_table(&Definitions::new())
    );

    // clearing just files:
    defs = with_dummy_defs();
    tab = construct_def_table(&defs);
    defs.clear(true);
    {
        // simulate removing the file rows
        let mut r: Vec<usize> = tab
            .rows()
            .enumerate()
            .filter_map(|(idx, mut r)| {
                let x = r.nth(3).unwrap();
                                 if matches!(x, Entry::Obj(Value::Str(x)) if x == "location" || x == "shell" || x == "<ogma>" ) {
                                     None
                                 } else {
                                     Some(idx)
                                 }
            })
            .collect();
        r.reverse();
        let t = tab.make_mut();
        for i in r {
            t.remove_row(i);
        }
    }

    assert_eq!(construct_def_table(&defs), tab);
}

#[test]
fn add_from_multiline_str() {
    let defs = &mut Definitions::new();

    let s = "
# This is a
# multiline comment
def zog Num (x y) {
    + $x |
    * $y |
    if {= 3}
        $x
        $y
}

# Type of Ord2
def-ty Ord2 ::
Lt |
Eq { x:Num } |
Gt

def bar () {
    if {= foo}
    #t
    #f
}
";

    assert_eq!(defs.add_from_str(s, Path::new("foo")), Ok(3));

    let x = process_w_nil("zog --help", &defs).unwrap_err().to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Help: `zog`
--> shell:0
 | ---- Input Type: Number ----
 | user defined implementation in 'foo' - line 4
 | `def zog Num (x y) {
 |     + $x |
 |     * $y |
 |     if {= 3}
 |         $x
 |         $y
 | }`
 | 
 | This is a
 | multiline comment
 | 
 | Usage:
 |  => zog x y
"
    );

    let x = process_w_nil("bar --help", &defs).unwrap_err().to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Help: `bar`
--> shell:0
 | ---- Input Type: <any> ----
 | user defined implementation in 'foo' - line 18
 | `def bar () {
 |     if {= foo}
 |     #t
 |     #f
 | }`
 | 
 | Usage:
 |  => bar
"
    );
}

#[test]
fn inner_definition_error() {
    let defs = &with_dummy_defs();
    let x = process_w_table("filter gt10 not-a-header", defs); // this caused a span_start error so check that first!
    assert_eq!(
        x,
        Err(Error {
            cat: Category::Evaluation,
            desc: "header `not-a-header` not found in table".into(),
            traces: vec![Trace {
                loc: Location::file("some/file", 12),
                source: "def gt10 (n) { get $n | > 10 }".into(),
                desc: Some("`n` resolves to `not-a-header`".into()),
                start: 20,
                len: 1,
            }],
            ..Default::default()
        })
    );

    let x = x.unwrap_err().to_string();

    println!("{}", x);
    assert_eq!(
        &x,
        "Evaluation Error: header `not-a-header` not found in table
--> 'some/file' - line 12:20
 | def gt10 (n) { get $n | > 10 }
 |                     ^ `n` resolves to `not-a-header`
"
    );
}

#[test]
fn invalid_def_syntax() {
    let mut defs = Definitions::new();
    let x = process_definition("def foo bar zog () { }", Location::Shell, None, &mut defs)
        .unwrap_err()
        .to_string();
    assert_eq!(
        &x,
        "Parsing Error: could not parse input line
--> shell:12
 | def foo bar zog () { }
 |             ^^^^^^^^^^ expected `(`
"
    )
}

#[test]
fn passing_invalid_arg_to_def() {
    let defs = &mut Definitions::new();
    process_definition(
        "def test-expr-err (rhs) { \\ 5 | + $rhs }",
        Location::Shell,
        None,
        defs,
    )
    .unwrap();

    let x = process_w_table("test-expr-err 'hello'", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        r#"Semantics Error: expecting argument with output type `Number`, found `String`
--> shell:35
 | def test-expr-err (rhs) { \ 5 | + $rhs }
 |                                    ^^^ this argument returns type `String`
--> shell:0
 | test-expr-err 'hello'
 | ^^^^^^^^^^^^^^^^^^^^ invoked here
--> help: commands may require specific argument types, use `--help` to view requirements
"#
    );
    let x = process_w_table("test-expr-err { \\ 5 | > 2 }", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        r#"Semantics Error: expecting argument with output type `Number`, found `Bool`
--> shell:35
 | def test-expr-err (rhs) { \ 5 | + $rhs }
 |                                    ^^^ this argument returns type `Bool`
--> shell:0
 | test-expr-err { \ 5 | > 2 }
 | ^^^^^^^^^^^^^^^^^^^^^^^^^^^ invoked here
--> help: commands may require specific argument types, use `--help` to view requirements
"#
    );
}

#[test]
fn not_defined_err_msg() {
    let defs = &mut Definitions::new();
    process_definition("def foo Table () { \\ #t }", Location::Shell, None, defs).unwrap();
    process_definition("def foo Num () { \\ #t }", Location::Shell, None, defs).unwrap();

    let x = process_w_nil("foo", defs).unwrap_err().to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Unknown Command: operation `foo` not defined
--> shell:0
 | foo
 | ^^^ `foo` not defined for input `Nil`
--> help: `foo` is implemented for the following input types: Table Number
"
    );
}
