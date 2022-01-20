use crate::prelude::*;
use ::libs::{colored::*, divvy::ProgressTx};
use ::table::Entry::*;
use ast::*;
use err::*;
use lang::{defs::*, help::*, syntax::parse::expression};
use print::*;
use rt::{bat::*, process_expression};
use std::{iter::*, path::*};
use HelpParameter::*;


#[test]
fn table_printing() {
    let mut table = Table::default();
    let mut wtr = Vec::new();

    // empty table
    print_table(&table, &mut wtr).unwrap();
    assert_eq!(
        std::str::from_utf8(&wtr).unwrap().to_string(),
        format!("{}\n", "table is empty".bright_yellow())
    );

    let t = table.make_mut();
    // do table on bounds of constraints (30row, 7col)
    t.add_row(
        once(o("idx"))
            .chain(once(o("one")))
            .chain(once(o("two")))
            .chain(once(o("three")))
            .chain(once(o("four")))
            .chain(once(o("five")))
            .chain(once(o("six"))),
    );
    t.add_rows((0..29).map(|n| once(Num(n.into())).chain(repeat_with(|| Nil).take(6))));

    wtr.clear();
    print_table(&table, &mut wtr).unwrap();
    check_table(
        &wtr,
        "┌──────┬─────┬─────┬───────┬──────┬──────┬─────┐
│ idx  ┆ one ┆ two ┆ three ┆ four ┆ five ┆ six │
╞══════╪═════╪═════╪═══════╪══════╪══════╪═════╡
│ 0    ┆ -   ┆ -   ┆ -     ┆ -    ┆ -    ┆ -   │
│ 1.0  ┆ -   ┆ -   ┆ -     ┆ -    ┆ -    ┆ -   │
│ 2.0  ┆ -   ┆ -   ┆ -     ┆ -    ┆ -    ┆ -   │
│ 3.0  ┆ -   ┆ -   ┆ -     ┆ -    ┆ -    ┆ -   │
│ 4.0  ┆ -   ┆ -   ┆ -     ┆ -    ┆ -    ┆ -   │
│ 5.0  ┆ -   ┆ -   ┆ -     ┆ -    ┆ -    ┆ -   │
│ 6.0  ┆ -   ┆ -   ┆ -     ┆ -    ┆ -    ┆ -   │
│ 7.0  ┆ -   ┆ -   ┆ -     ┆ -    ┆ -    ┆ -   │
│ 8.0  ┆ -   ┆ -   ┆ -     ┆ -    ┆ -    ┆ -   │
│ 9.0  ┆ -   ┆ -   ┆ -     ┆ -    ┆ -    ┆ -   │
│ 10.0 ┆ -   ┆ -   ┆ -     ┆ -    ┆ -    ┆ -   │
│ 11.0 ┆ -   ┆ -   ┆ -     ┆ -    ┆ -    ┆ -   │
│ 12.0 ┆ -   ┆ -   ┆ -     ┆ -    ┆ -    ┆ -   │
│ 13.0 ┆ -   ┆ -   ┆ -     ┆ -    ┆ -    ┆ -   │
│ 14.0 ┆ -   ┆ -   ┆ -     ┆ -    ┆ -    ┆ -   │
│ 15.0 ┆ -   ┆ -   ┆ -     ┆ -    ┆ -    ┆ -   │
│ 16.0 ┆ -   ┆ -   ┆ -     ┆ -    ┆ -    ┆ -   │
│ 17.0 ┆ -   ┆ -   ┆ -     ┆ -    ┆ -    ┆ -   │
│ 18.0 ┆ -   ┆ -   ┆ -     ┆ -    ┆ -    ┆ -   │
│ 19.0 ┆ -   ┆ -   ┆ -     ┆ -    ┆ -    ┆ -   │
│ 20.0 ┆ -   ┆ -   ┆ -     ┆ -    ┆ -    ┆ -   │
│ 21.0 ┆ -   ┆ -   ┆ -     ┆ -    ┆ -    ┆ -   │
│ 22.0 ┆ -   ┆ -   ┆ -     ┆ -    ┆ -    ┆ -   │
│ 23.0 ┆ -   ┆ -   ┆ -     ┆ -    ┆ -    ┆ -   │
│ 24.0 ┆ -   ┆ -   ┆ -     ┆ -    ┆ -    ┆ -   │
│ 25.0 ┆ -   ┆ -   ┆ -     ┆ -    ┆ -    ┆ -   │
│ 26.0 ┆ -   ┆ -   ┆ -     ┆ -    ┆ -    ┆ -   │
│ 27.0 ┆ -   ┆ -   ┆ -     ┆ -    ┆ -    ┆ -   │
│ 28.0 ┆ -   ┆ -   ┆ -     ┆ -    ┆ -    ┆ -   │
└──────┴─────┴─────┴───────┴──────┴──────┴─────┘
",
    );

    let t = table.make_mut();
    // do table outside bounds of constraints (21row, 8col)
    t.add_row(once(Num(29.into())).chain(repeat_with(|| Nil).take(7)));

    wtr.clear();
    print_table(&table, &mut wtr).unwrap();
    check_table(
        &wtr,
        "┌────────────────┬─────┬─────┬───────────────┬──────┬─────┬─────┐
│ idx            ┆ one ┆ two ┆ 2 cols elided ┆ five ┆ six ┆ -   │
╞════════════════╪═════╪═════╪═══════════════╪══════╪═════╪═════╡
│ 0              ┆ -   ┆ -   ┆ ...           ┆ -    ┆ -   ┆ -   │
│ 1.0            ┆ -   ┆ -   ┆ ...           ┆ -    ┆ -   ┆ -   │
│ 2.0            ┆ -   ┆ -   ┆ ...           ┆ -    ┆ -   ┆ -   │
│ 3.0            ┆ -   ┆ -   ┆ ...           ┆ -    ┆ -   ┆ -   │
│ 4.0            ┆ -   ┆ -   ┆ ...           ┆ -    ┆ -   ┆ -   │
│ 20 rows elided ┆ ... ┆ ... ┆ ...           ┆ ...  ┆ ... ┆ ... │
│ 25.0           ┆ -   ┆ -   ┆ ...           ┆ -    ┆ -   ┆ -   │
│ 26.0           ┆ -   ┆ -   ┆ ...           ┆ -    ┆ -   ┆ -   │
│ 27.0           ┆ -   ┆ -   ┆ ...           ┆ -    ┆ -   ┆ -   │
│ 28.0           ┆ -   ┆ -   ┆ ...           ┆ -    ┆ -   ┆ -   │
│ 29.0           ┆ -   ┆ -   ┆ ...           ┆ -    ┆ -   ┆ -   │
└────────────────┴─────┴─────┴───────────────┴──────┴─────┴─────┘
",
    );
}

fn check_table(table: &[u8], chk: &str) {
    let table = std::str::from_utf8(table).unwrap();
    println!("{}", table);
    assert_eq!(table, chk);
}

#[test]
fn help_msg() {
    let h = HelpMessage {
        desc: "this is a description".into(),
        params: vec![Required("required1".into()), Required("req2".into())],
        ..HelpMessage::new("cmd-name")
    };
    let s = help_as_error(&h).to_string();
    assert_eq!(
        &s,
        "Help: `cmd-name`
--> shell:0
 | this is a description
 | 
 | Usage:
 |  => cmd-name required1 req2
"
    );

    let h = HelpMessage {
        desc: "this is a description".into(),
        examples: vec![
            HelpExample {
                desc: "example 1",
                code: "cmd-name this is a thingo",
            },
            HelpExample {
                desc: "example 2",
                code: "cmd-name ",
            },
        ],
        ..HelpMessage::new("cmd-name")
    };
    let s = help_as_error(&h).to_string();
    assert_eq!(
        &s,
        "Help: `cmd-name`
--> shell:0
 | this is a description
 | 
 | Usage:
 |  => cmd-name
 | 
 | Examples:
 |  example 1
 |  => cmd-name this is a thingo
 | 
 |  example 2
 |  => cmd-name 
"
    );
}

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

// ###### COMMANDS #############################################################
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

fn print_help(src: &str, defs: &Definitions) -> String {
    let x = eng::handle_help(&expression(src, Location::Shell, defs).unwrap(), defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    x
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

// ------ Definitions ----------------------------------------------------------
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
            "┌────────────────┬─────────────┬───────┬──────────┬──────┬────────────────────────────┐
│ name           ┆ category    ┆ input ┆ location ┆ line ┆ code                       │
╞════════════════╪═════════════╪═══════╪══════════╪══════╪════════════════════════════╡
│ !=             ┆ cmp         ┆ -     ┆ <ogma>   ┆ -    ┆ != (rhs) { eq $rhs | not } │
│ *              ┆ arithmetic  ┆ -     ┆ <ogma>   ┆ -    ┆ -                          │
│ +              ┆ arithmetic  ┆ -     ┆ <ogma>   ┆ -    ┆ -                          │
│ -              ┆ arithmetic  ┆ -     ┆ <ogma>   ┆ -    ┆ -                          │
│ .              ┆ pipeline    ┆ -     ┆ <ogma>   ┆ -    ┆ -                          │
│ 61 rows elided ┆ ...         ┆ ...   ┆ ...      ┆ ...  ┆ ...                        │
│ take           ┆ morphism    ┆ -     ┆ <ogma>   ┆ -    ┆ -                          │
│ to-str         ┆ pipeline    ┆ -     ┆ <ogma>   ┆ -    ┆ -                          │
│ typify         ┆ diagnostics ┆ -     ┆ <ogma>   ┆ -    ┆ -                          │
│ ×              ┆ arithmetic  ┆ -     ┆ <ogma>   ┆ -    ┆ -                          │
│ ÷              ┆ arithmetic  ┆ -     ┆ <ogma>   ┆ -    ┆ -                          │
└────────────────┴─────────────┴───────┴──────────┴──────┴────────────────────────────┘
"
        );
    } else {
        panic!("table printing failed");
    }
}

#[test]
fn add_from_str_and_clearing() {
    use lang::defs::construct_def_table;

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
            help_msg: None
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
        r#"Semantics Error: expecting argument with type `Number`, found `String`
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
        r#"Semantics Error: expecting argument with type `Number`, found `Bool`
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

// ------ User Type Interactions -----------------------------------------------
// as an example we can test the struct defining and implementing custom add
#[test]
fn point_construction() {
    // this is a verbose check for typedefs, just as an initial check
    let defs = &with_dummy_defs();
    let x = process_w_nil("Point 1 { \\ 3 }", defs);
    if let Ok(Value::Ogma(x)) = x {
        assert_eq!(x.ty.name().str(), "Point");
        assert_eq!(&x.data, &[Value::Num(1.into()), Value::Num(3.into())]);
    } else {
        panic!("not right variant")
    }

    let x = process_w_nil("\\ 1 | let $x | \\ 3 | let $y | Point $x $y", defs);
    if let Ok(Value::Ogma(x)) = x {
        assert_eq!(x.ty.name().str(), "Point");
        assert_eq!(&x.data, &[Value::Num(1.into()), Value::Num(3.into())]);
    } else {
        panic!("not right variant")
    }
}

#[test]
fn invalid_point_construction() {
    let defs = &with_dummy_defs();
    let x = process_w_nil("Point 1", defs).unwrap_err().to_string();
    assert_eq!(
        &x,
        "Semantics Error: expecting more than 1 arguments
--> shell:0
 | Point 1
 | ^^^^^^^ expecting additional argument(s)
--> help: try using the `--help` flag to view requirements
"
    );
}

#[test]
fn point_construction_help() {
    let defs = &with_dummy_defs();
    let x = process_w_nil("Point --help", defs).unwrap_err().to_string();
    assert_eq!(
        &x,
        "Help: `Point`
--> shell:0
 | initialise a `Point`
 | 
 | Usage:
 |  => Point x:Number y:Number
"
    );
}

#[test]
fn getting_a_field() {
    let defs = &with_dummy_defs();
    let x = process_w_nil("Point 1 3 | get x", defs);
    assert_eq!(x, Ok(Value::Num(1.into())));
    let x = process_w_nil("Point 1 3 | get y", defs);
    assert_eq!(x, Ok(Value::Num(3.into())));
}

#[test]
fn field_does_not_exist() {
    let defs = &with_dummy_defs();
    let x = process_w_nil("Point 1 3 | get z", defs)
        .unwrap_err()
        .to_string();
    assert_eq!(
        &x,
        "Semantics Error: `Point` does not contain field `z`
--> shell:16
 | Point 1 3 | get z
 |                 ^ `z` not found
"
    );
}

// ------ bat - module processing testing --------------------------------------
#[test]
fn batch_success_testing() {
    use rt::bat::*;
    use Outcome::*;

    let p = &ProgressTx::dummy();
    let (root, wd) = paths();

    let code = r#"def foo-bar () { \5 }

# Testing a comment
foo-bar | + 5

def-ty Foo { x:Num }"#;

    let batch = parse_str(code);
    let p = |b| {
        process(&b, root, wd, p, Default::default())
            .into_iter()
            .map(|x| x.0)
            .collect::<Vec<_>>()
    };
    assert_eq!(p(batch), vec![Success, Success, Success]);

    let batch = parse_str(code);
    assert_eq!(p(batch), vec![Success, Success, Success]);
}

#[test]
fn batch_fail_testing() {
    use rt::bat::*;
    use Outcome::*;

    let p = &ProgressTx::dummy();
    let (root, wd) = paths();

    let code = r#"def foo-bar () { \5 }

# This should fail
foo-bar | + 5 | - 'foo'

def-ty Foo { x:Num y: }"#;

    fn print<T>(o: (Outcome, T)) -> String {
        match o {
            (Failed(e), _) => e.to_string(),
            _ => panic!(),
        }
    }

    let batch = Batch {
        parallelise: false,
        fail_fast: true,
        ..parse_str(code)
    };
    let mut x = process(&batch, root, wd, p, Default::default()).into_iter();
    assert!(matches!(x.next(), Some((Success, _))));
    assert!(matches!(x.next(), Some((Outstanding, _))));
    assert_eq!(
        &x.next().map(print).unwrap(),
        "Parsing Error: could not parse input line
--> '' - line 6:21
 | def-ty Foo { x:Num y: }
 |                      ^ missing a valid type specifier: `field:Type`
"
    );

    let batch = parse_str(code);
    let mut x = process(&batch, root, wd, p, Default::default()).into_iter();
    assert!(matches!(x.next(), Some((Success, _))));
    assert_eq!(
        &x.next().map(print).unwrap(),
        r#"Semantics Error: expecting argument with type `Number`, found `String`
--> '' - line 4:19
 | foo-bar | + 5 | - 'foo'
 |                    ^^^ this argument returns type `String`
--> help: commands may require specific argument types, use `--help` to view requirements
"#
    );
    assert_eq!(
        &x.next().map(print).unwrap(),
        "Parsing Error: could not parse input line
--> '' - line 6:21
 | def-ty Foo { x:Num y: }
 |                      ^ missing a valid type specifier: `field:Type`
"
    );
}

// ------ Benchmark ------------------------------------------------------------
#[test]
fn benchmark_help_msg() {
    let src = "benchmark --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `benchmark`
--> shell:0
 | time the expression evaluation
 | pipes <input> to <expr>
 | 
 | Usage:
 |  => benchmark expr
 | 
 | Examples:
 |  time loading in a file
 |  => benchmark { open file.csv }
 | 
 |  time filtering a table
 |  => \\ file.csv | benchmark filter = col 1
"
    );
}

#[test]
fn benchmark_test() {
    let defs = &Definitions::new();
    // filter out the row to just get the headers
    let x = process_w_num(
        "eq 3 | benchmark and { \\ 2 | > 1 } | filter duration = 2",
        defs,
    );
    let exp = vec![vec![
        o("duration"),
        o("seconds"),
        o("milliseconds"),
        o("microseconds"),
    ]];
    check_is_table(x, exp);
}

// ------ Booleans -------------------------------------------------------------
#[test]
fn boolean_test() {
    let defs = &Definitions::new();
    let x = process_w_nil("\\ #t", defs);
    assert_eq!(x, Ok(Value::Bool(true)));
    let x = process_w_nil("\\ #f", defs);
    assert_eq!(x, Ok(Value::Bool(false)));
    let x = process_w_nil("\\#t", defs);
    assert_eq!(x, Ok(Value::Bool(true)));
    let x = process_w_nil("\\#f", defs);
    assert_eq!(x, Ok(Value::Bool(false)));
    let x = process_w_nil("\\ #f | = #t", defs);
    assert_eq!(x, Ok(Value::Bool(false)));

    let x = process_w_nil("\\ #tf", defs).unwrap_err().to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        r#"Parsing Error: could not parse input line
--> shell:3
 | \ #tf
 |    ^^ special literals only have one character
"#
    );
}

// ------ Infinity -------------------------------------------------------------

#[test]
fn inf_testing() {
    let defs = &Definitions::new();
    let inf = Ok(Value::Num(std::f64::INFINITY.into()));
    let x = process_w_num("+ ∞", defs);
    assert_eq!(x, inf);
    let x = process_w_num("+ inf", defs);
    assert_eq!(x, inf);
    let x = process_w_num("+ - inf", defs);
    assert_eq!(x, Ok(Value::Num(std::f64::NEG_INFINITY.into())));
}

// ------ Nan ------------------------------------------------------------------
#[test]
fn nan_testing() {
    let defs = &Definitions::new();
    let nan = Ok(Value::Num(std::f64::NAN.into()));
    let x = process_w_num("+ nan", defs);
    assert_eq!(x, nan);
    let x = process_w_num("- nan", defs);
    assert_eq!(x, nan);
}

// ------ Nil ------------------------------------------------------------------
#[test]
fn nil_test() {
    let defs = &Definitions::new();
    let x = process_w_nil("\\ #n", defs);
    assert_eq!(x, Ok(Value::Nil));
    let x = process_w_nil("\\ #n | = #n", defs);
    assert_eq!(x, Ok(Value::Bool(true)));
    let x = process_w_nil("\\ #n | cmp #n | = Ord::Eq", defs);
    assert_eq!(x, Ok(Value::Bool(true)));
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
