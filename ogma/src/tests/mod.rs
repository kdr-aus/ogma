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
            "┌────────────────┬────────────┬───────┬──────────┬──────┬────────────────────────────┐
│ name           ┆ category   ┆ input ┆ location ┆ line ┆ code                       │
╞════════════════╪════════════╪═══════╪══════════╪══════╪════════════════════════════╡
│ !=             ┆ cmp        ┆ -     ┆ <ogma>   ┆ -    ┆ != (rhs) { eq $rhs | not } │
│ *              ┆ arithmetic ┆ -     ┆ <ogma>   ┆ -    ┆ -                          │
│ +              ┆ arithmetic ┆ -     ┆ <ogma>   ┆ -    ┆ -                          │
│ -              ┆ arithmetic ┆ -     ┆ <ogma>   ┆ -    ┆ -                          │
│ .              ┆ pipeline   ┆ -     ┆ <ogma>   ┆ -    ┆ -                          │
│ 60 rows elided ┆ ...        ┆ ...   ┆ ...      ┆ ...  ┆ ...                        │
│ sort-by        ┆ morphism   ┆ -     ┆ <ogma>   ┆ -    ┆ -                          │
│ take           ┆ morphism   ┆ -     ┆ <ogma>   ┆ -    ┆ -                          │
│ to-str         ┆ pipeline   ┆ -     ┆ <ogma>   ┆ -    ┆ -                          │
│ ×              ┆ arithmetic ┆ -     ┆ <ogma>   ┆ -    ┆ -                          │
│ ÷              ┆ arithmetic ┆ -     ┆ <ogma>   ┆ -    ┆ -                          │
└────────────────┴────────────┴───────┴──────────┴──────┴────────────────────────────┘
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
            traces: vec![ErrorTrace {
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

// ------ Abs ------------------------------------------------------------------
#[test]
fn abs_help_msg() {
    let src = "abs --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `abs`
--> shell:0
 | user defined implementation in <ogma>
 | `def abs Num () { if {< 0} {* -1} #i }`
 | take the absolute of a number
 | 
 | Usage:
 |  => abs
"
    );
}

#[test]
fn abs_testing() {
    let defs = &Definitions::new();
    let x = process_w_num("abs", defs);
    assert_eq!(x, Ok(Value::Num(3.into())));
    let x = process_w_num("* -1 3 | abs", defs);
    assert_eq!(x, Ok(Value::Num(9.into())));
}

// ------ Add ------------------------------------------------------------------
#[test]
fn add_help_msg() {
    let src = "+ --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `+`
--> shell:0
 | add arguments together
 | if input is a Table, concat or join additional tables
 | -variadic-: more than one argument can be specified
 | 
 | Usage:
 |  => + args..
 | 
 | Flags:
 |  --cols: join tables (append columns)
 |  --union: expand table to capture all data (default)
 |  --intersect: use minimum size of table; min rows for --cols, min cols for concat rows
 | 
 | Examples:
 |  add 2 to 1
 |  => \\ 1 | + 2
 | 
 |  add multiple numbers together
 |  => + 1 2 3 4 5
 | 
 |  add two tables together, concatenating rows
 |  => range 0 10 | + range 10 20
 | 
 |  index filesystem items, shrink table to min rows
 |  => range 0 1000 | + --cols --intersect ls
"
    );
}

#[test]
fn add_testing() {
    let defs = &Definitions::new();
    let x = process_w_num("+ 101 ", defs);
    assert_eq!(x, Ok(Value::Num(104.into())));
    let x = process_w_num("+ 3 | +  { + 2 | + 2 } ", defs);
    assert_eq!(x, Ok(Value::Num(16.into())));
    // ^^ this technically works but is not obvious.
    // process_w_num starts with 3, then + 3 = 6, which is then fed into the expr.
    // expr is 6 + 2 + 2 = 10. This is evaluated so the + expr becomes +10, and the input
    // is 6 so 6 + 10 = 16!
    let x = process_w_num("+ 101 202", defs);
    assert_eq!(x, Ok(Value::Num(306.into())));
    let x = process_w_num("let $x | + 101 202", defs);
    assert_eq!(x, Ok(Value::Num(306.into())));
    // ^^ let $x sends through 3
    let x = process_w_num("let $x | \\ 0 | + 1 2 $x", defs);
    assert_eq!(x, Ok(Value::Num(6.into()))); // 0 + 1 + 2 + 3
}

#[test]
fn add_str_testing() {
    let defs = &Definitions::new();
    let x = process_w_str("+ World ", defs);
    assert_eq!(x, Ok(Value::Str("HelloWorld".into())));
    let x = process_w_str("+ Zog ' World' ", defs);
    assert_eq!(x, Ok(Value::Str("HelloZog World".into())));
}

#[test]
fn point_adding_overload() {
    let defs = &mut with_dummy_defs();
    let x = process_definition("def + Point (rhs) { Point { get x | + { \\ $rhs | get x } } { get y | + { \\ $rhs | get y } } }", Location::Shell, None, defs);
    assert_eq!(x, Ok((Value::Nil, None)));

    let x = process_w_nil("Point 1 3 | + Point -2 2 | get x", defs);
    assert_eq!(x, Ok(Value::Num((-1).into())));
    let x = process_w_nil("Point 1 3 | + Point -2 2 | get y", defs);
    assert_eq!(x, Ok(Value::Num(5.into())));
}

#[test]
fn table_adding_by_row() {
    let defs = &Definitions::new();

    macro_rules! union_same {
        ($($f:literal)*) => {{
            $(
    let s = concat!("+ ",$f," range 1 5");
    println!("expr: '{}'", s);
    let x = process_w_table(s, defs);
    let mut exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    exp.extend((1..5).map(|x| vec![n(x)]));
    check_is_table(x, exp);

    let s = concat!("let $x | range 1 5 | + ",$f," $x");
    println!("expr: '{}'", s);
    let x = process_w_table(s, defs);
    let mut exp = vec![
        vec![o("i"), o("snd"), o("Heading 3")],
    ];
    exp.extend((1..5).map(|x| vec![n(x)]));
        exp.extend(vec![
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ].into_iter());
    check_is_table(x, exp);
            )*
        }};
    }

    // should be the same for union flag
    union_same!("" "--union");

    // testing intersection
    let x = process_w_table("+ --intersect range 1 5", defs);
    let mut exp = vec![vec![o("first")], vec![n(0)], vec![n(1)], vec![n(-30)]];
    exp.extend((1..5).map(|x| vec![n(x)]));
    check_is_table(x, exp);

    let x = process_w_table("let $x | range 1 5 | + $x --intersect", defs);
    let mut exp = vec![vec![o("i")]];
    exp.extend((1..5).map(|x| vec![n(x)]));
    exp.extend(vec![vec![n(0)], vec![n(1)], vec![n(-30)]]);
    check_is_table(x, exp);
}

#[test]
fn table_adding_by_col() {
    let defs = &Definitions::new();

    macro_rules! union_same {
        ($($f:literal)*) => {{
            $(
    let s = concat!("+ ",$f," range 1 5");
    println!("expr: '{}'", s);
    let x = process_w_table(s, defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3"), o("i")],
        vec![n(0), n(3), o("a"), n(1)],
        vec![n(1), n(20), o("b"), n(2)],
        vec![n(-30), n(100), o("z"), n(3)],
        vec![Nil, Nil, Nil, n(4)],
    ];
    check_is_table(x, exp);

    let s = concat!("let $x | range 1 5 | + ",$f," $x");
    println!("expr: '{}'", s);
    let x = process_w_table(s, defs);
    let exp = vec![
        vec![o("i"), o("first"), o("snd"), o("Heading 3")],
        vec![n(1), n(0), n(3), o("a")],
        vec![n(2), n(1), n(20), o("b"),],
        vec![n(3), n(-30), n(100), o("z")],
        vec![n(4), Nil, Nil, Nil],
    ];
    check_is_table(x, exp);
            )*
        }};
    }

    // should be the same for union flag
    union_same!("--cols" "--cols --union");

    // testing intersection
    let x = process_w_table(
        "+ --cols --intersect { range 1 5 | append { get i | + 1 } }",
        defs,
    );
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3"), o("i"), o("_append1")],
        vec![n(0), n(3), o("a"), n(1), n(2)],
        vec![n(1), n(20), o("b"), n(2), n(3)],
        vec![n(-30), n(100), o("z"), n(3), n(4)],
    ];
    check_is_table(x, exp);

    let x = process_w_table(
        "let $x | range 1 5 | map i + 1 | + $x --cols --intersect",
        defs,
    );
    let exp = vec![
        vec![o("i"), o("first"), o("snd"), o("Heading 3")],
        vec![n(2), n(0), n(3), o("a")],
        vec![n(3), n(1), n(20), o("b")],
        vec![n(4), n(-30), n(100), o("z")],
    ];
    check_is_table(x, exp);
}

#[test]
fn table_adding_by_col_empty_table() {
    let defs = &Definitions::new();

    // make sure adding an empty table doesn't stuff things up.
    let x = process_w_nil("Table | + --cols range 0 1", defs);
    let exp = vec![vec![o("i")], vec![n(0)]];
    check_is_table(x, exp);

    let x = process_w_nil("Table | + range 0 1", defs);
    let exp = vec![vec![o("i")], vec![n(0)]];
    check_is_table(x, exp);

    let x = process_w_nil("range 0 3 | + --cols Table", defs);
    let exp = vec![vec![o("i")], vec![n(0)], vec![n(1)], vec![n(2)]];
    check_is_table(x, exp);

    let x = process_w_nil("range 0 3 | + Table", defs);
    let exp = vec![vec![o("i")], vec![n(0)], vec![n(1)], vec![n(2)]];
    check_is_table(x, exp);

    let x = process_w_nil("range 0 3 | + --intersect Table", defs);
    let exp = vec![];
    check_is_table(x, exp);

    let x = process_w_nil("range 0 3 | + --cols --intersect Table foo", defs);
    let exp = vec![vec![o("i"), o("foo")]];
    check_is_table(x, exp);

    let x = process_w_nil("range 0 3 | + --cols --intersect Table", defs);
    let exp = vec![];
    check_is_table(x, exp);
}

#[test]
fn table_both_flags_err() {
    let defs = &Definitions::new();
    let x = process_w_table(
        "+ --cols --intersect --union { range 1 5 | append { get i | + 1 } }",
        defs,
    )
    .unwrap_err()
    .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Semantics Error: not expecting `intersect` flag
--> shell:11
 | + --cols --intersect --union { range 1 5 | append { get i | + 1 } }
 |            ^^^^^^^^^ flag not supported
--> help: try using the `--help` flag to view requirements
"
    );
}

// ------ And ------------------------------------------------------------------
#[test]
fn and_help_msg() {
    let src = "and --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `and`
--> shell:0
 | returns true if all arguments are true
 | -variadic-: more than one argument can be specified
 | 
 | Usage:
 |  => and args..
 | 
 | Examples:
 |  10 is less than 20 and equal to 10
 |  => \\ 10 | and { < 20 } { = 10 }
"
    );
}

#[test]
fn and_test() {
    let defs = &Definitions::new();
    let x = process_w_num("eq 3 | and { \\ 2 | > 1 }", defs);
    assert_eq!(x, Ok(Value::Bool(true)));
    let x = process_w_num("and { > 1 } { = 3 }", defs);
    assert_eq!(x, Ok(Value::Bool(true)));
    let x = process_w_num("and { > 3 } { = 3 }", defs);
    assert_eq!(x, Ok(Value::Bool(false)));

    // test that table rows can be used with an and!
    let x = process_w_table("filter and { get snd | > 5 } { get first | > 0 }", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(1), n(20), o("b")],
    ];
    check_is_table(x, exp);
}

// ------ Append ---------------------------------------------------------------
#[test]
fn append_help_msg() {
    let src = "append --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `append`
--> shell:0
 | add new columns onto a table using one or more expressions
 | each expression adds a new column, populated by row with the result of the expression
 | tags can be optionally specified to name the columns
 | 
 | Usage:
 |  => append args..
 | 
 | Flags:
 |  --<col-names>: name each column in order of expression
 | 
 | Examples:
 |  flag if a filesystem item is a file
 |  => ls | append { get type --Str | eq file } --is-file
 | 
 |  add more than one column
 |  => ls | append { get size | if { > 1e9 } 'big file' '' } { get ext --Str | eq csv }
"
    );
}

#[test]
fn append_testing() {
    let defs = &Definitions::new();

    let x = process_w_table("append { + { get first } get snd }", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3"), o("_append1")],
        vec![n(0), n(3), o("a"), n(3)],
        vec![n(1), n(20), o("b"), n(21)],
        vec![n(-30), n(100), o("z"), n(70)],
    ];
    check_is_table(x, exp);
    let x = process_w_table(
        "let $x | append { + { get first } get snd } --foo { get 'Heading 3' --Str }",
        defs,
    );
    let exp = vec![
        vec![
            o("first"),
            o("snd"),
            o("Heading 3"),
            o("foo"),
            o("_append1"),
        ],
        vec![n(0), n(3), o("a"), n(3), o("a")],
        vec![n(1), n(20), o("b"), n(21), o("b")],
        vec![n(-30), n(100), o("z"), n(70), o("z")],
    ];
    check_is_table(x, exp);
}

#[test]
fn empty_append_err() {
    let defs = &Definitions::new();
    let x = process_w_table("append", defs).unwrap_err().to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Semantics Error: expecting more than 0 arguments
--> shell:0
 | append
 | ^^^^^^ expecting additional argument(s)
--> help: try using the `--help` flag to view requirements
"
    );
}

#[test]
fn append_encounter_wrong_ty() {
    let defs = &Definitions::new();
    let x = process_w_table("append { get first --Str | + 'foo' }", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert!(x.contains("expected `String`, found `Number`")); // parallel so exact error might chg
}

// ------ Append-Row -----------------------------------------------------------
#[test]
fn append_row_help_msg() {
    let src = "append-row --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `append-row`
--> shell:0
 | append a row to the table
 | the row is populated with the expression results
 | -variadic-: more than one argument can be specified
 | 
 | Usage:
 |  => append-row args..
 | 
 | Examples:
 |  append the row 1 2 3 to the table
 |  => append-row 1 2 3
"
    );
}

#[test]
fn append_row_testing() {
    let defs = &Definitions::new();

    let x = process_w_table("append-row", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
        vec![Nil, Nil, Nil],
    ];
    check_is_table(x, exp);

    let x = process_w_table("append-row 1 2", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
        vec![n(1), n(2), Nil],
    ];
    check_is_table(x, exp);

    let x = process_w_table("append-row 1 2 3 4", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3"), o("_append1")],
        vec![n(0), n(3), o("a"), Nil],
        vec![n(1), n(20), o("b"), Nil],
        vec![n(-30), n(100), o("z"), Nil],
        vec![n(1), n(2), n(3), n(4)],
    ];
    check_is_table(x, exp);
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

// ------ Ceil and Floor -------------------------------------------------------
#[test]
fn ceil_help_msg() {
    let src = "ceil --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `ceil`
--> shell:0
 | return the smallest integer greater than or equal to a number
 | 
 | Usage:
 |  => ceil
"
    );
}

#[test]
fn floor_help_msg() {
    let src = "floor --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `floor`
--> shell:0
 | return the largest integer less than or equal to a number
 | 
 | Usage:
 |  => floor
"
    );
}

#[test]
fn ceil_and_floor_testing() {
    let defs = &Definitions::new();
    let x = process_w_num("ceil", defs);
    assert_eq!(x, Ok(Value::Num(3.into())));
    let x = process_w_num("floor", defs);
    assert_eq!(x, Ok(Value::Num(3.into())));
    let x = process_w_num("\\ 3.01 | ceil", defs);
    assert_eq!(x, Ok(Value::Num(4.into())));
    let x = process_w_num("\\ 3.01 | floor", defs);
    assert_eq!(x, Ok(Value::Num(3.into())));
}

// ------ Cmp ------------------------------------------------------------------
#[test]
fn cmp_help_test() {
    let defs = &Definitions::new();
    let x = process_w_nil("cmp --help", defs).unwrap_err().to_string();
    assert_eq!(
        &x,
        "Help: `cmp`
--> shell:0
 | compare <rhs> to input
 | 
 | Usage:
 |  => cmp rhs
 | 
 | Examples:
 |  compare 2 to 1
 |  => \\ 1 | cmp 2
"
    );
}

#[test]
fn ord_init_help_test() {
    let defs = &Definitions::new();
    let x = process_w_nil("Ord::Gt --help", defs)
        .unwrap_err()
        .to_string();
    assert_eq!(
        &x,
        "Help: `Ord`
--> shell:0
 | initialise a `Ord`
 | 
 | Usage:
 |  => Ord::Lt
 |  => Ord::Eq
 |  => Ord::Gt
"
    );
}

fn is_ord(res: Result<Value>, s: &'static str, idx: usize) {
    if let Err(e) = &res {
        println!("{}", e);
    }
    let res = res.unwrap();
    assert!(
        matches!(res, Value::Ogma(y) if y.variant_idx == idx),
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

#[test]
fn ord_init_testing() {
    let defs = &Definitions::new();
    is_lt(process_w_nil("Ord::Lt", defs));
    is_eq(process_w_nil("Ord::Eq", defs));
    is_gt(process_w_nil("Ord::Gt", defs));
}

#[test]
fn ord_prim_testing() {
    use std::cmp::Ordering;
    let t = Ordering::as_type();
    assert!(matches!(t, Type::Def(x) if x.name().str() == "Ord"));

    is_lt(Ok(Ordering::Less.into()));
    is_eq(Ok(Ordering::Equal.into()));
    is_gt(Ok(Ordering::Greater.into()));
}

#[test]
fn cmp_ord_test() {
    let defs = &Definitions::new();
    is_eq(process_w_num("Ord::Gt | cmp Ord::Gt", defs));
    is_eq(process_w_num("Ord::Eq | cmp Ord::Eq", defs));
    is_eq(process_w_num("Ord::Lt | cmp Ord::Lt", defs));

    is_gt(process_w_num("Ord::Gt | cmp Ord::Eq", defs));
    is_gt(process_w_num("Ord::Gt | cmp Ord::Lt", defs));
    is_gt(process_w_num("Ord::Eq | cmp Ord::Lt", defs));

    is_lt(process_w_num("Ord::Lt | cmp Ord::Gt", defs));
    is_lt(process_w_num("Ord::Lt | cmp Ord::Eq", defs));
    is_lt(process_w_num("Ord::Eq | cmp Ord::Gt", defs));
}

#[test]
fn cmp_num_test() {
    let defs = &Definitions::new();
    // process_w_num uses 3
    is_lt(process_w_num("cmp 5", defs));
    is_eq(process_w_num("cmp 3", defs));
    is_gt(process_w_num("cmp 1", defs));

    is_lt(process_w_num("cmp \\ 5", defs));
    is_eq(process_w_num("cmp \\ 3", defs));
    is_gt(process_w_num("cmp \\ 1", defs));
}

#[test]
fn point_cmp_overload() {
    // only doing cmp on x as proof of concept
    let defs = &mut with_dummy_defs();
    process_definition(
        "def cmp Point (rhs) { get x | cmp { \\ $rhs | get x } }",
        Location::Shell,
        None,
        defs,
    )
    .unwrap();

    is_gt(process_w_nil("Point 1 3 | cmp Point -2 2", defs));
    is_eq(process_w_nil("Point 1 3 | cmp Point 1 2", defs));
    is_lt(process_w_nil("Point 1 3 | cmp Point 3 2", defs));
}

#[test]
fn cmp_tablerow() {
    let defs = &Definitions::new();
    let x = process_w_table("filter { get first | > 1 }", defs);
    let exp = vec![vec![o("first"), o("snd"), o("Heading 3")]];
    check_is_table(x, exp);

    let x = process_w_table("filter first >= 1", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(1), n(20), o("b")],
    ];
    check_is_table(x, exp);

    let x = process_w_table("filter { get first | < 1 }", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(-30), n(100), o("z")],
    ];
    check_is_table(x, exp);

    let x = process_w_table("filter first <= 1", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    check_is_table(x, exp);

    let x = process_w_table("filter snd = 100", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(-30), n(100), o("z")],
    ];
    check_is_table(x, exp);

    let x = process_w_table("filter first != 1 ", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(-30), n(100), o("z")],
    ];
    check_is_table(x, exp);
}

// ------ Dedup ----------------------------------------------------------------
#[test]
fn dedup_help_msg() {
    let src = "dedup --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `dedup`
--> shell:0
 | deduplicate items
 | for Tables consectutive repeated rows are removed if the cells in
 | specified columns match. if no columns are specified the whole row must match.
 | if the table is sorted, this removes all duplicates.
 | for Strs duplicate characters are removed.
 | 
 | Usage:
 |  => dedup col-name..
 | 
 | Examples:
 |  remove all duplicate entries in the 'Product' heading
 |  => sort Product | dedup Product
 | 
 |  remove duplicates that match the entire row
 |  => ls foo | + ls bar | sort name | dedup
"
    );
}

#[test]
fn dedup_table_testing() {
    let defs = &Definitions::new();

    // check that dedup uses all columns
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    let x = process_w_table("+ #i | sort snd | dedup", defs);
    check_is_table(x, exp.clone());

    // check that dedup doesn't work if not sorted!
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    let x = process_w_table("+ #i | dedup", defs);
    check_is_table(x, exp.clone());

    // check on dedup just single columns
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(-30), n(100), o("z")],
        vec![n(-30), n(101), o("z")],
        vec![n(0), n(3), o("a")],
        vec![n(0), n(4), o("a")],
        vec![n(1), n(20), o("b")],
        vec![n(1), n(21), o("b")],
    ];
    let x = process_w_table("+ {\\#i | map snd + 1} | sort first | dedup", defs);
    check_is_table(x, exp.clone());
    let x = process_w_table(
        "+ {\\#i | map snd + 1} | sort first | dedup first snd",
        defs,
    );
    check_is_table(x, exp.clone());
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(-30), n(100), o("z")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
    ];
    let x = process_w_table("+ {\\#i | map snd + 1} | sort first | dedup first", defs);
    check_is_table(x, exp.clone());
}

#[test]
fn dedup_str_testing() {
    let defs = &Definitions::new();

    let x = process_w_str("dedup", defs);
    assert_eq!(x, Ok(Value::Str("Helo".into())));

    let x = process_w_str("\\\'foo barr zoog\' | dedup", defs);
    assert_eq!(x, Ok(Value::Str("fo bar zog".into())));
}

// ------ Div ------------------------------------------------------------------
#[test]
fn div_help_msg() {
    let src = "/ --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `/`
--> shell:0
 | divide arguments against one another
 | note: if input is not a Num, the first arg is used as lhs
 | dividing by 0 will result in infinity (∞)
 | -variadic-: more than one argument can be specified
 | 
 | Usage:
 |  => / args..
 | 
 | Examples:
 |  divide 4 by 2
 |  => \\ 4 | / 2
 | 
 |  divide 2 ÷ 3
 |  => ÷ 2 3
 | 
 |  divide multiple numbers together
 |  => / 1 2 3 4 5
"
    );
}

#[test]
fn div_testing() {
    let defs = &Definitions::new();
    let x = process_w_nil("/ 5", defs);
    assert_eq!(x, Ok(Value::Num((5).into())));
    let x = process_w_num("/ 6", defs);
    assert_eq!(x, Ok(Value::Num((0.5).into())));
    let x = process_w_num("let $x | \\ 30 | ÷ -5 $x", defs);
    assert_eq!(x, Ok(Value::Num((-2).into()))); // 30 / -5 / 3 = -2
    let x = process_w_num("/ 0", defs);
    assert_eq!(x, Ok(Value::Num(std::f64::INFINITY.into())));
    let x = process_w_num("/ 0 3", defs);
    assert_eq!(x, Ok(Value::Num(std::f64::INFINITY.into())));
}

// ------ Dot Operator ---------------------------------------------------------
#[test]
fn dotop_help_msg() {
    let src = ". --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `.`
--> shell:0
 | extract a value out of a structure using infix operator
 | 
 | Usage:
 |  => . => $foo.bar
 | 
 | Examples:
 |  extract the x coord of a point structure
 |  => $point.x
 | 
 |  get the value of a column entry in a TableRow
 |  => $table-row.col-name
"
    );
}

#[test]
fn dotop_test() {
    let defs = &mut Definitions::new();
    process_definition("def-ty Bar { x:Num y:Num }", Location::Shell, None, defs).unwrap();
    process_definition("def-ty Foo { x:Num bar:Bar }", Location::Shell, None, defs).unwrap();

    let print = |s| match process_w_nil(s, defs) {
        Ok(Value::Ogma(x)) => print_ogma_data(x),
        e => panic!("not expecting {:?}", e),
    };

    let x = process_w_nil("Bar 1 3 | let $x | \\ $x.x", defs);
    assert_eq!(x, Ok(Value::Num(1.into())));

    let x = process_w_nil("Foo 5 Bar 1 3 | let $x | \\ $x.x", defs);
    assert_eq!(x, Ok(Value::Num(5.into())));

    let x = print("Foo 5 Bar 1 3 | let $x | \\ $x.bar");
    assert_eq!(&x, "Bar (x = 1, y = 3)");

    let x = process_w_nil("Foo 5 Bar 1 3 | let $foo | \\ $foo.bar.x", defs);
    assert_eq!(x, Ok(Value::Num(1.into())));

    let x = process_w_nil("Foo 5 Bar 1 3 | let $foo | \\ $foo.bar.y", defs);
    assert_eq!(x, Ok(Value::Num(3.into())));

    let x = print("Foo 5 Bar 1 3 | let $foo | Bar $foo.x $foo.bar.y");
    assert_eq!(&x, "Bar (x = 5, y = 3)");

    let x = process_w_nil("\\ {Foo 5 Bar 1 3}.x", defs);
    assert_eq!(x, Ok(Value::Num(5.into())));
}

#[test]
fn dotop_identifier_tests() {
    let defs = &Definitions::new();

    let err = process_w_table("fold 0 + $row.'Testing encased string'", defs)
        .unwrap_err()
        .to_string();
    assert_eq!(err, "Evaluation Error: header `Testing encased string` not found in table
--> shell:15
 | fold 0 + $row.'Testing encased string'
 |                ^^^^^^^^^^^^^^^^^^^^^^ `Testing encased string` resolves to `Testing encased string`
");

    let err = process_w_table("fold 0 + $row.\"Testing encased string\"", defs)
        .unwrap_err()
        .to_string();
    assert_eq!(err, "Evaluation Error: header `Testing encased string` not found in table
--> shell:15
 | fold 0 + $row.\"Testing encased string\"
 |                ^^^^^^^^^^^^^^^^^^^^^^ `Testing encased string` resolves to `Testing encased string`
");

    let err = process_w_table("fold 0 + $row.Testing-weird\\string", defs)
        .unwrap_err()
        .to_string();
    println!("{}", err);
    assert_eq!(
        err,
        "Semantics Error: expecting argument with type `Number`, found `String`
--> shell:27
 | fold 0 + $row.Testing-weird\\string
 |                            ^^^^^^^ this argument returns type `String`
--> shell:27
 | fold 0 + $row.Testing-weird\\string
 |                            ^^^^^^^ invoked here
--> shell:0
 | fold 0 + $row.Testing-weird\\string
 | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ invoked here
--> help: commands may require specific argument types, use `--help` to view requirements
"
    );
}

#[test]
fn dotop_err_test() {
    let defs = &mut Definitions::new();
    process_definition("def-ty Bar { x:Num y:Num }", Location::Shell, None, defs).unwrap();
    process_definition("def-ty Foo { x:Num bar:Bar }", Location::Shell, None, defs).unwrap();

    let x = process_w_nil("Bar 1 3 | let $x | . x", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Semantics Error: expecting more than 1 arguments
--> shell:19
 | Bar 1 3 | let $x | . x
 |                    ^^^ expecting additional argument(s)
--> help: try using the `--help` flag to view requirements
"
    );

    let x = process_w_nil("Bar 1 3 | let $x | \\ $x.z", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        r#"Semantics Error: `Bar` does not contain field `z`
--> shell:24
 | Bar 1 3 | let $x | \ $x.z
 |                         ^ `z` not found
--> shell:19
 | Bar 1 3 | let $x | \ $x.z
 |                    ^^^^^^ invoked here
"#
    );

    let x = process_w_nil("Foo 5 Bar 1 3 | let $x | \\ $x.z", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        r#"Semantics Error: `Foo` does not contain field `z`
--> shell:30
 | Foo 5 Bar 1 3 | let $x | \ $x.z
 |                               ^ `z` not found
--> shell:25
 | Foo 5 Bar 1 3 | let $x | \ $x.z
 |                          ^^^^^^ invoked here
"#
    );

    let x = process_w_nil("Foo 5 Bar 1 3 | let $x | \\ $x.bar.z", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        r#"Semantics Error: `Bar` does not contain field `z`
--> shell:34
 | Foo 5 Bar 1 3 | let $x | \ $x.bar.z
 |                                   ^ `z` not found
--> shell:25
 | Foo 5 Bar 1 3 | let $x | \ $x.bar.z
 |                          ^^^^^^^^^^ invoked here
"#
    );

    let x = process_w_nil("Foo 5 Bar 1 3 | let $x | \\ $x.bar.z.y", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        r#"Semantics Error: `Bar` does not contain field `z`
--> shell:34
 | Foo 5 Bar 1 3 | let $x | \ $x.bar.z.y
 |                                   ^ `z` not found
--> shell:27
 | Foo 5 Bar 1 3 | let $x | \ $x.bar.z.y
 |                            ^^^^^^^^^^ invoked here
--> shell:25
 | Foo 5 Bar 1 3 | let $x | \ $x.bar.z.y
 |                          ^^^^^^^^^^^^ invoked here
"#
    );

    let x = process_w_nil("\\ {Foo 5 Bar 1 3}.z", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        r#"Semantics Error: `Foo` does not contain field `z`
--> shell:18
 | \ {Foo 5 Bar 1 3}.z
 |                   ^ `z` not found
--> shell:0
 | \ {Foo 5 Bar 1 3}.z
 | ^^^^^^^^^^^^^^^^^^^ invoked here
"#
    );
}

// ------ Eq -------------------------------------------------------------------
#[test]
fn eq_help_test() {
    let defs = &Definitions::new();
    let x = process_w_nil("eq --help", defs).unwrap_err().to_string();
    assert_eq!(
        &x,
        "Help: `eq`
--> shell:0
 | returns if <rhs> is equal to input
 | 
 | Usage:
 |  => eq rhs
 | 
 | Examples:
 |  does 2 equal 1
 |  => \\ 1 | eq 2
 | 
 |  1 equals 1
 |  => \\ 1 | eq 1
"
    );
}

#[test]
fn eq_num_test() {
    let defs = &Definitions::new();
    // process_w_num uses 3
    assert_eq!(process_w_num("eq 5", defs), Ok(Value::Bool(false)));
    assert_eq!(process_w_num("eq 3", defs), Ok(Value::Bool(true)));
    assert_eq!(process_w_num("= 5", defs), Ok(Value::Bool(false)));
    assert_eq!(process_w_num("= 3", defs), Ok(Value::Bool(true)));
    assert_eq!(process_w_num("!= 5", defs), Ok(Value::Bool(true))); // 3 != 5
    assert_eq!(process_w_num("!= 3", defs), Ok(Value::Bool(false))); // 3 != 3 (false)
}

#[test]
fn eq_str_test() {
    let defs = &Definitions::new();
    // process_w_str uses "Hello"
    assert_eq!(process_w_str("eq Hello", defs), Ok(Value::Bool(true)));
    assert_eq!(process_w_str("eq world", defs), Ok(Value::Bool(false)));
    assert_eq!(process_w_str("= world", defs), Ok(Value::Bool(false)));
    assert_eq!(process_w_str("= Hello", defs), Ok(Value::Bool(true)));
    assert_eq!(process_w_str("!= world", defs), Ok(Value::Bool(true)));
    assert_eq!(process_w_str("!= Hello", defs), Ok(Value::Bool(false)));
}

#[test]
fn point_eq_overload() {
    let defs = &mut with_dummy_defs();
    let x = process_definition(
        "def eq Point (rhs) { and {get x|= $rhs.x} {get y|= $rhs.y} }",
        Location::Shell,
        None,
        defs,
    );
    assert_eq!(x, Ok((Value::Nil, None)));

    let x = process_w_nil("Point 1 3 | eq Point -2 2", defs);
    assert_eq!(x, Ok(Value::Bool(false)));
    let x = process_w_nil("Point 1 3 | eq Point 1 3", defs);
    assert_eq!(x, Ok(Value::Bool(true)));
    let x = process_w_nil("Point 1 3 | = Point 1 3", defs);
    assert_eq!(x, Ok(Value::Bool(true)));
}

// ------ Filtering ------------------------------------------------------------
#[test]
fn filtering_help_msg() {
    let src = "filter --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `filter`
--> shell:0
 | filter incoming data using a predicate
 | filter can be used with a column header and a type flag
 | filtering columns is achievable with the --cols flag
 | 
 | Usage:
 |  => filter [col-name] <predicate>
 | 
 | Flags:
 |  --<type>: only filter entries of type. defaults to Num if not specified
 |  --cols: filter columns with predicate. predicate is String -> Bool
 | 
 | Examples:
 |  filter ls items greater than 5kB
 |  => ls | filter size > 5e3
 | 
 |  filter ls by extension
 |  => ls | filter ext --Str = md
 | 
 |  filter a table by two columns
 |  => \\ table.csv | filter { and { get col-a | > 100 } { get col-b | < 10 } }
 | 
 |  filter table columns
 |  => \\ table.csv | filter --cols or { = 'foo' } { = bar }
"
    );
}

#[test]
fn row_filtering() {
    let defs = &Definitions::new();
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    let x = process_w_table("filter { get snd | > 10 }", defs);
    check_is_table(x, exp.clone());
    let x = process_w_table("filter snd > 10", defs);
    check_is_table(x, exp.clone());
    let x = process_w_table("filter snd { > 10 }", defs);
    check_is_table(x, exp.clone());
}

#[test]
fn row_filtering2() {
    let defs = &Definitions::new();
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    let x = process_w_table("filter { get 'Heading 3' --Str | > a }", defs);
    check_is_table(x, exp.clone());
    let x = process_w_table("filter 'Heading 3' --Str > a", defs);
    check_is_table(x, exp.clone());
    let x = process_w_table("filter 'Heading 3' --Num > 10", defs);
    check_is_table(x, vec![vec![o("first"), o("snd"), o("Heading 3")]]);
}

#[test]
fn row_filtering_by_building_new_table() {
    let defs = &Definitions::new();
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    // The let binding should force the table to be shared
    let x = process_w_table("let $x | filter { get 'Heading 3' --Str | > a }", defs);
    check_is_table(x, exp.clone());
}

#[test]
fn column_not_table() {
    let defs = &Definitions::new();
    let x = process_w_table("filter { get not-here | > 10 }", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Evaluation Error: header `not-here` not found in table
--> shell:13
 | filter { get not-here | > 10 }
 |              ^^^^^^^^ `not-here` resolves to `not-here`
"
    );

    let x = process_w_table("filter not-here > 10", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Evaluation Error: header `not-here` not found in table
--> shell:7
 | filter not-here > 10
 |        ^^^^^^^^ `not-here` resolves to `not-here`
"
    );
}

#[test]
fn row_filtering_using_def() {
    let defs = &with_dummy_defs();
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    let x = process_w_table("filter gt10", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Semantics Error: expecting more than 0 arguments
--> shell:7
 | filter gt10
 |        ^^^^ expecting additional argument(s)
--> shell:0
 | filter gt10
 | ^^^^^^^^^^^ invoked here
--> help: try using the `--help` flag to view requirements
"
    );
    let x = process_w_table("filter gt10 snd", defs);
    check_is_table(x, exp.clone());
}

#[test]
fn column_filtering() {
    let defs = &Definitions::new();

    let x = process_w_table("filter --cols = first", defs);
    let exp = vec![vec![o("first")], vec![n(0)], vec![n(1)], vec![n(-30)]];
    check_is_table(x, exp.clone());

    let x = process_w_table("filter --cols or { = 'Heading 3' } { = first }", defs);
    let exp = vec![
        vec![o("first"), o("Heading 3")],
        vec![n(0), o("a")],
        vec![n(1), o("b")],
        vec![n(-30), o("z")],
    ];
    check_is_table(x, exp.clone());
}

// ------ Folding --------------------------------------------------------------
#[test]
fn fold_help_msg() {
    let src = "fold --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `fold`
--> shell:0
 | fold (reduce) table into single value
 | fold takes a seed value and an accumulator expression
 | the variable $row is available to query the table row
 | 
 | Usage:
 |  => fold seed accumulator
 | 
 | Examples:
 |  sum numbers (0,10)
 |  => range 0 11 | fold 0 { + $row.i }
 | 
 |  count number of files in directory
 |  => ls | filter { get type --Str | = file } | fold 0 + 1
"
    );
}

#[test]
fn fold_test() {
    let defs = &Definitions::new();
    let x = process_w_num("range 0 10 | fold 0 { + { \\$row | get i } }", defs);
    assert_eq!(x, Ok(Value::Num(45.into())));
    let x = process_w_num("range 0 10 | fold 0 + $row.i", defs);
    assert_eq!(x, Ok(Value::Num(45.into())));
    let x = process_w_num("range 0 0 | fold -100 + $row.i", defs);
    assert_eq!(x, Ok(Value::Num((-100).into())));
}

#[test]
fn fold_while_help_msg() {
    let src = "fold-while --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `fold-while`
--> shell:0
 | fold (reduce) table into single value while a predicate remains true
 | fold-while is similar to fold with an added predicate check on each iteration
 | the input into the predicate is the current accumulator value
 | fold-while will stop iterating once the predicate returns false
 | 
 | Usage:
 |  => fold-while seed predicate accumulator
 | 
 | Examples:
 |  sum natural numbers until sum is greater than one million
 |  => range 1 1e6 | fold-while 0 {<= 1e6} { + $row.i }
"
    );
}

#[test]
fn fold_while_test() {
    let defs = &Definitions::new();
    let x = process_w_num("range 0 10 | fold-while 0 {>= 0} { + $row.i }", defs);
    assert_eq!(x, Ok(Value::Num(45.into())));
    let x = process_w_num("range 0 10 | fold-while 0 {< 30} + $row.i", defs);
    assert_eq!(x, Ok(Value::Num(36.into())));
    let x = process_w_num("range 1 20 | fold-while 1 {< 1e6} * $row.i", defs);
    assert_eq!(x, Ok(Value::Num((3628800).into())));
    let x = process_w_num("range 1 20 | fold-while {Tuple 0 0} {get t0 | < 20} { Tuple {+ #i.t0 #i.t1} $row.i } | get t0", defs);
    assert_eq!(x, Ok(Value::Num((21).into())));
}

// ------ Get ------------------------------------------------------------------
#[test]
fn get_help_msg() {
    let src = "get --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `get`
--> shell:0
 | extract a value out of a data structure
 | optionally specify a default value if the get type does not match
 | 
 | Usage:
 |  => get field [default]
 | 
 | Flags:
 |  --<type>: assert that the entry is of type. defaults to Num if not specified
 | 
 | Examples:
 |  get the x field of a user defined Point type
 |  => Point 1 3 | get x
 | 
 |  get the entry of a table row under the column 'size'
 |  => ls | filter { get size | > 100 }
 | 
 |  get all files in the directory, using the --Str flag
 |  => ls | filter { get type --Str | = 'file' }
 | 
 |  sum the size of files, using a default of zero
 |  => ls | fold 0 { + {\\$row | get size 0} }
"
    );
}

#[test]
fn get_test() {
    let defs = &Definitions::new();
    let x = process_w_table("fold 0 { \\$row | get snd --Str | \\ 3 }", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Evaluation Error: table entry for [row:1,col:'snd'] did not have expected type
expected `String`, found `Number`
--> shell:21
 | fold 0 { \\$row | get snd --Str | \\ 3 }
 |                      ^^^
--> help: column entries must have a matching type
"
    );

    let x = process_w_table("fold 0 { \\$row | get snd --foo | \\ 3 }", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        r#"Semantics Error: type `foo` not defined
--> shell:27
 | fold 0 { \$row | get snd --foo | \ 3 }
 |                            ^^^ `foo` not defined
--> shell:0
 | fold 0 { \$row | get snd --foo | \ 3 }
 | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ invoked here
--> help: view a list of types using `def-ty --list`
"#
    );

    let x = process_w_table("fold 0 { \\$row | get snd --Str --foo | \\ 3 }", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        r#"Semantics Error: not expecting `foo` flag
--> shell:33
 | fold 0 { \$row | get snd --Str --foo | \ 3 }
 |                                  ^^^ flag not supported
--> shell:0
 | fold 0 { \$row | get snd --Str --foo | \ 3 }
 | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ invoked here
--> help: try using the `--help` flag to view requirements
"#
    );

    let x = process_w_table(
        "fold 0 { + $row.first {\\$row | get 'Heading 3' 100} }",
        defs,
    );
    assert_eq!(x, Ok(Value::Num((0 + 1 - 30 + 100 + 100 + 100).into())));
}

// ------ Greater Than ---------------------------------------------------------
#[test]
fn gt_help_msg() {
    let src = "> --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `>`
--> shell:0
 | user defined implementation in <ogma>
 | `def > (rhs) { cmp $rhs | = Ord::Gt }`
 | test if input is greater than rhs
 | 
 | Usage:
 |  => > rhs
 | 
 | Examples:
 |  test if 1 is greater than 0
 |  => \\ 1 | > 0
 | 
 |  use to filter ls
 |  => ls | filter > size 1e6
"
    );
}

#[test]
fn test_gt_cmp() {
    let defs = &with_dummy_defs();
    let x = process_w_table("num5 | > 3.14", defs);
    assert_eq!(x, Ok(Value::Bool(true)));
    let x = process_w_table("\\ 5 | > num5", defs);
    assert_eq!(x, Ok(Value::Bool(false)));
    let x = process_w_num(">= 3", defs);
    assert_eq!(x, Ok(Value::Bool(true)));
}

// ------ Grp ------------------------------------------------------------------
#[test]
fn grp_help_msg() {
    let src = "grp --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `grp`
--> shell:0
 | group a table by column headers
 | each value under the header is stringified and
 | concatenated together separated by a hyphen
 | to group on a derived value see `grp-by`
 | 
 | Usage:
 |  => grp col-name..
 | 
 | Examples:
 |  group by file extension
 |  => ls | grp ext
 | 
 |  group by file extension and modified
 |  => ls | grp ext modified
"
    );
}

#[test]
fn grp_testing() {
    let defs = &Definitions::new();

    let x = process_w_table(
        "grp 'Heading 3' | 
fold {range 0 0} {let $acc | \\$row | get value --Table | pick first | let $x | \\$acc | + $x}",
        defs,
    );
    let exp = vec![vec![o("i")], vec![n(0)], vec![n(1)], vec![n(-30)]];
    check_is_table(x, exp);
    let x = process_w_table(
        "append --'foo' {get first | >= 0} |
grp foo | map value --Table len",
        defs,
    );
    let exp = vec![
        vec![o("key"), o("value")],
        vec![o("false"), n(1)],
        vec![o("true"), n(2)],
    ];
    check_is_table(x, exp);
    let x = process_w_table(
        "append --'foo' {get first | >= 0} |
grp foo 'Heading 3' | map value --Table len",
        defs,
    );
    let exp = vec![
        vec![o("key"), o("value")],
        vec![o("false-z"), n(1)],
        vec![o("true-a"), n(1)],
        vec![o("true-b"), n(1)],
    ];
    check_is_table(x, exp);
}

// ------ Grp-by ---------------------------------------------------------------
#[test]
fn grpby_help_msg() {
    let src = "grp-by --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `grp-by`
--> shell:0
 | group table using an expression
 | the result of the expression must define a `cmp` implementation
 | this can be used to group user-defined types
 | 
 | Usage:
 |  => grp-by <expr>
 | 
 | Examples:
 |  group ls by file extension
 |  => ls | grp-by { get --Str ext }
 | 
 |  group using a user-defined type
 |  => ls | grp-by { Point { get size } }
"
    );
}

#[test]
fn grpby_testing() {
    let defs = &Definitions::new();

    let x = process_w_table(
        "grp-by {get --Str 'Heading 3'} | 
fold {range 0 0} { let $acc | \\$row | get value --Table | pick first | let $x | \\$acc | + $x}",
        defs,
    );
    let exp = vec![vec![o("i")], vec![n(0)], vec![n(1)], vec![n(-30)]];
    check_is_table(x, exp);
    let x = process_w_table("grp-by {get first | >= 0} | map value --Table len", defs);
    let exp = vec![
        vec![o("key"), o("value")],
        vec![Entry::from(Value::Bool(false)), n(1)],
        vec![Entry::from(Value::Bool(true)), n(2)],
    ];
    check_is_table(x, exp);
}

// ------ If -------------------------------------------------------------------
#[test]
fn if_help_msg() {
    let src = "if --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `if`
--> shell:0
 | evaluate expression if predicate is met
 | input is carried through to each of the expressions
 | `expr-if-true` and `expr-if-false` must evaluate to the same type
 | `if` can be overloaded such that it can test multiple predicates
 | 
 | Usage:
 |  => if predicate-1 expr-if-true-1 [predicate-2] [expr-if-true-2] ... expr-if-false
 | 
 | Examples:
 |  return 2 if 3, otherwise 1
 |  => \\ 3 | if { = 3 } 2 1
 | 
 |  return 2 if 3, 1 if 2, otherwise 0
 |  => \\ 10 | if {= 3} 2 {= 2} 1 0
"
    );
}

#[test]
fn if_testing() {
    let defs = &Definitions::new();
    let x = process_w_num("if { = 3 } 2 1", defs);
    assert_eq!(x, Ok(Value::Num(2.into())));
    let x = process_w_num("if { = 3 } { + 2 } + 1", defs);
    assert_eq!(x, Ok(Value::Num(5.into())));
    let x = process_w_num("+ if { = 3 } 2 1", defs);
    assert_eq!(x, Ok(Value::Num(5.into())));
    let x = process_w_num("+ if { = 4 } 2 1", defs);
    assert_eq!(x, Ok(Value::Num(4.into())));
    let x = process_w_num("if {= 3} 2 {= 2} 1 0", defs);
    assert_eq!(x, Ok(Value::Num(2.into())));
    let x = process_w_num("if {= 10} 2 {> 0} 1 0", defs);
    assert_eq!(x, Ok(Value::Num(1.into())));
}

#[test]
fn if_err_testing() {
    let defs = &Definitions::new();
    let x = process_w_num("if { = 3 } 0 'foo'", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Evaluation Error: branch arms do not have matching output types
--> shell:11
 | if { = 3 } 0 'foo'
 |            ^ this branch has a different output type
--> help: branching impls require consistent output types
"
    );
    let x = process_w_num("if { = 'foo' } 0 1", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Semantics Error: expecting argument with type `Number`, found `String`
--> <ogma>:18
 | def = (rhs) { eq $rhs }
 |                   ^^^ this argument returns type `String`
--> shell:5
 | if { = 'foo' } 0 1
 |      ^^^^^^ invoked here
--> shell:0
 | if { = 'foo' } 0 1
 | ^^^^^^^^^^^^^^^^^^ invoked here
--> help: commands may require specific argument types, use `--help` to view requirements
"
    );

    let x = process_w_num("if {= 3} 0 {= 2} 1", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Semantics Error: expecting more than 4 arguments
--> shell:0
 | if {= 3} 0 {= 2} 1
 | ^^^^^^^^^^^^^^^^^^ expecting additional argument(s)
--> help: `if` requires odd number of arguments to match true/false expressions
"
    );
}

// ------ Input ----------------------------------------------------------------
#[test]
fn input_help_msg() {
    let src = "\\ --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `\\`
--> shell:0
 | sets the input value for the next pipeline block
 | 
 | Usage:
 |  => \\ input
 | 
 | Examples:
 |  feed in a number
 |  => \\ 3.14
 | 
 |  feed in a string
 |  => \\ 'hello, world!'
"
    );
}

#[test]
fn in_testing() {
    let defs = &Definitions::new();

    let x = process_w_num("+ { \\ 5 }", defs);
    assert_eq!(x, Ok(Value::Num(8.into())));
    let x = process_w_num("\\ { \\ 5 }", defs);
    assert_eq!(x, Ok(Value::Num(5.into())));
    let x = process_w_num("\\ { \\ 'hello, world!' }", defs);
    assert_eq!(x, Ok(Value::Str("hello, world!".into())));
}

#[test]
fn input_empty_string() {
    let defs = &Definitions::new();
    let x = process_w_num("\\ '' | eq \"\"", defs);
    assert_eq!(x, Ok(Value::Bool(true)));
}

#[test]
fn using_pound_i() {
    let d = &mut Definitions::default();
    process_definition("def-ty Point { x:Num y:Num }", Location::Shell, None, d).unwrap();

    let x = process_w_num("if {= 3} #i 2", d);
    assert_eq!(x, Ok(Value::Num(3.into())));
    let x = process_w_num("Point #i 2 | get x", d);
    assert_eq!(x, Ok(Value::Num(3.into())));
    let x = process_w_num("Point #i 2 | if { get y | = 3 } #i.x #i.y", d);
    assert_eq!(x, Ok(Value::Num(2.into())));
}

#[test]
fn using_pound_i_table_row() {
    let d = &Definitions::new();

    let x = process_w_table("append + #i.snd 1", d);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3"), o("_append1")],
        vec![n(0), n(3), o("a"), n(4)],
        vec![n(1), n(20), o("b"), n(21)],
        vec![n(-30), n(100), o("z"), n(101)],
    ];
    check_is_table(x, exp.clone());
}

#[test]
fn input_backslash_str() {
    let defs = &Definitions::new();
    let x = process_w_num(r#"\ 'foo\bar' | eq "foo\bar""#, defs);
    assert_eq!(x, Ok(Value::Bool(true)));
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

// ------ Is Finite ------------------------------------------------------------
#[test]
fn isfinite_help_msg() {
    let src = "is-finite --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `is-finite`
--> shell:0
 | returns whether a number is finite
 | a number is finite if it is not infinite AND not NaN
 | 
 | Usage:
 |  => is-finite
 | 
 | Examples:
 |  most numbers are finite
 |  => \\ 5 | is-finite
 | 
 |  but dividing by zero isn't!
 |  => ÷ 1 0 | is-finite
"
    );
}

#[test]
fn isfinite_testing() {
    let defs = &Definitions::new();
    let x = process_w_num("is-finite", defs);
    assert_eq!(x, Ok(Value::Bool(true)));
    let x = process_w_num("\\ - inf | is-finite", defs);
    assert_eq!(x, Ok(Value::Bool(false)));
    let x = process_w_num("\\ inf | is-finite", defs);
    assert_eq!(x, Ok(Value::Bool(false)));
    let x = process_w_num("\\ nan | is-finite", defs);
    assert_eq!(x, Ok(Value::Bool(false)));
    let x = process_w_num("/ 0 | is-finite", defs);
    assert_eq!(x, Ok(Value::Bool(false)));
}

// ------ Last -----------------------------------------------------------------
#[test]
fn last_testing() {
    let defs = &Definitions::new();

    // table
    let x = process_w_table("last {get first}", defs);
    assert_eq!(x, Ok(Value::Num((-30).into())));
    let x = process_w_table("last {get snd}", defs);
    assert_eq!(x, Ok(Value::Num(100.into())));

    // string
    let x = process_w_str("last", defs);
    assert_eq!(x, Ok(Value::Str("o".into())));
}

// ------ Length ---------------------------------------------------------------
#[test]
fn len_help_msg() {
    let src = "len --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `len`
--> shell:0
 | return the length of a table or string (chars)
 | table length **does not include header row**
 | 
 | Usage:
 |  => len
 | 
 | Flags:
 |  --cols: return the number of columns in a table
 | 
 | Examples:
 |  return the number of files on the filesystem
 |  => ls | filter type --Str eq file | len
 | 
 |  columns in the ls table
 |  => ls | len --cols
 | 
 |  length of a string
 |  => \\ 'Hello, 🌎!' | len
"
    );
}

#[test]
fn len_table_testing() {
    let defs = &Definitions::new();
    let x = process_w_table("len", defs);
    assert_eq!(x, Ok(Value::Num(3.into())));
    let x = process_w_table("len --cols", defs);
    assert_eq!(x, Ok(Value::Num(3.into())));
}

#[test]
fn len_str_testing() {
    let defs = &Definitions::new();
    let x = process_w_str("len", defs);
    assert_eq!(x, Ok(Value::Num(5.into())));
    let x = process_w_str("\\ '' | len", defs);
    assert_eq!(x, Ok(Value::Num(0.into())));
    let x = process_w_str("\\ 'Hello, 🌎!' | len", defs);
    assert_eq!(x, Ok(Value::Num(9.into())));
}

// ------ Let and Variables ----------------------------------------------------
#[test]
fn let_help_msg() {
    let src = "let --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `let`
--> shell:0
 | assign variable identifiers to expression results
 | each binding takes the form `<expr> $var`
 | optionally a final `$var` can be specified which assigns the input
 | to `$var` and throughputs the input as the output
 | variables are scoped to within the expression they are defined
 | 
 | Usage:
 |  => let [<expr-1> $var-1] [<expr-2> $var-2] ... [$var-final]
 | 
 | Examples:
 |  assign $x to the number 5
 |  => \\ 5 | let $x
 | 
 |  assign $x to 1, $y to 2, $z to 3
 |  => \\ 6 | let {- 5} $x {/ 3} $y {* 0.5} $z
 | 
 |  assign $x to double input, assign $y to input and pass through
 |  => let {* 2} $x $y
"
    );
}

#[test]
fn assigning() {
    let defs = &Definitions::new();
    let x = process_w_table("\\ 5 | let $x | \\ 10 | > $x", defs);
    assert_eq!(x, Ok(Value::Bool(true)));

    let x = process_w_num(
        "let {+ 1} $x {- 1} $y {= 3} $z | \\ $x | / $y | and {= 2} $z",
        defs,
    );
    assert_eq!(x, Ok(Value::Bool(true)));

    let x = process_w_num("let {+ 1} $x {- 1} $y $z | \\ $x | * $y $z", defs);
    assert_eq!(x, Ok(Value::Num((4 * 2 * 3).into())));

    let x = process_w_table(
        "filter { let {get first} $x {get snd} $y | \\ $x | < $y }",
        defs,
    );
    check_is_table(
        x,
        vec![
            vec![o("first"), o("snd"), o("Heading 3")],
            vec![n(0), n(3), o("a")],
            vec![n(1), n(20), o("b")],
            vec![n(-30), n(100), o("z")],
        ],
    );
}

#[test]
fn let_tablerow() {
    let defs = &Definitions::new();
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    let x = process_w_table("filter { let $x | get snd | > 10 }", defs);
    check_is_table(x, exp.clone());
    let x = process_w_table("filter { let $x | \\$x.snd | > 10 }", defs);
    check_is_table(x, exp);
}

#[test]
fn wrong_variable_type() {
    let defs = &Definitions::new();
    let x = process_w_table("let $x | \\ 5 | > $x", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        r#"Semantics Error: expecting argument with type `Number`, found `Table`
--> <ogma>:19
 | def > (rhs) { cmp $rhs | = Ord::Gt }
 |                    ^^^ this argument returns type `Table`
--> shell:15
 | let $x | \ 5 | > $x
 |                ^^^^ invoked here
--> help: commands may require specific argument types, use `--help` to view requirements
"#
    );
}

#[test]
fn variable_not_existing() {
    let defs = &Definitions::new();
    let x = process_w_table("\\ 5 | > $x", defs)
        .unwrap_err()
        .to_string();
    assert_eq!(
        &x,
        r#"Semantics Error: variable `x` does not exist
--> shell:9
 | \ 5 | > $x
 |          ^ `x` not in scope
--> help: variables must be in scope and can be defined using the `let` command
"#
    );
    let x = process_w_table("filter { \\ 5 | let $x | \\ 1 | > 0 } | \\ 5 | > $x", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        r#"Semantics Error: variable `x` does not exist
--> shell:47
 | filter { \ 5 | let $x | \ 1 | > 0 } | \ 5 | > $x
 |                                                ^ `x` not in scope
--> help: variables must be in scope and can be defined using the `let` command
"#
    );
}

#[test]
fn test_wrong_arg() {
    let def = &Definitions::new();
    let x = process_w_table("let foo", def).unwrap_err().to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Semantics Error: not expecting argument variant `identifier`
--> shell:4
 | let foo
 |     ^^^ argument variant `identifier` is not supported here
--> help: commands may require specific argument types, use `--help` to view requirements
"
    );
}

#[test]
fn variables_respect_scope() {
    let defs = &mut Definitions::new();
    process_definition(
        "def test-var-scope () { \\ 5 | + $x }",
        Location::Shell,
        None,
        defs,
    )
    .unwrap();
    process_definition(
        "def test-var-scope2 () { \\ 5 | let $x }",
        Location::Shell,
        None,
        defs,
    )
    .unwrap();

    let x = process_w_num("test-var-scope", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        r#"Semantics Error: variable `x` does not exist
--> shell:33
 | def test-var-scope () { \ 5 | + $x }
 |                                  ^ `x` not in scope
--> shell:0
 | test-var-scope
 | ^^^^^^^^^^^^^^ invoked here
--> help: variables must be in scope and can be defined using the `let` command
"#
    );
    let x = process_w_num("let $x | test-var-scope", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        r#"Semantics Error: variable `x` does not exist
--> shell:33
 | def test-var-scope () { \ 5 | + $x }
 |                                  ^ `x` not in scope
--> shell:9
 | let $x | test-var-scope
 |          ^^^^^^^^^^^^^^ invoked here
--> help: variables must be in scope and can be defined using the `let` command
"#
    );
    let x = process_w_num("test-var-scope2 | + $x", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Semantics Error: variable `x` does not exist
--> shell:21
 | test-var-scope2 | + $x
 |                      ^ `x` not in scope
--> help: variables must be in scope and can be defined using the `let` command
"
    );
}

#[test]
fn not_enough_let_params() {
    let defs = &mut Definitions::new();

    let x = process_w_num("let {+ 3} $x {- 3}", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Semantics Error: not expecting argument variant `expression`
--> shell:13
 | let {+ 3} $x {- 3}
 |              ^^^^^ argument variant `expression` is not supported here
--> help: commands may require specific argument types, use `--help` to view requirements
"
    );
}

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

// ------ Map ------------------------------------------------------------------
#[test]
fn map_help_msg() {
    let src = "map --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `map`
--> shell:0
 | replace entry in column with result of an expression
 | `map` provides the variable `$row` which is the TableRow
 | the input into the expression is the value of the entry
 | 
 | Usage:
 |  => map col-name value
 | 
 | Flags:
 |  --<type>: the type that entry has
 |  --force: ignore entry types
 | 
 | Examples:
 |  scale 'size' by dividing by one million
 |  => ls | map size / 1e6
 | 
 |  use a different column and result type
 |  => ls | map type --Str { \\$row.size | + 100 }
"
    );
}

#[test]
fn map_testing() {
    let defs = &Definitions::new();
    let x = process_w_table("map first + 1", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(1), n(3), o("a")],
        vec![n(2), n(20), o("b")],
        vec![n(-29), n(100), o("z")],
    ];
    check_is_table(x, exp);
    let x = process_w_table("map 'Heading 3' --Str { \\$row.first | + 1 }", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), n(1)],
        vec![n(1), n(20), n(2)],
        vec![n(-30), n(100), n(-29)],
    ];
    check_is_table(x, exp);

    // check we can use variables/exprs in column heading
    let x = process_w_table("map { \\ 'Heading 3' } --Str { \\$row.first | + 1 }", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), n(1)],
        vec![n(1), n(20), n(2)],
        vec![n(-30), n(100), n(-29)],
    ];
    check_is_table(x, exp);
    let x = process_w_table(
        "let {\\ 'Heading 3'} $x | map $x --Str { \\$row.first | + 1 }",
        defs,
    );
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), n(1)],
        vec![n(1), n(20), n(2)],
        vec![n(-30), n(100), n(-29)],
    ];
    check_is_table(x, exp);

    // check parallelsiation doesn't wreak havoc
    let x = process_w_nil("range 1 100 | map i { \\$row | + {get i} {get i} }", defs);
    let mut exp = vec![vec![o("i")]];
    exp.extend((1..100).map(|i| vec![n(i * 2)]).collect::<Vec<_>>());
    check_is_table(x, exp);

    // check ignore flag
    let x = process_w_table("map 'Heading 3' --force $row.first", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), n(0)],
        vec![n(1), n(20), n(1)],
        vec![n(-30), n(100), n(-30)],
    ];
    check_is_table(x, exp);
}

// ------ Min Max --------------------------------------------------------------
#[test]
fn min_help_msg() {
    let src = "min --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `min`
--> shell:0
 | return the minimum value
 | -variadic-: more than one argument can be specified
 | 
 | Usage:
 |  => min args..
 | 
 | Examples:
 |  minimum of 2 and 3
 |  => \\ 2 | min 3
 | 
 |  minimum of multiple args
 |  => min 1 2 3 4 5
"
    );
}

#[test]
fn max_help_msg() {
    let src = "max --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `max`
--> shell:0
 | return the maximum value
 | -variadic-: more than one argument can be specified
 | 
 | Usage:
 |  => max args..
 | 
 | Examples:
 |  maximum of 2 and 3
 |  => \\ 2 | max 3
 | 
 |  maximum of multiple args
 |  => max 1 2 3 4 5
"
    );
}

#[test]
fn min_max_testing() {
    let defs = &Definitions::new();
    let x = process_w_num("max 101 ", defs);
    assert_eq!(x, Ok(Value::Num(101.into())));
    let x = process_w_num("min 101 ", defs);
    assert_eq!(x, Ok(Value::Num(3.into())));
    let x = process_w_num("min 101 0", defs);
    assert_eq!(x, Ok(Value::Num(0.into())));
    let x = process_w_num("max 101 0", defs);
    assert_eq!(x, Ok(Value::Num(101.into())));
}

// ------ Mod ------------------------------------------------------------------
#[test]
fn mod_help_msg() {
    let src = "mod --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `mod`
--> shell:0
 | user defined implementation in <ogma>
 | `def mod Num (denom) { - {/ $denom | floor | * $denom} }`
 | return the modulus of a number
 | 
 | Usage:
 |  => mod denom
 | 
 | Examples:
 |  return remainder of 35 divided by 3
 |  => \\ 35 | mod 3
"
    );
}

#[test]
fn mod_testing() {
    let defs = &Definitions::new();
    let x = process_w_num("mod 2", defs);
    assert_eq!(x, Ok(Value::Num(1.into())));
    let x = process_w_num("* 7 | mod 5", defs);
    assert_eq!(x, Ok(Value::Num(1.into())));
}

// ------ Mul ------------------------------------------------------------------
#[test]
fn mul_help_msg() {
    let src = "* --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `*`
--> shell:0
 | multiply arguments together
 | -variadic-: more than one argument can be specified
 | 
 | Usage:
 |  => * args..
 | 
 | Examples:
 |  multiply 2 three times
 |  => \\ 2 | * 3
 | 
 |  multiply multiple numbers together
 |  => × 1 2 3 4 5
"
    );
}

#[test]
fn mul_testing() {
    let defs = &Definitions::new();
    let x = process_w_num("* 101 ", defs);
    assert_eq!(x, Ok(Value::Num(303.into())));
    let x = process_w_num("* 101 0", defs);
    assert_eq!(x, Ok(Value::Num(0.into())));
    let x = process_w_num("let $x | \\ 1 | × 1 2 $x", defs);
    assert_eq!(x, Ok(Value::Num(6.into()))); // 1 * 1 * 2 * 3
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

// ------ Nth ------------------------------------------------------------------
#[test]
fn nth_help_msg() {
    let src = "nth --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `nth`
--> shell:0
 | retrieve the nth element of a data structure
 | String: retrieves the nth character
 | Table: retrieves the nth row and applies the expression
 | 
 | Usage:
 |  => nth index [expr]
 | 
 | Examples:
 |  get the first row of a table
 |  => nth 0 {get col-name}
 | 
 |  get the 2nd last row of a table
 |  => nth {len | - 2} {get col-name}
 | 
 |  get the 10th character of a string
 |  => \\ 'Hello, world!' | nth 10
"
    );
}

#[test]
fn nth_testing() {
    let defs = &Definitions::new();

    // table
    let x = process_w_table("nth 0 {get first}", defs);
    assert_eq!(x, Ok(Value::Num(0.into())));
    let x = process_w_table("nth 2 {get first}", defs);
    assert_eq!(x, Ok(Value::Num((-30).into())));
    let x = process_w_table("nth {\\ 1 | + 2} {get first}", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        r#"Evaluation Error: index is outside table bounds
--> shell:4
 | nth {\ 1 | + 2} {get first}
 |     ^^^^^^^^^^^ this resolves to `3`
"#
    );

    // string
    let x = process_w_str("nth 0", defs);
    assert_eq!(x, Ok(Value::Str("H".into())));
    let x = process_w_str("nth 4", defs);
    assert_eq!(x, Ok(Value::Str("o".into())));
    let x = process_w_str("nth 20", defs).unwrap_err().to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Evaluation Error: index is outside string bounds
--> shell:4
 | nth 20
 |     ^^ this resolves to `20`
"
    );
}

#[test]
fn open_bom_test() {
    let defs = &Definitions::new();

    let exp = vec![
        vec![o("English name"), o("Native name")],
        vec![o("English"), o("English")],
        vec![o("German"), o("Deutsch")],
        vec![o("French"), o("Français")],
        vec![o("Russian"), o("Русский")],
        vec![o("Japanese"), o("日本語")],
    ];

    let utf8 = {
        std::fs::write("ls-test/test-bom.csv", b"English name,Native name\nEnglish,English\nGerman,Deutsch\nFrench,Fran\xc3\xa7ais\nRussian,\xd0\xa0\xd1\x83\xd1\x81\xd1\x81\xd0\xba\xd0\xb8\xd0\xb9\nJapanese,\xe6\x97\xa5\xe6\x9c\xac\xe8\xaa\x9e\n").unwrap();
        process_w_nil("open 'ls-test/test-bom.csv'", defs)
    };

    let utf8bom = {
        std::fs::write("ls-test/test-bom.csv", b"\xef\xbb\xbfEnglish name,Native name\nEnglish,English\nGerman,Deutsch\nFrench,Fran\xc3\xa7ais\nRussian,\xd0\xa0\xd1\x83\xd1\x81\xd1\x81\xd0\xba\xd0\xb8\xd0\xb9\nJapanese,\xe6\x97\xa5\xe6\x9c\xac\xe8\xaa\x9e\n").unwrap();
        process_w_nil("open 'ls-test/test-bom.csv'", defs)
    };

    let utf16le = {
        std::fs::write("ls-test/test-bom.csv", b"\xff\xfeE\x00n\x00g\x00l\x00i\x00s\x00h\x00 \x00n\x00a\x00m\x00e\x00,\x00N\x00a\x00t\x00i\x00v\x00e\x00 \x00n\x00a\x00m\x00e\x00\n\x00E\x00n\x00g\x00l\x00i\x00s\x00h\x00,\x00E\x00n\x00g\x00l\x00i\x00s\x00h\x00\n\x00G\x00e\x00r\x00m\x00a\x00n\x00,\x00D\x00e\x00u\x00t\x00s\x00c\x00h\x00\n\x00F\x00r\x00e\x00n\x00c\x00h\x00,\x00F\x00r\x00a\x00n\x00\xe7\x00a\x00i\x00s\x00\n\x00R\x00u\x00s\x00s\x00i\x00a\x00n\x00,\x00 \x04C\x04A\x04A\x04:\x048\x049\x04\n\x00J\x00a\x00p\x00a\x00n\x00e\x00s\x00e\x00,\x00\xe5e,g\x9e\x8a\n\x00").unwrap();
        process_w_nil("open 'ls-test/test-bom.csv'", defs)
    };

    let utf16be = {
        std::fs::write("ls-test/test-bom.csv", b"\xfe\xff\x00E\x00n\x00g\x00l\x00i\x00s\x00h\x00 \x00n\x00a\x00m\x00e\x00,\x00N\x00a\x00t\x00i\x00v\x00e\x00 \x00n\x00a\x00m\x00e\x00\n\x00E\x00n\x00g\x00l\x00i\x00s\x00h\x00,\x00E\x00n\x00g\x00l\x00i\x00s\x00h\x00\n\x00G\x00e\x00r\x00m\x00a\x00n\x00,\x00D\x00e\x00u\x00t\x00s\x00c\x00h\x00\n\x00F\x00r\x00e\x00n\x00c\x00h\x00,\x00F\x00r\x00a\x00n\x00\xe7\x00a\x00i\x00s\x00\n\x00R\x00u\x00s\x00s\x00i\x00a\x00n\x00,\x04 \x04C\x04A\x04A\x04:\x048\x049\x00\n\x00J\x00a\x00p\x00a\x00n\x00e\x00s\x00e\x00,e\xe5g,\x8a\x9e\x00\n").unwrap();
        process_w_nil("open 'ls-test/test-bom.csv'", defs)
    };

    check_is_table(utf8, exp.clone());
    check_is_table(utf8bom, exp.clone());
    check_is_table(utf16le, exp.clone());
    check_is_table(utf16be, exp.clone());
}

// ------ Or -------------------------------------------------------------------
#[test]
fn or_help_msg() {
    let src = "or --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `or`
--> shell:0
 | returns true if any arguments are true
 | -variadic-: more than one argument can be specified
 | 
 | Usage:
 |  => or args..
 | 
 | Examples:
 |  1 is less than OR equal to 2
 |  => \\ 1 | or { < 2 } { = 2 }
"
    );
}

#[test]
fn or_test() {
    let defs = &Definitions::new();
    let x = process_w_num("eq 3 | or { \\ 2 | > 1 }", defs);
    assert_eq!(x, Ok(Value::Bool(true)));
    let x = process_w_num("or { > 4 } { = 3 }", defs);
    assert_eq!(x, Ok(Value::Bool(true)));
    let x = process_w_num("or { > 3 } { = 4 }", defs);
    assert_eq!(x, Ok(Value::Bool(false)));

    // test that table rows can be used with an or!
    let x = process_w_table("filter snd or { > 5 } { > 20 }", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    check_is_table(x, exp);
}

// ------ Pick -----------------------------------------------------------------
#[test]
fn pick_help_msg() {
    let src = "pick --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `pick`
--> shell:0
 | pick out columns to keep in a table, in order
 | 
 | Usage:
 |  => pick col-name..
 | 
 | Flags:
 |  --add: add a blank column if it does not exist in the table
 |  --trail: append any remaining columns in order
 | 
 | Examples:
 |  choose the size, name, and type columns
 |  => ls | pick name size type
"
    );
}

#[test]
fn pick_testing() {
    let defs = &Definitions::new();

    let x = process_w_table("pick first snd 'Heading 3'", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    check_is_table(x, exp);

    let x = process_w_table("pick snd first 'Heading 3'", defs);
    let exp = vec![
        vec![o("snd"), o("first"), o("Heading 3")],
        vec![n(3), n(0), o("a")],
        vec![n(20), n(1), o("b")],
        vec![n(100), n(-30), o("z")],
    ];
    check_is_table(x, exp);

    let x = process_w_table("pick 'Heading 3' snd snd", defs);
    let exp = vec![
        vec![o("Heading 3"), o("snd"), o("snd")],
        vec![o("a"), n(3), n(3)],
        vec![o("b"), n(20), n(20)],
        vec![o("z"), n(100), n(100)],
    ];
    check_is_table(x, exp);
}

#[test]
fn pick_add_testing() {
    let defs = &Definitions::new();

    let x = process_w_table("pick --add a first b", defs);
    let exp = vec![
        vec![o("a"), o("first"), o("b")],
        vec![Nil, n(0), Nil],
        vec![Nil, n(1), Nil],
        vec![Nil, n(-30), Nil],
    ];
    check_is_table(x, exp);
}

#[test]
fn pick_trail_testing() {
    let defs = &Definitions::new();

    let x = process_w_table("pick --trail snd", defs);
    let exp = vec![
        vec![o("snd"), o("first"), o("Heading 3")],
        vec![n(3), n(0), o("a")],
        vec![n(20), n(1), o("b")],
        vec![n(100), n(-30), o("z")],
    ];
    check_is_table(x, exp);

    let x = process_w_table("pick --add --trail snd snd a b", defs);
    let exp = vec![
        vec![
            o("snd"),
            o("snd"),
            o("a"),
            o("b"),
            o("first"),
            o("Heading 3"),
        ],
        vec![n(3), n(3), Nil, Nil, n(0), o("a")],
        vec![n(20), n(20), Nil, Nil, n(1), o("b")],
        vec![n(100), n(100), Nil, Nil, n(-30), o("z")],
    ];
    check_is_table(x, exp);
}

#[test]
fn pick_err_testing() {
    let defs = &Definitions::new();

    let x = process_w_table("pick first snd third", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Evaluation Error: header `third` not found in table
--> shell:15
 | pick first snd third
 |                ^^^^^ `third` resolves to `third`
"
    );
}

// ------ Rand -----------------------------------------------------------------
#[test]
fn rand_help_msg() {
    let src = "rand --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `rand`
--> shell:0
 | return a random number
 | rand has four ways of calling:
 | 1. Without arguments: this returns a number (0,1],
 | 2. With one argument: this returns a number (0,to],
 | 3. With two arguments: this returns a number (from,to],
 | 4. With three arguments: this returns a table populated with random numbers (from,to]
 | 
 | Usage:
 |  => rand [from] [to] [length]
 | 
 | Examples:
 |  random integer from 0 to 9
 |  => rand 0 10 | floor
 | 
 |  create 10 random numbers
 |  => rand 0 1 10
"
    );
}

#[test]
fn rand_test() {
    let defs = &Definitions::new();
    let x = process_w_nil("rand | floor", defs);
    assert_eq!(x, Ok(Value::Num(0.into())));

    let x = process_w_nil("rand 1 | floor", defs);
    assert_eq!(x, Ok(Value::Num(0.into())));

    let x = process_w_nil("rand 9 10 | floor", defs);
    assert_eq!(x, Ok(Value::Num(9.into())));

    let x = process_w_nil("rand 0 -1", defs).unwrap_err().to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Evaluation Error: from must be less than to. found from: 0 to: -1
--> shell:0
 | rand 0 -1
 | ^^^^
"
    );

    let x = process_w_nil("rand 0 1 5 | map 'rand' floor", defs);
    check_is_table(
        x,
        vec![
            vec![o("rand")],
            vec![n(0)],
            vec![n(0)],
            vec![n(0)],
            vec![n(0)],
            vec![n(0)],
        ],
    );
}

// ------ Range ----------------------------------------------------------------
#[test]
fn range_help_msg() {
    let src = "range --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `range`
--> shell:0
 | create a single column table of integers (from,to]
 | `from` is inclusive, `to` is exclusive
 | `to` can be omitted if input is a number
 | 
 | Usage:
 |  => range from [to]
 | 
 | Examples:
 |  integers from 0 to 9
 |  => range 0 10
 | 
 |  the five preceding numbers
 |  => \\ 10 | range - 5
"
    );
}

#[test]
fn range_test() {
    let defs = &Definitions::new();
    let x = process_w_nil("range 0 2", defs);
    let exp = vec![vec![o("i")], vec![n(0)], vec![n(1)]];
    check_is_table(x, exp);

    let x = process_w_num("range 1", defs);
    let exp = vec![vec![o("i")], vec![n(1)], vec![n(2)]];
    check_is_table(x, exp);

    let x = process_w_nil("range 0 -1", defs).unwrap_err().to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Evaluation Error: could not convert number into unsigned integer
--> shell:8
 | range 0 -1
 |         ^^ -1 does not convert to uint
"
    );

    let x = process_w_nil("range 3.14 1.2e3", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Evaluation Error: could not convert number into unsigned integer
--> shell:6
 | range 3.14 1.2e3
 |       ^^^^ 3.14 does not convert to uint
"
    );
}

// ------ Ren ------------------------------------------------------------------
#[test]
fn ren_help_msg() {
    let src = "ren --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `ren`
--> shell:0
 | rename column headers
 | each binding takes the form `<col-ref> <name>`
 | `<col-ref>` can be a string or a column index number
 | 
 | Usage:
 |  => ren [<col-ref-1> <name-1>] [<col-ref-2> <name-2>] ...
 | 
 | Examples:
 |  rename foo to bar and bar to foo
 |  => ren foo bar bar foo
 | 
 |  rename idx 0 to foo
 |  => ren 0 foo
"
    );
}

#[test]
fn ren_testing() {
    let defs = &Definitions::new();

    let x = process_w_table("ren first hello", defs);
    let exp = vec![
        vec![o("hello"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    check_is_table(x, exp);

    let x = process_w_table("ren first hello snd hello2", defs);
    let exp = vec![
        vec![o("hello"), o("hello2"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    check_is_table(x, exp);

    let x = process_w_table("ren 0 hello snd hello2", defs);
    let exp = vec![
        vec![o("hello"), o("hello2"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    check_is_table(x, exp);
}

#[test]
fn ren_err_testing() {
    let defs = &Definitions::new();

    let x = process_w_table("ren frist hello", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Evaluation Error: header `frist` not found in table
--> shell:4
 | ren frist hello
 |     ^^^^^ `frist` resolves to `frist`
"
    );

    let x = process_w_table("ren first", defs).unwrap_err().to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Semantics Error: too many arguments supplied
--> shell:4
 | ren first
 |     ^^^^^ identifier argument is unnecessary
--> help: the command does not require or support additional arguments
"
    );
}

// ------ Ren-With -------------------------------------------------------------
#[test]
fn ren_with_help_msg() {
    let src = "ren-with --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `ren-with`
--> shell:0
 | rename column headers using a row as a seed
 | each entry is fed into the expression, which returns a string
 | the default entry type required is a string
 | 
 | Usage:
 |  => ren-with row-idx name-expr
 | 
 | Flags:
 |  --<type>: the type of the entry
 | 
 | Examples:
 |  rename the header with what is in row 2
 |  => ren-with 2 #i
 | 
 |  append the headers with something
 |  => ren-with 0 + ' bar'
 | 
 |  use the first row as a header and forget the old one
 |  => ren-with 1 #i | skip 1
"
    );
}

#[test]
fn ren_with_testing() {
    let defs = &Definitions::new();

    let x = process_w_table("map first to-str | map snd to-str | ren-with 1 #i", defs);
    let exp = vec![
        vec![o("0"), o("3.0"), o("a")],
        vec![o("0"), o("3.0"), o("a")],
        vec![o("1.0"), o("20.0"), o("b")],
        vec![o("-30.0"), o("100.0"), o("z")],
    ];
    check_is_table(x, exp);

    // test the derived impl skip-hdrs
    let x = process_w_table("map first to-str | map snd to-str | skip-hdrs 2", defs);
    let exp = vec![
        vec![o("1.0"), o("20.0"), o("b")],
        vec![o("-30.0"), o("100.0"), o("z")],
    ];
    check_is_table(x, exp);
}

#[test]
fn ren_with_err_testing() {
    let defs = &Definitions::new();

    let x = process_w_table("ren-with 1 hello", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Evaluation Error: table entry for [row:1,col:'0'] did not have expected type
expected `String`, found `Number`
--> shell:9
 | ren-with 1 hello
 |          ^
--> help: column entries must have a matching type
"
    );

    let x = process_w_table("ren-with 100 foo", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Evaluation Error: row index `100` is outside table bounds
--> shell:9
 | ren-with 100 foo
 |          ^^^ `100` resolves to 100
--> help: use `len` command to check the size of the table
"
    );

    let x = process_w_table("\\Table | ren-with 100 foo", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Evaluation Error: empty table
--> shell:9
 | \\Table | ren-with 100 foo
 |          ^^^^^^^^^^^^^^^^
"
    );
}

// ------ Rev ------------------------------------------------------------------
#[test]
fn rev_help_msg() {
    let src = "rev --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `rev`
--> shell:0
 | reverse the order of the input
 | for String inputs; character ordering is reversed
 | for Table inputs; row or col ordering is reversed
 | 
 | Usage:
 |  => rev
 | 
 | Flags:
 |  --cols: reverse table column ordering
 | 
 | Examples:
 |  reverse table row ordering
 |  => ls | rev
 | 
 |  reverse string character ordering
 |  => \\ '!dlrow ,olleH' | rev
"
    );
}

#[test]
fn rev_testing() {
    let defs = &Definitions::new();

    let x = process_w_table("rev", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(-30), n(100), o("z")],
        vec![n(1), n(20), o("b")],
        vec![n(0), n(3), o("a")],
    ];
    check_is_table(x, exp);

    let x = process_w_table("rev --cols", defs);
    let exp = vec![
        vec![o("Heading 3"), o("snd"), o("first")],
        vec![o("a"), n(3), n(0)],
        vec![o("b"), n(20), n(1)],
        vec![o("z"), n(100), n(-30)],
    ];
    check_is_table(x, exp);

    let x = process_w_table("sort 'Heading 3' | rev", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(-30), n(100), o("z")],
        vec![n(1), n(20), o("b")],
        vec![n(0), n(3), o("a")],
    ];
    check_is_table(x, exp);

    let x = process_w_str("rev", defs);
    assert_eq!(x, Ok(Value::Str(Str::from("olleH"))));
}

// ------ Root -----------------------------------------------------------------
#[test]
fn root_help_msg() {
    let src = "root --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `root`
--> shell:0
 | calculate the nth root of a number
 | 
 | Usage:
 |  => root index
 | 
 | Examples:
 |  the square root of 4
 |  => \\ 4 | root 2
 | 
 |  the cube root of 27
 |  => \\ 27 | root 3
"
    );
}

#[test]
fn root_testing() {
    let defs = &Definitions::new();
    let x = process_w_num("* 9 | root 3 | - 3 | abs | < 1e-10", defs);
    assert_eq!(x, Ok(Value::Bool(true)));
    let x = process_w_num("\\ 16 | root 2 | - 4 | abs | < 1e-10", defs);
    assert_eq!(x, Ok(Value::Bool(true)));
    let x = process_w_num("\\ 16 | root 4 | - 2 | abs | < 1e-10", defs);
    assert_eq!(x, Ok(Value::Bool(true)));
}

// ------ Skip -----------------------------------------------------------------
#[test]
fn skip_help_msg() {
    let src = "skip --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `skip`
--> shell:0
 | skip the first n elements of a data structure
 | 
 | Usage:
 |  => skip count
 | 
 | Examples:
 |  skip the first 10 rows of a table
 |  => skip 10
 | 
 |  skip the first 5 characters of a string
 |  => \\ 'Hello, world!' | skip 5
 | 
 |  skip and take can be used to slice into a string
 |  => \\ 'Hello, world!' | skip 7 | take 5
"
    );
}

#[test]
fn skip_testing() {
    let defs = &Definitions::new();

    // table
    let x = process_w_table("skip 0", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    check_is_table(x, exp);

    let x = process_w_table("skip 2", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(-30), n(100), o("z")],
    ];
    check_is_table(x, exp);
    let x = process_w_table("let $n | skip 2", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(-30), n(100), o("z")],
    ];
    check_is_table(x, exp);

    let x = process_w_table("skip 5", defs);
    let exp = vec![vec![o("first"), o("snd"), o("Heading 3")]];
    check_is_table(x, exp);

    // string
    let x = process_w_str("skip 0", defs);
    assert_eq!(x, Ok(Value::Str("Hello".into())));
    let x = process_w_str("skip 2", defs);
    assert_eq!(x, Ok(Value::Str("llo".into())));
    let x = process_w_str("skip 5", defs);
    assert_eq!(x, Ok(Value::Str("".into())));
}

// ------ Sort -----------------------------------------------------------------
#[test]
fn sort_help_msg() {
    let src = "sort --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `sort`
--> shell:0
 | sort a table by column headers
 | each header sorts the rows lowest to highest in a canonical fashion,
 | in order specified (1st column is sorted first)
 | this sorts different value types, but NOT user-defined types. see `sort-by`
 | 
 | Usage:
 |  => sort col-name..
 | 
 | Examples:
 |  sort ls by file size
 |  => ls | sort size
 | 
 |  sort ls by ext, THEN by size (notice the inverted order)
 |  => ls | sort size ext
"
    );
}

#[test]
fn sort_testing() {
    let defs = &Definitions::new();

    let x = process_w_table("sort first", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(-30), n(100), o("z")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
    ];
    check_is_table(x, exp);
    let x = process_w_table("sort first 'Heading 3'", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    check_is_table(x, exp);
}

#[test]
fn empty_sort_err() {
    let defs = &Definitions::new();
    let x = process_w_table("sort", defs).unwrap_err().to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Semantics Error: expecting more than 0 arguments
--> shell:0
 | sort
 | ^^^^ expecting additional argument(s)
--> help: try using the `--help` flag to view requirements
"
    );
}

// ------ Sort-by --------------------------------------------------------------
#[test]
fn sortby_help_msg() {
    let src = "sort-by --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `sort-by`
--> shell:0
 | sort table using an expression
 | the result of the expression must define a `cmp` implementation
 | this can be used to sort user-defined types
 | 
 | Usage:
 |  => sort-by <expr>
 | 
 | Examples:
 |  sort ls by file size
 |  => ls | sort-by { get size }
 | 
 |  sort using a user-defined type
 |  => ls | sort-by { Point { get size } }
"
    );
}

#[test]
fn sortby_testing() {
    let defs = &Definitions::new();

    let x = process_w_table("sort-by { get first }", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(-30), n(100), o("z")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
    ];
    check_is_table(x, exp);

    let x = process_w_table("sort-by { get first | if { < 0 } { * -1 } { + 0 } }", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    check_is_table(x, exp);

    let x = process_w_table("sort-by { get snd | * -1 }", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(-30), n(100), o("z")],
        vec![n(1), n(20), o("b")],
        vec![n(0), n(3), o("a")],
    ];
    check_is_table(x, exp);

    let x = process_w_table("let $x | sort-by { get snd | * -1 }", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(-30), n(100), o("z")],
        vec![n(1), n(20), o("b")],
        vec![n(0), n(3), o("a")],
    ];
    check_is_table(x, exp);
}

#[test]
fn sortby_errors() {
    let defs = &mut Definitions::new();

    process_definition("def-ty Point { x:Num y:Num }", Location::Shell, None, defs).unwrap();

    let x = process_w_table("sort-by Point 1 0", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Semantics Error: `cmp` implementation not suitable for `sort-by` with `Point`
--> shell:8
 | sort-by Point 1 0
 |         ^^^^^^^^^ this returns `Point`
--> help: `cmp` implementation expects T=>(rhs:T) -> Ord
"
    );

    process_definition(
        "def cmp Point (rhs x) { \\ $x }",
        Location::Shell,
        None,
        defs,
    )
    .unwrap();

    let x = process_w_table("sort-by Point 1 0", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Semantics Error: `cmp` implementation not suitable for `sort-by` with `Point`
--> shell:8
 | sort-by Point 1 0
 |         ^^^^^^^^^ this returns `Point`
--> help: `cmp` implementation expects T=>(rhs:T) -> Ord
"
    );

    process_definition(
        "def cmp Point (rhs) { \\ $rhs }",
        Location::Shell,
        None,
        defs,
    )
    .unwrap();

    let x = process_w_table("sort-by Point 1 0", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Semantics Error: expecting argument with type `Ord`, found `Point`
--> <ogma>:0
 | cmp $rhs
 | ^^^^^^^^ this argument returns type `Point`
--> shell:8
 | sort-by Point 1 0
 |         ^^^^^^^^^ `Point`'s cmp impl returns `Point`
--> help: commands may require specific argument types, use `--help` to view requirements
"
    );
}

// ------ Sub ------------------------------------------------------------------
#[test]
fn sub_help_msg() {
    let src = "- --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `-`
--> shell:0
 | subtract arguments from one another
 | note: if input is not a Num, the first arg is used as lhs
 | -variadic-: more than one argument can be specified
 | 
 | Usage:
 |  => - args..
 | 
 | Examples:
 |  subtract 2 from 1
 |  => \\ 1 | - 2
 | 
 |  subtract 1 - 2 = -1
 |  => - 1 2
 | 
 |  subtract multiple numbers together
 |  => - 1 2 3 4 5
"
    );
}

#[test]
fn sub_testing() {
    let defs = &Definitions::new();
    let x = process_w_num("- 5", defs);
    assert_eq!(x, Ok(Value::Num((-2).into())));
    let x = process_w_nil("- -2 -1", defs);
    assert_eq!(x, Ok(Value::Num((-1).into())));
    let x = process_w_num("let $x | \\ 1 | - 1 2 $x", defs);
    assert_eq!(x, Ok(Value::Num((-5).into()))); // 1 - 1 - 2 - 3
}

// ------ Table ctor -----------------------------------------------------------
#[test]
fn table_help_msg() {
    let src = "Table --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `Table`
--> shell:0
 | create an empty table with the given table headers
 | -variadic-: more than one argument can be specified
 | 
 | Usage:
 |  => Table args..
 | 
 | Examples:
 |  create an empty table
 |  => Table
 | 
 |  create table with the headers 'Foo' and 'Bar'
 |  => Table 'Foo' 'Bar'
"
    );
}

#[test]
fn table_testing() {
    let defs = &Definitions::new();

    let x = process_w_nil("Table", defs);
    check_is_table(x, vec![]);

    let x = process_w_nil("Table 'Foo' Bar 'Heading 3'", defs);
    let exp = vec![vec![o("Foo"), o("Bar"), o("Heading 3")]];
    check_is_table(x, exp);
    let x = process_w_num("Table {+ 1 | to-str} {+ 2 | to-str}", defs);
    let exp = vec![vec![o("4.0"), o("5.0")]];
    check_is_table(x, exp);
}

// ------ Take -----------------------------------------------------------------
#[test]
fn take_help_msg() {
    let src = "take --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `take`
--> shell:0
 | take the first n elements of a data structure
 | 
 | Usage:
 |  => take count
 | 
 | Examples:
 |  take the first 10 rows of a table
 |  => take 10
 | 
 |  take the first 5 characters of a string
 |  => \\ 'Hello, world!' | take 5
 | 
 |  skip and take can be used to slice into a string
 |  => \\ 'Hello, world!' | skip 7 | take 5
"
    );
}

#[test]
fn take_testing() {
    let defs = &Definitions::new();

    // table
    let x = process_w_table("take 0", defs);
    let exp = vec![vec![o("first"), o("snd"), o("Heading 3")]];
    check_is_table(x, exp);

    let x = process_w_table("take 2", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
    ];
    check_is_table(x, exp);
    let x = process_w_table("let $n | take 2", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
    ];
    check_is_table(x, exp);

    let x = process_w_table("take 5", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    check_is_table(x, exp);

    // string
    let x = process_w_str("take 0", defs);
    assert_eq!(x, Ok(Value::Str("".into())));
    let x = process_w_str("take 2", defs);
    assert_eq!(x, Ok(Value::Str("He".into())));
    let x = process_w_str("take 5", defs);
    assert_eq!(x, Ok(Value::Str("Hello".into())));
}

// ------ To-str ---------------------------------------------------------------
#[test]
fn to_str_help_msg() {
    let src = "to-str --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `to-str`
--> shell:0
 | convert the input into a string
 | 
 | Usage:
 |  => to-str
"
    );
}

#[test]
fn to_str_testing() {
    let defs = &Definitions::new();
    let x = process_w_num("to-str", defs);
    assert_eq!(x, Ok(Value::Str("3.0".into())));
}

// ------ Tuples ---------------------------------------------------------------
#[test]
fn tuple_help_msg() {
    let src = "Tuple --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `Tuple`
--> shell:0
 | construct a tuple of the result of each expression
 | tuples impl `eq` and `cmp` if all its fields also implement `eq` and `cmp`
 | tuples have unique types: `U_<t0_Ty>-<t1_Ty>_`
 | access of the fields is using `get t#` with the field number
 | -variadic-: more than one argument can be specified
 | 
 | Usage:
 |  => Tuple args..
 | 
 | Examples:
 |  create a two element tuple of numbers. type: U_Num-Num_
 |  => Tuple 1 2
 | 
 |  create 3 numbers after input. type: U_Num-Num-Num_
 |  => \\ 3 | Tuple {+ 1} {+ 2} {+ 3}
 | 
 |  tuples are heterogeneous. type: U_Num-Str-Bool_
 |  => Tuple 1 'foo' #t
 | 
 |  get the first and third element
 |  => Tuple 1 'foo' 2 | + {get t0} {get t2}
"
    );
}

#[test]
fn tuple_testing() {
    let defs = &Definitions::new();

    let print = |s| match process_w_num(s, defs) {
        Ok(Value::Ogma(x)) => print_ogma_data(x),
        e => panic!("not expecting {:?}", e),
    };

    let x = print("Tuple #i 'foo' + 2 3");
    assert_eq!(&x, "U_Num-Str-Num_ (t0 = 3, t1 = \"foo\", t2 = 8)");

    let x = process_w_nil("Tuple #i 1 2 3 | get t3", defs);
    assert_eq!(x, Ok(Value::Num(3.into())));
}

#[test]
fn tuple_err_testing() {
    let defs = &Definitions::new();

    let x = process_w_nil("Tuple 1 'foo' | get t3", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Semantics Error: `U_Num-Str_` does not contain field `t3`
--> shell:20
 | Tuple 1 'foo' | get t3
 |                     ^^ `t3` not found
"
    );
}

#[test]
fn tuple_eq_testing() {
    let defs = &Definitions::new();

    let x = process_w_nil("Tuple 1 2 'foo' | eq Tuple 1 2 'foo'", defs);
    assert_eq!(x, Ok(Value::Bool(true)));
    let x = process_w_nil("Tuple 1 2 3 | eq Tuple 1 3 3", defs);
    assert_eq!(x, Ok(Value::Bool(false)));

    let x = process_w_nil("Tuple 1 'foo' | eq Tuple 'foo' 1", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Semantics Error: expecting argument with type `U_Num-Str_`, found `U_Str-Num_`
--> shell:19
 | Tuple 1 'foo' | eq Tuple 'foo' 1
 |                    ^^^^^^^^^^^^^ this argument returns type `U_Str-Num_`
--> shell:19
 | Tuple 1 'foo' | eq Tuple 'foo' 1
 |                    ^^^^^^^^^^^^^ invoked here
--> help: commands may require specific argument types, use `--help` to view requirements
"
    );
}

#[test]
fn tuple_cmp_testing() {
    let defs = &Definitions::new();

    let x = process_w_nil("Tuple 1 2 'foo' | cmp Tuple 1 2 'foo'", defs);
    is_eq(x);
    let x = process_w_nil("Tuple 1 2 3 | cmp Tuple 1 3 3", defs);
    is_lt(x);
    let x = process_w_nil("Tuple 1 'foo' 3 | cmp Tuple 1 'bar' 3", defs);
    is_gt(x);

    let x = process_w_nil("Tuple 1 'foo' | cmp Tuple 'foo' 1", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Semantics Error: expecting argument with type `U_Num-Str_`, found `U_Str-Num_`
--> shell:20
 | Tuple 1 'foo' | cmp Tuple 'foo' 1
 |                     ^^^^^^^^^^^^^ this argument returns type `U_Str-Num_`
--> shell:20
 | Tuple 1 'foo' | cmp Tuple 'foo' 1
 |                     ^^^^^^^^^^^^^ invoked here
--> help: commands may require specific argument types, use `--help` to view requirements
"
    );
}

#[test]
fn tuples_in_tables_work() {
    let defs = &Definitions::new();
    let x = process_w_table(
        "append --foo Tuple {get first} {get snd} | map foo --U_Num-Num_ get t0",
        defs,
    );
    check_is_table(
        x,
        vec![
            vec![o("first"), o("snd"), o("Heading 3"), o("foo")],
            vec![n(0), n(3), o("a"), n(0)],
            vec![n(1), n(20), o("b"), n(1)],
            vec![n(-30), n(100), o("z"), n(-30)],
        ],
    );
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
