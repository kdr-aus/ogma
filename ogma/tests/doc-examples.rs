use libs::divvy::Str;
use ogma::lang::ast::Location;
use ogma::lang::{Definitions, Value};
use std::path::Path;
use table::Entry::{self, Nil};

type Result<T> = std::result::Result<T, ogma::Error>;

fn paths() -> (&'static Path, &'static Path) {
    (Path::new("."), Path::new("../ogma"))
}

fn process(src: &str, defs: &Definitions) -> Result<Value> {
    let (root, wd) = paths();
    ogma::rt::process_expression((), src, Location::Shell, defs, root, wd)
}

fn process_def(def: &str, defs: &mut Definitions) {
    ogma::lang::process_definition(def, Location::Shell, None, defs).unwrap();
}

fn check_is_table(r: Result<Value>, table: Vec<Vec<Entry<Value>>>) {
    match r {
        Ok(Value::Tab(tab)) => {
            assert_eq!(tab, ogma::lang::Table::from(::table::Table::from(table)));
        }
        Err(e) => {
            println!("{}", e);
            panic!("returned err: {:?}", e)
        }
        x => panic!("not a table: {:?}", x),
    }
}

fn n<N: Into<::kserd::Number>>(n: N) -> Entry<Value> {
    Entry::Num(n.into())
}
fn s(s: &str) -> Entry<Value> {
    Entry::Obj(Value::Str(Str::new(s)))
}

// #### 2.2 FizzBuzz ###########################################################

fn _2_2_fizzbuzz_exp() -> Vec<Vec<Entry<Value>>> {
    vec![
        vec![s("i")],
        vec![s("1.0")],
        vec![s("2.0")],
        vec![s("Fizz")],
        vec![s("4.0")],
        vec![s("Buzz")],
        vec![s("Fizz")],
        vec![s("7.0")],
        vec![s("8.0")],
        vec![s("Fizz")],
        vec![s("Buzz")],
        vec![s("11.0")],
        vec![s("Fizz")],
        vec![s("13.0")],
        vec![s("14.0")],
        vec![s("FizzBuzz")],
        vec![s("16.0")],
        vec![s("17.0")],
        vec![s("Fizz")],
        vec![s("19.0")],
        vec![s("Buzz")],
    ]
}

#[test]
fn _2_2_fizzbuzz_01() {
    let x = process(
        r#"range 1 21 | map i { let $e |
    if { \$e | mod 3 | = 0 } 'Fizz' '' |
    + if { \$e | mod 5 | = 0 } 'Buzz' '' |
    if {empty} { \$e | to-str } #i
} 
"#,
        &Definitions::new(),
    );

    check_is_table(x, _2_2_fizzbuzz_exp());
}

#[test]
fn _2_2_fizzbuzz_02() {
    let defs = &mut Definitions::new();

    process_def(
        "def if-div Num (div:Num yes:Str) { mod $div | if {= 0} $yes '' }",
        defs,
    );

    let x = process("\\ 1 | if-div 3 'Fizz'", defs);
    assert_eq!(x, Ok(Value::Str(Str::from(""))));
    let x = process("\\ 15 | if-div 3 'Fizz'", defs);
    assert_eq!(x, Ok(Value::Str(Str::from("Fizz"))));
    let x = process("\\ 15 | if-div 5 'Buzz'", defs);
    assert_eq!(x, Ok(Value::Str(Str::from("Buzz"))));

    process_def(
        r#"def to-fizz-buzz Num () {
    let {if-div 3 'Fizz'} $f {if-div 5 'Buzz'} $b
    | \'' | + $f $b
}"#,
        defs,
    );

    let x = process(
        r#"range 1 21 | map i { let {to-str} $n | to-fizz-buzz | if {empty} $n #i }"#,
        defs,
    );

    check_is_table(x, _2_2_fizzbuzz_exp());
}

// #### 4.0 Command Commands ###################################################

#[test]
fn _4_0_common_cmds_01() {
    let defs = &Definitions::new();

    let x = process("Tuple 1 2 | get t0", defs);
    assert_eq!(x, Ok(Value::Num(1u8.into())));
    let x = process("Tuple 1 2 | get t1", defs);
    assert_eq!(x, Ok(Value::Num(2u8.into())));

    let x = process("open tests/diamonds.csv | last get color", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(x, "Semantics Error: ambiguous inference. more than one output type can compile op
--> shell:31
 | open tests/diamonds.csv | last get color
 |                                ^^^ this op can be compiled with `Nil` and `TableRow` as output types
--> shell:31
 | open tests/diamonds.csv | last get color
 |                                ^^^ try annotating output type: `get:<type> ...`
");

    let x = process("open tests/diamonds.csv | last get:Str color", defs);
    assert_eq!(x, Ok(Value::Str(Str::from("D"))));
}

#[test]
fn _4_0_common_cmds_02() {
    let x = process(
        r#"open tests/diamonds.csv | grp cut | append
--'Max Price' {get value | fold 0 max $row.price}
--'Total Carats' {get value | fold 0 + $row.carat}
| filter --cols != value"#,
        &Definitions::new(),
    );

    let exp = vec![
        vec![s("key"), s("Max Price"), s("Total Carats")],
        vec![s("Fair"), n(18574), n(1684.2800000000038)],
        vec![s("Good"), n(18788), n(4166.100000000046)],
        vec![s("Ideal"), n(18806), n(15146.83999999912)],
        vec![s("Premium"), n(18823), n(12300.949999999846)],
        vec![s("Very Good"), n(18818), n(9742.700000000264)],
    ];

    check_is_table(x, exp);
}
