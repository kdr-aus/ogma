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
        vec![s("1")],
        vec![s("2")],
        vec![s("Fizz")],
        vec![s("4")],
        vec![s("Buzz")],
        vec![s("Fizz")],
        vec![s("7")],
        vec![s("8")],
        vec![s("Fizz")],
        vec![s("Buzz")],
        vec![s("11")],
        vec![s("Fizz")],
        vec![s("13")],
        vec![s("14")],
        vec![s("FizzBuzz")],
        vec![s("16")],
        vec![s("17")],
        vec![s("Fizz")],
        vec![s("19")],
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

#[test]
fn _4_0_common_cmds_03() {
    let x = process(
        r#"open tests/diamonds.csv | fold 0 + $row.price"#,
        &Definitions::new(),
    );
    assert_eq!(x, Ok(Value::Num(212135217.into())));
}

#[test]
fn _4_0_common_cmds_04() {
    let x = process(
        r#"open tests/diamonds.csv | fold -inf max $row.carat"#,
        &Definitions::new(),
    );
    assert_eq!(x, Ok(Value::Num(5.01f64.into())));
}

// #### 6.0 Command Commands ###################################################

#[test]
fn _6_0_variables_01() {
    let defs = &Definitions::new();

    let a = process(
        r#"open tests/diamonds.csv | append --'Price per Carat' {
let {get:Num price} $price {get:Num carat} $ct | \$price | / $ct }"#,
        defs,
    )
    .unwrap();

    let b = process(
        r#"open tests/diamonds.csv | append --'Price per Carat' / #i.price #i.carat"#,
        defs,
    )
    .unwrap();

    assert_eq!(a, b);
}

// #### 11 (No) Recursion ######################################################

#[test]
fn _11_0_no_recursion_01() {
    let defs = &mut Definitions::new();

    process_def(
        r#"def pwr (n x) { if { \$x | = 0 } 1 { range 1 $x | fold $n * $n } }"#,
        defs,
    );

    let x = process("pwr 2 3", defs);
    assert_eq!(x, Ok(Value::Num(8u8.into())));
    let x = process("pwr 2 2", defs);
    assert_eq!(x, Ok(Value::Num(4u8.into())));
    let x = process("pwr 2 1", defs);
    assert_eq!(x, Ok(Value::Num(2u8.into())));
    let x = process("pwr 2 0", defs);
    assert_eq!(x, Ok(Value::Num(1u8.into())));
}

#[test]
fn _11_0_no_recursion_02() {
    let defs = &mut Definitions::new();

    process_def(
        r#"def fact Num () { if {<= 1} 1 { + 1 | range 1 | fold 1 * $row.i } }"#,
        defs,
    );

    let x = process("range 1 11 | append --'i!' { get i | fact }", defs);

    let fact = |n: u8| (1..=n).map(|x| x as f64).fold(1f64, std::ops::Mul::mul);

    let exp = vec![
        vec![s("i"), s("i!")],
        vec![n(1u8), n(fact(1))],
        vec![n(2u8), n(fact(2))],
        vec![n(3u8), n(fact(3))],
        vec![n(4u8), n(fact(4))],
        vec![n(5u8), n(fact(5))],
        vec![n(6u8), n(fact(6))],
        vec![n(7u8), n(fact(7))],
        vec![n(8u8), n(fact(8))],
        vec![n(9u8), n(fact(9))],
        vec![n(10u8), n(fact(10))],
    ];

    check_is_table(x, exp);
}

#[test]
fn _11_0_no_recursion_03() {
    let defs = &mut Definitions::new();

    process_def(
        r#"def gcd (a b) { range 0 {\$a|abs|min {\$b|abs}} |
    fold-while { if {\$a|< $b} {Tuple $b $a} {Tuple $a $b} }
        { get t1 | != 0 }
        { let $acc | get t0 | mod $acc.t1 | Tuple $acc.t1 #i }
    | get t0
}"#,
        defs,
    );

    let x = process("gcd 10 4", defs);
    assert_eq!(x, Ok(Value::Num(2u8.into())));
    let x = process("gcd 100 80", defs);
    assert_eq!(x, Ok(Value::Num(20u8.into())));
    let x = process("gcd 255 25", defs);
    assert_eq!(x, Ok(Value::Num(5u8.into())));
}
