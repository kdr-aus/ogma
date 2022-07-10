use super::*;

// ------ Abs ------------------------------------------------------------------
#[test]
fn abs_help_msg() {
    let src = "abs --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `abs`
--> shell:0
 | ---- Input Type: Number ----
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
        r#"Help: `+`
--> shell:0
 | ---- Input Type: Number ----
 | add numbers together
 | -variadic-: more than one argument can be specified
 | 
 | Usage:
 |  => + args..
 | 
 | Examples:
 |  add 2 to 1
 |  => \ 1 | + 2
 | 
 |  add multiple numbers together
 |  => + 1 2 3 4 5
 | 
 | ---- Input Type: String ----
 | concatenate strings together
 | -variadic-: more than one argument can be specified
 | 
 | Usage:
 |  => + args..
 | 
 | Examples:
 |  join together strings
 |  => \ Hello | + ', world!'
 | 
 |  join strings with a new line
 |  => \ 'First Line' | + #b 'Second Line'
 | 
 | ---- Input Type: Table ----
 | concatenate rows of table
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
 |  add two tables together, concatenating rows
 |  => range 0 10 | + range 10 20
 | 
 |  index filesystem items, shrink table to min rows
 |  => range 0 1000 | + --cols --intersect ls
"#
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
        "Semantics Error: not expecting flags: `intersect`
--> shell:11
 | + --cols --intersect --union { range 1 5 | append { get i | + 1 } }
 |            ^^^^^^^^^ flag not supported
--> help: try using the `--help` flag to view requirements
"
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
 | ---- Input Type: <any> ----
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
 | ---- Input Type: <any> ----
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

// ------ Div ------------------------------------------------------------------
#[test]
fn div_help_msg() {
    let src = "/ --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `/`
--> shell:0
 | ---- Input Type: <any> ----
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
    let x = process_w_num("/ 6", defs);
    assert_eq!(x, Ok(Value::Num((0.5).into())));
    let x = process_w_num("let $x | \\ 30 | ÷ -5 $x", defs);
    assert_eq!(x, Ok(Value::Num((-2).into()))); // 30 / -5 / 3 = -2
    let x = process_w_num("/ 0", defs);
    assert_eq!(x, Ok(Value::Num(std::f64::INFINITY.into())));
    let x = process_w_num("/ 0 3", defs);
    assert_eq!(x, Ok(Value::Num(std::f64::INFINITY.into())));
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
 | ---- Input Type: <any> ----
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

// ------ Mod ------------------------------------------------------------------
#[test]
fn mod_help_msg() {
    let src = "mod --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `mod`
--> shell:0
 | ---- Input Type: Number ----
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
 | ---- Input Type: Number ----
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

// ------ Root -----------------------------------------------------------------
#[test]
fn root_help_msg() {
    let src = "root --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `root`
--> shell:0
 | ---- Input Type: <any> ----
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

// ------ Sub ------------------------------------------------------------------
#[test]
fn sub_help_msg() {
    let src = "- --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `-`
--> shell:0
 | ---- Input Type: <any> ----
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
    let x = process_w_nil("\\ -2 | - -1", defs);
    assert_eq!(x, Ok(Value::Num((-1).into())));
    let x = process_w_num("let $x | \\ 1 | - 1 2 $x", defs);
    assert_eq!(x, Ok(Value::Num((-5).into()))); // 1 - 1 - 2 - 3
}
