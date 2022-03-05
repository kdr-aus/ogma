use super::*;

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
        "Semantics Error: expecting argument with output type `Number`, found `String`
--> <ogma>:18
 | def = (rhs) { eq $rhs }
 |                   ^^^ this argument returns type `String`
--> shell:5
 | if { = 'foo' } 0 1
 |      ^^^^^^ invoked here
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
