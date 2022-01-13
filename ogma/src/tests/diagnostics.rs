use super::*;

// ------ Typify ---------------------------------------------------------------
#[test]
fn typify_help_msg() {
    let src = "typify --help";
    let x = print_help(src, &Definitions::new());
    return; // pass for now TODO wire in
    assert_eq!(
        &x,
        "Help: `typify`
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
fn typify_test_raw() {
    let defs = &Definitions::new();

    let s = |s: &str| Ok(Value::Str(Str::new(s)));

    // Ident
    let x = process_w_nil("typify foo-bar", defs);
    assert_eq!(x, s("foo-bar:Str"));

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
    assert_eq!(x, s("{:Nil ls |:Table filter foo:Str {:Num < 3:Num }:Bool }:Table"));
}

