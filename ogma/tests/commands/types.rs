use super::*;

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

