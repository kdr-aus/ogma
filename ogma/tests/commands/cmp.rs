use super::*;

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
