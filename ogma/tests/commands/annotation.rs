use super::*;

#[test]
fn success_01() {
    let defs = &Definitions::new();
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    let x = process_w_table(
        "filter:Table {:TableRow get:Num snd |:Num >:Bool 10 }:Bool",
        defs,
    );
    check_is_table(x, exp.clone());
    let x = process_w_table("filter snd >:Bool 10", defs);
    check_is_table(x, exp.clone());
    let x = process_w_table("filter snd {:Num > 10 }", defs);
    check_is_table(x, exp.clone());
}

#[test]
fn success_02() {
    let defs = &Definitions::new();

    let s = |s: &str| Ok(Value::Str(Str::new(s)));

    let x = process_w_table(
        "typify --verbose { filter { get bar |:Str =:Bool 'foo' } }",
        defs,
    );
    assert_eq!(
        x,
        s("{:Table filter:Table {:TableRow get:Str bar:Str |:Str =:Bool foo:Str }:Bool }:Table")
    );

    let x = process_w_num(
        "typify --verbose { + 3 |:Num max 2 | to-str |:Str len }",
        defs,
    );
    assert_eq!(
        x,
        s("{:Num +:Num 3:Num |:Num max:Num 2:Num |:Num to-str:Str |:Str len:Num }:Num")
    );
}

#[test]
fn success_03() {
    let defs = &Definitions::new();

    let x = process_w_table(
        "append --foo Tuple {get snd}:Num {get:Num snd} | fold 0 + $row.snd",
        defs,
    );
    assert_eq!(x, Ok(Value::Num(123.into())));

    // TODO: once . operator uses type inference, this should be turned back on.
    //     let x = process_w_table(
    //         "nth 1 Tuple {get:Num snd} #i.'Heading 3':Str | get t1",
    //         defs,
    //     );
    //     assert_eq!(x, Ok(Value::Str(Str::new(""))));
}

#[test]
fn errors_01() {
    let defs = &Definitions::new();

    // can't constrain input into root
    let x = process_w_table(":Nil filter bar = 'foo'", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Typing Error: Type application failed
--> shell:5
 | :Nil filter bar = 'foo'
 |      ^^^^^^ this node has input type `Nil`
--> shell:5
 | :Nil filter bar = 'foo'
 |      ^^^^^^ but it is inferred to use only types: Table String
"
    );

    // can't constrain literal output
    let x = process_w_table("filter bar:Str = 'foo'", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Parsing Error: could not parse input line
--> shell:10
 | filter bar:Str = 'foo'
 |           ^^^^ unexpected type identifier
"
    );

    // can't constrain variable output
    let x = process_w_table("let $x | \\ $x:Table", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Parsing Error: could not parse input line
--> shell:13
 | let $x | \\ $x:Table
 |              ^^^^^^ unexpected type identifier
"
    );

    // can't constrain pound
    let x = process_w_table("\\ #t:Table", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Parsing Error: could not parse input line
--> shell:4
 | \\ #t:Table
 |     ^^^^^^ unexpected type identifier
"
    );
}

#[test]
fn errors_02() {
    let defs = &Definitions::new();

    // filter returns a Table
    let x = process_w_table("filter:Str { get bar }", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Typing Error: Type application failed
--> shell:0
 | filter:Str { get bar }
 | ^^^^^^ this node is trying to have a type `Table` applied to it
--> shell:0
 | filter:Str { get bar }
 | ^^^^^^ but it is already obligated to use type `String`
--> help: maybe remove any type annotations
"
    );

    // add returns a number
    let x = process_w_num("+:Str 3", defs).unwrap_err().to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Typing Error: Type application failed
--> shell:0
 | +:Str 3
 | ^ this node is trying to have a type `Number` applied to it
--> shell:0
 | +:Str 3
 | ^ but it is already obligated to use type `String`
--> help: maybe remove any type annotations
"
    );

    // conflicting input
    let x = process_w_table("filter { get:Num snd |:Str + bar | = foo }", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Typing Error: Type resolution failed. Conflicting obligation type
--> shell:9
 | filter { get:Num snd |:Str + bar | = foo }
 |          ^^^ this node returns a `Number`
--> shell:27
 | filter { get:Num snd |:Str + bar | = foo }
 |                            ^ but this node is obliged to return `String`
"
    );

    // runtime error, expecting num
    let x = process_w_table("nth 1 Tuple #i.snd:Str #i.snd:Num", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Evaluation Error: table entry for [row:2,col:'snd'] did not have expected type
expected `String`, found `Number`
--> shell:15
 | nth 1 Tuple #i.snd:Str #i.snd:Num
 |                ^^^
--> help: column entries must have a matching type
"
    );
}
