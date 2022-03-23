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
        "filter:Bool {:TableRow get:Num snd |:Num >:Bool 10 }:Bool",
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

    let x = process_w_table("append --foo Tuple {get snd}:Num | fold 0 + $row.snd", defs);
    assert_eq!(x, Ok(Value::Num(0.into())));

    let x = process_w_table(
        "nth 1 Tuple {get:Num snd} #i.'Heading 3':Str | get t1",
        defs,
    );
    assert_eq!(x, Ok(Value::Str(Str::new(""))));
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
        "Typing Error: Type resolution failed. Conflicting obligation type
--> shell:0
 | :Nil filter bar = 'foo'
 | ^^^^^^^^^^^^^^^^^^^^^^^ this node has input type `Table`
--> shell:5
 | :Nil filter bar = 'foo'
 |      ^^^^^^ but this node is obliged to use input `Nil`
"
    );

    // can't constrain literal output
    let x = process_w_table("filter bar:Str = 'foo'", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(&x, "");

    // can't constrain variable output
    let x = process_w_table("let $x | \\ $x:Table", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(&x, "");

    // can't constrain pound
    let x = process_w_table("\\ #t:Table", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(&x, "");
}

#[test]
fn errors_02() {
    let defs = &Definitions::new();

    // filter returns a Table
    let x = process_w_table("filter:Str { get bar }", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(&x, "");

    // add returns a number
    let x = process_w_num("+:Str 3", defs).unwrap_err().to_string();
    println!("{}", x);
    assert_eq!(&x, "");

    // conflicting input
    let x = process_w_table("filter { get:Num snd |:Str + bar | = foo }", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(&x, "");

    // runtime error, expecting num
    let x = process_w_table("nth 1 Tuple #i.snd:Str", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(&x, "");
}
