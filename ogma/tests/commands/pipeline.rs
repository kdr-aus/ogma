use super::*;

// ------ Dot Operator ---------------------------------------------------------
#[test]
fn dotop_help_msg() {
    let src = ". --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `.`
--> shell:0
 | ---- Input Type: <any> ----
 | extract a value out of a structure using an infix operator
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
 | 
 |  explicitly constrain output type of a column
 |  => $table-row.col-name:Str
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
        "Semantics Error: expecting argument with output type `Number`, found `String`
--> shell:27
 | fold 0 + $row.Testing-weird\\string
 |                            ^^^^^^^ this argument returns type `String`
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
--> help: `Bar` has the following fields: x, y
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
--> help: `Foo` has the following fields: x, bar
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
--> help: `Bar` has the following fields: x, y
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
--> help: `Bar` has the following fields: x, y
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
--> help: `Foo` has the following fields: x, bar
"#
    );
}

#[test]
fn dotop_infers_output() {
    let defs = &Definitions::new();

    let x = process_w_table("fold 0 + $row.first", defs);
    assert_eq!(x, Ok(Value::Num((-29.0).into())));

    let x = process_w_table("fold 'foo' + $row.'Heading 3'", defs);
    assert_eq!(x, Ok(Value::Str("fooabz".into())));

    let x = process_w_table("fold 1 + $row.'Heading 3'", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Evaluation Error: table entry for [row:1,col:'Heading 3'] did not have expected type
expected `Number`, found `String`
--> shell:15
 | fold 1 + $row.'Heading 3'
 |                ^^^^^^^^^
--> help: column entries must have a matching type
"
    );

    let x = process_w_table("fold 'foo' + $row.first", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Evaluation Error: table entry for [row:1,col:'first'] did not have expected type
expected `String`, found `Number`
--> shell:18
 | fold 'foo' + $row.first
 |                   ^^^^^
--> help: column entries must have a matching type
"
    );
}

// ------ Get ------------------------------------------------------------------
#[test]
fn get_help_msg() {
    let src = "get --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        r#"Help: `get`
--> shell:0
 | ---- Input Type: <any> ----
 | extract a value out of a data structure
 | 
 | Usage:
 |  => get field
 | 
 | Examples:
 |  get the x field of a user defined Point type
 |  => Point 1 3 | get x
 | 
 | ---- Input Type: TableRow ----
 | extract a value out of a column in a table row.
 | optionally specify a default value if the get type does not match
 | 
 | Usage:
 |  => get field [default]
 | 
 | Examples:
 |  get the entry of a table row under the column 'size'
 |  => ls | filter { get size | > 100 }
 | 
 |  get all files in the directory, requiring 'type' to return a string
 |  => ls | filter { get:Str type | = 'file' }
 | 
 |  sum the size of files, using a default of zero
 |  => ls | fold 0 { + {\$row | get size 0} }
"#
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
--> help: view a list of types using `def-ty --list`
"#
    );

    let x = process_w_table("fold 0 { \\$row | get snd --Str --foo | \\ 3 }", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        r#"Semantics Error: not expecting flags: `foo`
--> shell:33
 | fold 0 { \$row | get snd --Str --foo | \ 3 }
 |                                  ^^^ flag not supported
--> help: try using the `--help` flag to view requirements
"#
    );

    let x = process_w_table(
        "fold 0 { + $row.first {\\$row | get 'Heading 3' 100} }",
        defs,
    );
    assert_eq!(x, Ok(Value::Num((0 + 1 - 30 + 100 + 100 + 100).into())));
}

#[test]
fn get_test_with_default_as_another_get() {
    let defs = &Definitions::new();
    let x = process_w_table("fold 0 { \\ $row | get snd { get first } }", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        r#"Semantics Error: `get` does not support `Nil` input data
--> shell:28
 | fold 0 { \ $row | get snd { get first } }
 |                             ^^^
--> help: use `get --help` to view requirements. consider implementing `def get`
"#
    );

    let x = process_w_table("fold 0 { \\ $row | get snd $row.first:Num }", defs);
    assert_eq!(x, Ok(Value::Num(100.into())));
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
 | ---- Input Type: <any> ----
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

    let x = process_w_table("append { \\ #i.snd:Num | + 1 }", d);
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

// ------ Last -----------------------------------------------------------------
#[test]
fn last_help_msg() {
    let src = "last --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        r#"Help: `last`
--> shell:0
 | ---- Input Type: String ----
 | user defined implementation in <ogma>
 | `def last Str () { nth {len | - 1} }`
 | get the last character of a string
 | 
 | Usage:
 |  => last
 | 
 | Examples:
 |  get the last character
 |  => \ 'Hello' | last
 | 
 | ---- Input Type: Table ----
 | user defined implementation in <ogma>
 | `def last Table (expr:Expr) { nth {len | - 1} $expr }`
 | apply the expression to the last row in a table
 | 
 | Usage:
 |  => last expr:Expr
 | 
 | Examples:
 |  fetch the last value in a column 'foo'
 |  => last {get:Str 'foo'}
"#
    );
}

#[test]
fn last_testing() {
    let defs = &Definitions::new();

    // table
    let x = process_w_table("last {get first --Num}", defs);
    assert_eq!(x, Ok(Value::Num((-30).into())));
    let x = process_w_table("last {get snd --Num}", defs);
    assert_eq!(x, Ok(Value::Num(100.into())));

    // string
    let x = process_w_str("last", defs);
    assert_eq!(x, Ok(Value::Str("o".into())));
}

#[test]
fn last_testing_bug_116() {
    let defs = &Definitions::new();

    let x = process_w_nil(
        r#"ls | grp name | fold 0 { \$row | get value | last get:Num size }"#,
        defs,
    );
    assert!(matches!(x, Ok(Value::Num(_))));
}

// ------ Length ---------------------------------------------------------------
#[test]
fn len_help_msg() {
    let src = "len --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        r#"Help: `len`
--> shell:0
 | ---- Input Type: String ----
 | return the number of characters in a string
 | 
 | Usage:
 |  => len
 | 
 | Examples:
 |  length of a string
 |  => \ 'Hello, 🌎!' | len
 | 
 | ---- Input Type: Table ----
 | return the number of rows or columns in a table.
 | length **does not include header row**
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
"#
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
 | ---- Input Type: <any> ----
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
        "let {+ 1} $x {- 1} $y {= 3} $z | \\ $x | / $y | = 2 | and $z",
        defs,
    );
    assert_eq!(x, Ok(Value::Bool(true)));

    let x = process_w_num("let {+ 1} $x {- 1} $y $z | \\ $x | * $y $z", defs);
    assert_eq!(x, Ok(Value::Num((4 * 2 * 3).into())));

    let x = process_w_table(
        "filter { let {get first --Num} $x {get snd --Num} $y | \\ $x | < $y }",
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
    let x = process_w_table("filter { let $x | \\$x.snd:Num | > 10 }", defs);
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
        r#"Semantics Error: expecting argument with output type `Number`, found `Table`
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
    println!("{}", x);
    assert_eq!(
        &x,
        r#"Semantics Error: variable `x` does not exist
--> shell:9
 | \ 5 | > $x
 |          ^ `x` not in scope
--> help: variables must be in scope
          variables can be defined using the `let` command
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
--> help: variables must be in scope
          variables can be defined using the `let` command
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
--> help: variables must be in scope
          variables can be defined using the `let` command
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
--> help: variables must be in scope
          variables can be defined using the `let` command
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
--> help: variables must be in scope
          variables can be defined using the `let` command
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

#[test]
fn variable_shadowing_soundness_01() {
    let defs = &Definitions::new();
    let code = "ls | let $x | + { let 'hdr' $x | Table $x }";
    let x = process_w_nil(code, defs);

    if let Err(e) = &x {
        println!("{e}");
    }

    assert!(matches!(x, Ok(Value::Tab(_))));

    let code = r#"ls | let $x | map size {:Num let $row.type:Str $x | Table $x }"#;
    let x = process_w_nil(code, defs);

    if let Err(e) = &x {
        println!("{e}");
    }

    assert!(matches!(x, Ok(Value::Tab(_))));
}

#[test]
fn variable_shadowing_soundness_02() {
    let defs = &Definitions::new();
    let code = r#"ls | let $x | grp type | map value {:Table \ $x | let $row.key:Str $x | fold {Table $x} append-row $row.size:Num  }"#;
    let x = process_w_nil(code, defs);

    if let Err(e) = &x {
        println!("{e}");
    }

    assert!(matches!(x, Ok(Value::Tab(_))));
}

// ------ Nth ------------------------------------------------------------------
#[test]
fn nth_help_msg() {
    let src = "nth --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        r#"Help: `nth`
--> shell:0
 | ---- Input Type: String ----
 | retrieves the nth character of a string
 | 
 | Usage:
 |  => nth index
 | 
 | Examples:
 |  get the 10th character of a string
 |  => \ 'Hello, world!' | nth 10
 | 
 | ---- Input Type: Table ----
 | retrieves the nth row and applies the expression
 | 
 | Usage:
 |  => nth index expr
 | 
 | Examples:
 |  get the first row of a table
 |  => nth 0 {get col-name}
 | 
 |  get the 2nd last row of a table
 |  => nth {len | - 2} {get col-name}
"#
    );
}

#[test]
fn nth_testing() {
    let defs = &Definitions::new();

    // table
    let x = process_w_table("nth 0 {get first --Num}", defs);
    assert_eq!(x, Ok(Value::Num(0.into())));
    let x = process_w_table("nth 2 {get first --Num}", defs);
    assert_eq!(x, Ok(Value::Num((-30).into())));
    let x = process_w_table("nth {\\ 1 | + 2} {get:Num first}", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        r#"Evaluation Error: index is outside table bounds
--> shell:4
 | nth {\ 1 | + 2} {get:Num first}
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

// ------ Rand -----------------------------------------------------------------
#[test]
fn rand_help_msg() {
    let src = "rand --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `rand`
--> shell:0
 | ---- Input Type: <any> ----
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
 | ---- Input Type: <any> ----
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

// ------ To-str ---------------------------------------------------------------
#[test]
fn to_str_help_msg() {
    let src = "to-str --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        r#"Help: `to-str`
--> shell:0
 | ---- Input Type: <any> ----
 | convert the input into a string
 | 
 | Usage:
 |  => to-str
 | 
 | ---- Input Type: Bool ----
 | return a boolean as 'true' or 'false'
 | 
 | Usage:
 |  => to-str
 | 
 | ---- Input Type: Number ----
 | format the number as a string
 | 
 | Usage:
 |  => to-str [fmt]
 | 
 | Examples:
 |  format a number as a percentage
 |  => \ 0.4123 | to-str '[.2%]'
 | 
 | ---- Input Type: String ----
 | pass through the string value
 | 
 | Usage:
 |  => to-str
"#
    );
}

#[test]
fn to_str_testing() {
    let defs = &Definitions::new();

    let x = process_w_num("to-str", defs);
    assert_eq!(x, Ok(Value::Str("3".into())));

    let x = process_w_nil("\\ 1.234e6 | to-str", defs);
    assert_eq!(x, Ok(Value::Str("1234000".into())));

    let x = process_w_nil("\\ 'hello, World!' | to-str", defs);
    assert_eq!(x, Ok(Value::Str("hello, World!".into())));

    let x = process_w_nil("\\ #t | to-str", defs);
    assert_eq!(x, Ok(Value::Str("true".into())));

    // with formatter
    let x = process_w_nil("\\ 1.234e6 | to-str ''", defs);
    assert_eq!(x, Ok(Value::Str("1.234 M".into())));

    let x = process_w_nil("\\ 1.234e6 | to-str 'yo [.0n] da'", defs);
    assert_eq!(x, Ok(Value::Str("yo 1,234,000 da".into())));

    let x = process_w_nil("\\ 1.234e6 | to-str '[.0n da'", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(&x, "Parsing Error: invalid format string: unexpected character. expected a ., ~, %, s, m, b, n, /, ] but found ' '
--> shell:20
 | \\ 1.234e6 | to-str '[.0n da'
 |                     ^^^^^^^ invalid format string
--> help: Number formatting syntax can be found at
          <https://daedalus.report/d/docs/ogma.book/05%20syntax%20and%20semantics/5.4%20number%20formatting.md?pwd-raw=docs>
");
}
