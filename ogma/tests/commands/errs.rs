use super::*;

#[test]
fn err_wrong_return_type() {
    let def = &Definitions::new();
    let x = process_w_table("filter { \\ 5 }", def)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        r#"Typing Error: Type resolution failed. Conflicting obligation type
--> shell:9
 | filter { \ 5 }
 |          ^ this node returns a `Number`
--> shell:7
 | filter { \ 5 }
 |        ^^^^^^^ but this node is obliged to return `Bool`
"#
    );
}

#[test]
fn suggest_pipe_if_trailing_cmd() {
    let x = process_w_nil("\\ 3 | let $n to-str", &Definitions::new())
        .unwrap_err()
        .to_string();
    println!("{x}");
    assert_eq!(
        &x,
        "Semantics Error: variable `n` does not exist
--> shell:11
 | \\ 3 | let $n to-str
 |            ^ `n` not in scope
--> help: variables must be in scope
          variables can be defined using the `let` command
    help: maybe you forgot a pipe: `let $n | to-str`?
"
    );
}

#[test]
fn suggest_typing_with_dot_operator() {
    let x = process_w_nil("ls | append #i.name", &Definitions::new())
        .unwrap_err()
        .to_string();
    println!("{x}");
    assert_eq!(
        &x,
        r#"Semantics Error: ambiguous inference. more than one output type can compile op
--> shell:14
 | ls | append #i.name
 |               ^ this op can be compiled with output types: Nil TableRow Number Table Bool Ord String
--> shell:12
 | ls | append #i.name
 |             ^^^^^^^ try annotating output type: `#i.name:<type>`
"#
    );
}

#[test]
fn better_parsing_error_message_bug_139() {
    let code = r#"def sim-characteristics Table (col:Str) {
    let {len} $len
    | let { fold 0 + { \ $row | get $col} | / $len } $avg
    | append --sq-diff { get $col | - $avg | * #i }
    | fold 0 + $row.sq-diff | / { \ $len | - 1} } | root 2
    | let { * -0.84162 | + $avg } $p20 { * 0.84162 | + $avg } $p80 $stdev_s
    | Table P20 P50 P80 'σ_s'
    | append-row $p20 $avg $p80 $stdev_s
}"#;

// Notice the extra brace at
// | fold 0 + $row.sq-diff | / { \ $len | - 1} } | root 2
//                                             ^

let x = process_definition(code, Location::Shell, None, &mut Definitions::new())
        .unwrap_err()
        .to_string();
    println!("{x}");
    assert_eq!(

        &x,
        r#""#,
    );
}
