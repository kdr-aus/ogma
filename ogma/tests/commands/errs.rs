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
