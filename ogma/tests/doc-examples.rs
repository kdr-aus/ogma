use libs::divvy::Str;
use ogma::lang::{Definitions, Value};
use std::path::Path;
use table::Entry::{self, Nil};

type Result<T> = std::result::Result<T, ogma::Error>;

fn paths() -> (&'static Path, &'static Path) {
    (Path::new("."), Path::new("../ogma"))
}

fn process(src: &str, defs: &Definitions) -> Result<Value> {
    let (root, wd) = paths();
    ogma::rt::process_expression((), src, ogma::lang::ast::Location::Shell, defs, root, wd)
}

fn check_is_table(r: Result<Value>, table: Vec<Vec<Entry<Value>>>) {
    match r {
        Ok(Value::Tab(tab)) => {
            assert_eq!(tab, ogma::lang::Table::from(::table::Table::from(table)));
        }
        Err(e) => {
            println!("{}", e);
            panic!("returned err: {:?}", e)
        }
        x => panic!("not a table: {:?}", x),
    }
}

fn n<N: Into<::kserd::Number>>(n: N) -> Entry<Value> {
    Entry::Num(n.into())
}
fn s(s: &str) -> Entry<Value> {
    Entry::Obj(Value::Str(Str::new(s)))
}

// #### 2.2 FizzBuzz ###########################################################

#[test]
fn _2_2_fizzbuzz_01() {
    let x = process(
        r#"range 1 101 | map i { let $e |
    if { \$e | mod 3 | = 0 } 'Fizz' '' |
    + if { \$e | mod 5 | = 0 } 'Buzz' '' |
    if {empty} { \$e | to-str } #i
} 
"#,
        &Definitions::new(),
    );

    let exp = vec![vec![s("i")]];

    check_is_table(x, exp);
}
