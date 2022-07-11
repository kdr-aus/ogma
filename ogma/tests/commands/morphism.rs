use super::*;

// ------ Append ---------------------------------------------------------------
#[test]
fn append_help_msg() {
    let src = "append --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `append`
--> shell:0
 | ---- Input Type: Table ----
 | add new columns onto a table using one or more expressions
 | each expression adds a new column, populated by row with the result of the expression
 | tags can be optionally specified to name the columns
 | 
 | Usage:
 |  => append args..
 | 
 | Flags:
 |  --<col-names>: name each column in order of expression
 | 
 | Examples:
 |  flag if a filesystem item is a file
 |  => ls | append { get type --Str | eq file } --is-file
 | 
 |  add more than one column
 |  => ls | append { get size | if { > 1e9 } 'big file' '' } { get ext --Str | eq csv }
"
    );
}

#[test]
fn append_testing() {
    let defs = &Definitions::new();

    let x = process_w_table("append { let {get first --Num} $f | get snd | + $f }", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3"), o("_append1")],
        vec![n(0), n(3), o("a"), n(3)],
        vec![n(1), n(20), o("b"), n(21)],
        vec![n(-30), n(100), o("z"), n(70)],
    ];
    check_is_table(x, exp);
    let x = process_w_table(
        "let $x | append { let { get --Num first } $f | get snd | + $f } --foo { get 'Heading 3' --Str }",
        defs,
    );
    let exp = vec![
        vec![
            o("first"),
            o("snd"),
            o("Heading 3"),
            o("foo"),
            o("_append1"),
        ],
        vec![n(0), n(3), o("a"), n(3), o("a")],
        vec![n(1), n(20), o("b"), n(21), o("b")],
        vec![n(-30), n(100), o("z"), n(70), o("z")],
    ];
    check_is_table(x, exp);
}

#[test]
fn empty_append_err() {
    let defs = &Definitions::new();
    let x = process_w_table("append", defs).unwrap_err().to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Semantics Error: expecting more than 0 arguments
--> shell:0
 | append
 | ^^^^^^ expecting additional argument(s)
--> help: try using the `--help` flag to view requirements
"
    );
}

#[test]
fn append_encounter_wrong_ty() {
    let defs = &Definitions::new();
    let x = process_w_table("append { get first --Str | + 'foo' }", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert!(x.contains("expected `String`, found `Number`")); // parallel so exact error might chg
}

// ------ Append-Row -----------------------------------------------------------
#[test]
fn append_row_help_msg() {
    let src = "append-row --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `append-row`
--> shell:0
 | ---- Input Type: Table ----
 | append a row to the table
 | the row is populated with the expression results
 | -variadic-: more than one argument can be specified
 | 
 | Usage:
 |  => append-row args..
 | 
 | Examples:
 |  append the row 1 2 3 to the table
 |  => append-row 1 2 3
"
    );
}

#[test]
fn append_row_testing() {
    let defs = &Definitions::new();

    let x = process_w_table("append-row", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
        vec![Nil, Nil, Nil],
    ];
    check_is_table(x, exp);

    let x = process_w_table("append-row 1 2", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
        vec![n(1), n(2), Nil],
    ];
    check_is_table(x, exp);

    let x = process_w_table("append-row 1 2 3 4", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3"), o("_append1")],
        vec![n(0), n(3), o("a"), Nil],
        vec![n(1), n(20), o("b"), Nil],
        vec![n(-30), n(100), o("z"), Nil],
        vec![n(1), n(2), n(3), n(4)],
    ];
    check_is_table(x, exp);
}

// ------ Dedup ----------------------------------------------------------------
#[test]
fn dedup_help_msg() {
    let src = "dedup --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        r#"Help: `dedup`
--> shell:0
 | ---- Input Type: String ----
 | de-duplicate consecutive characters from a string
 | 
 | Usage:
 |  => dedup
 | 
 | Examples:
 |  reduce the string 'aabbcc' to 'abc'
 |  => \ 'aabbcc' | dedup
 | 
 | ---- Input Type: Table ----
 | de-duplicate consecutive repeated rows.
 | rows are removed if the cells in the specified columns match.
 | if no columns are specified the whole row must match.
 | if the table is sorted, this removes all duplicates.
 | 
 | Usage:
 |  => dedup col-name..
 | 
 | Examples:
 |  remove all duplicate entries in the 'Product' heading
 |  => sort Product | dedup Product
 | 
 |  remove duplicates that match the entire row
 |  => ls foo | + ls bar | sort name | dedup
"#
    );
}

#[test]
fn dedup_table_testing() {
    let defs = &Definitions::new();

    // check that dedup uses all columns
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    let x = process_w_table("+ #i | sort snd | dedup", defs);
    check_is_table(x, exp.clone());

    // check that dedup doesn't work if not sorted!
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    let x = process_w_table("+ #i | dedup", defs);
    check_is_table(x, exp.clone());

    // check on dedup just single columns
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(-30), n(100), o("z")],
        vec![n(-30), n(101), o("z")],
        vec![n(0), n(3), o("a")],
        vec![n(0), n(4), o("a")],
        vec![n(1), n(20), o("b")],
        vec![n(1), n(21), o("b")],
    ];
    let x = process_w_table("+ {\\#i | map snd + 1} | sort first | dedup", defs);
    check_is_table(x, exp.clone());
    let x = process_w_table(
        "+ {\\#i | map snd + 1} | sort first | dedup first snd",
        defs,
    );
    check_is_table(x, exp.clone());
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(-30), n(100), o("z")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
    ];
    let x = process_w_table("+ {\\#i | map snd + 1} | sort first | dedup first", defs);
    check_is_table(x, exp.clone());
}

#[test]
fn dedup_str_testing() {
    let defs = &Definitions::new();

    let x = process_w_str("dedup", defs);
    assert_eq!(x, Ok(Value::Str("Helo".into())));

    let x = process_w_str("\\\'foo barr zoog\' | dedup", defs);
    assert_eq!(x, Ok(Value::Str("fo bar zog".into())));
}

// ------ Filtering ------------------------------------------------------------
#[test]
fn filtering_help_msg() {
    let src = "filter --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        r#"Help: `filter`
--> shell:0
 | ---- Input Type: String ----
 | filter a string based on if a character matches a predicate
 | 
 | Usage:
 |  => filter <predicate>
 | 
 | Examples:
 |  filtering a string
 |  => \ 'Hello, world!' | filter != ' '
 | 
 | ---- Input Type: Table ----
 | filter table using a predicate
 | filter can be used with a column header and a type flag
 | filtering columns is achievable with the --cols flag
 | 
 | Usage:
 |  => filter [col-name] <predicate>
 | 
 | Flags:
 |  --<type>: only filter entries of type. defaults to Num if not specified
 |  --cols: filter columns with predicate. predicate is String -> Bool
 | 
 | Examples:
 |  filter ls items greater than 5kB
 |  => ls | filter size > 5e3
 | 
 |  filter ls by extension
 |  => ls | filter ext --Str = md
 | 
 |  filter a table by two columns
 |  => \ table.csv | filter { and { get col-a | > 100 } { get col-b | < 10 } }
 | 
 |  filter table columns
 |  => \ table.csv | filter --cols or { = 'foo' } { = bar }
"#
    );
}

#[test]
fn row_filtering() {
    let defs = &Definitions::new();
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    let x = process_w_table("filter { get snd | > 10 }", defs);
    check_is_table(x, exp.clone());
    let x = process_w_table("filter snd > 10", defs);
    check_is_table(x, exp.clone());
    let x = process_w_table("filter snd { > 10 }", defs);
    check_is_table(x, exp.clone());
}

#[test]
fn row_filtering2() {
    let defs = &Definitions::new();
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    let x = process_w_table("filter { get 'Heading 3' --Str | > a }", defs);
    check_is_table(x, exp.clone());
    let x = process_w_table("filter 'Heading 3' --Str > a", defs);
    check_is_table(x, exp.clone());
    let x = process_w_table("filter 'Heading 3' --Num > 10", defs);
    check_is_table(x, vec![vec![o("first"), o("snd"), o("Heading 3")]]);
}

#[test]
fn row_filtering_by_building_new_table() {
    let defs = &Definitions::new();
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    // The let binding should force the table to be shared
    let x = process_w_table("let $x | filter { get 'Heading 3' --Str | > a }", defs);
    check_is_table(x, exp.clone());
}

#[test]
fn column_not_table() {
    let defs = &Definitions::new();
    let x = process_w_table("filter { get not-here | > 10 }", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Evaluation Error: header `not-here` not found in table
--> shell:13
 | filter { get not-here | > 10 }
 |              ^^^^^^^^ `not-here` resolves to `not-here`
"
    );

    let x = process_w_table("filter not-here > 10", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Evaluation Error: header `not-here` not found in table
--> shell:7
 | filter not-here > 10
 |        ^^^^^^^^ `not-here` resolves to `not-here`
"
    );
}

#[test]
fn row_filtering_using_def() {
    let defs = &with_dummy_defs();
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    let x = process_w_table("filter gt10", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Semantics Error: expecting more than 0 arguments
--> shell:7
 | filter gt10
 |        ^^^^ expecting additional argument(s)
--> help: try using the `--help` flag to view requirements.
          `gt10` is defined to accept parameters `(n)`
"
    );
    let x = process_w_table("filter gt10 snd", defs);
    check_is_table(x, exp.clone());
}

#[test]
fn column_filtering() {
    let defs = &Definitions::new();

    let x = process_w_table("filter --cols = first", defs);
    let exp = vec![vec![o("first")], vec![n(0)], vec![n(1)], vec![n(-30)]];
    check_is_table(x, exp.clone());

    let x = process_w_table("filter --cols or { = 'Heading 3' } { = first }", defs);
    let exp = vec![
        vec![o("first"), o("Heading 3")],
        vec![n(0), o("a")],
        vec![n(1), o("b")],
        vec![n(-30), o("z")],
    ];
    check_is_table(x, exp.clone());
}

#[test]
fn string_filtering() {
    let defs = &Definitions::new();

    let x = process_w_str("filter = l", defs);
    assert_eq!(x, Ok(Value::Str("ll".into())));
    let x = process_w_str("filter != l", defs);
    assert_eq!(x, Ok(Value::Str("Heo".into())));
    let x = process_w_str("filter #f", defs);
    assert_eq!(x, Ok(Value::Str("".into())));
    let x = process_w_str("filter #t", defs);
    assert_eq!(x, Ok(Value::Str("Hello".into())));
    let x = process_w_str("filter or {= H} {= o}", defs);
    assert_eq!(x, Ok(Value::Str("Ho".into())));
}

// ------ Folding --------------------------------------------------------------
#[test]
fn fold_help_msg() {
    let src = "fold --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `fold`
--> shell:0
 | ---- Input Type: Table ----
 | fold (reduce) table into single value
 | fold takes a seed value and an accumulator expression
 | the variable $row is available to query the table row
 | 
 | Usage:
 |  => fold seed accumulator
 | 
 | Examples:
 |  sum numbers (0,10)
 |  => range 0 11 | fold 0 { + $row.i }
 | 
 |  count number of files in directory
 |  => ls | filter { get type --Str | = file } | fold 0 + 1
"
    );
}

#[test]
fn fold_test() {
    let defs = &Definitions::new();
    let x = process_w_num("range 0 10 | fold 0 { + { \\$row | get i } }", defs);
    assert_eq!(x, Ok(Value::Num(45.into())));
    let x = process_w_num("range 0 10 | fold 0 + $row.i", defs);
    assert_eq!(x, Ok(Value::Num(45.into())));
    let x = process_w_num("range 0 0 | fold -100 + $row.i", defs);
    assert_eq!(x, Ok(Value::Num((-100).into())));
}

#[test]
fn fold_while_help_msg() {
    let src = "fold-while --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `fold-while`
--> shell:0
 | ---- Input Type: Table ----
 | fold (reduce) table into single value while a predicate remains true
 | fold-while is similar to fold with an added predicate check on each iteration
 | the input into the predicate is the current accumulator value
 | fold-while will stop iterating once the predicate returns false
 | 
 | Usage:
 |  => fold-while seed predicate accumulator
 | 
 | Examples:
 |  sum natural numbers until sum is greater than one million
 |  => range 1 1e6 | fold-while 0 {<= 1e6} { + $row.i }
"
    );
}

#[test]
fn fold_while_test() {
    let defs = &Definitions::new();
    let x = process_w_num("range 0 10 | fold-while 0 {>= 0} { + $row.i }", defs);
    assert_eq!(x, Ok(Value::Num(45.into())));
    let x = process_w_num("range 0 10 | fold-while 0 {< 30} + $row.i", defs);
    assert_eq!(x, Ok(Value::Num(36.into())));
    let x = process_w_num("range 1 20 | fold-while 1 {< 1e6} * $row.i", defs);
    assert_eq!(x, Ok(Value::Num((3628800).into())));
    let x = process_w_num("range 1 20 | fold-while {Tuple 0 0} {get t0 | < 20} { let {get t0} $t0 | get t1 | + $t0 | Tuple #i $row.i:Num } | get t0", defs);
    assert_eq!(x, Ok(Value::Num((21).into())));
}

// ------ Grp ------------------------------------------------------------------
#[test]
fn grp_help_msg() {
    let src = "grp --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `grp`
--> shell:0
 | ---- Input Type: Table ----
 | group a table by column headers
 | each value under the header is stringified and
 | concatenated together separated by a hyphen
 | to group on a derived value see `grp-by`
 | 
 | Usage:
 |  => grp col-name..
 | 
 | Examples:
 |  group by file extension
 |  => ls | grp ext
 | 
 |  group by file extension and modified
 |  => ls | grp ext modified
"
    );
}

#[test]
fn grp_testing() {
    let defs = &Definitions::new();

    let x = process_w_table(
        "grp 'Heading 3' | 
fold {range 0 0} {let $acc | \\$row | get value --Table | pick first | let $x | \\$acc | + $x}",
        defs,
    );
    let exp = vec![vec![o("i")], vec![n(0)], vec![n(1)], vec![n(-30)]];
    check_is_table(x, exp);
    let x = process_w_table(
        "append --'foo' {get first | >= 0} |
grp foo | map value --Table len",
        defs,
    );
    let exp = vec![
        vec![o("key"), o("value")],
        vec![o("false"), n(1)],
        vec![o("true"), n(2)],
    ];
    check_is_table(x, exp);
    let x = process_w_table(
        "append --'foo' {get first | >= 0} |
grp foo 'Heading 3' | map value --Table len",
        defs,
    );
    let exp = vec![
        vec![o("key"), o("value")],
        vec![o("false-z"), n(1)],
        vec![o("true-a"), n(1)],
        vec![o("true-b"), n(1)],
    ];
    check_is_table(x, exp);
}

// ------ Grp-by ---------------------------------------------------------------
#[test]
fn grpby_help_msg() {
    let src = "grp-by --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `grp-by`
--> shell:0
 | ---- Input Type: Table ----
 | group table using an expression
 | the result of the expression must define a `cmp` implementation
 | this can be used to group user-defined types
 | 
 | Usage:
 |  => grp-by <expr>
 | 
 | Examples:
 |  group ls by file extension
 |  => ls | grp-by { get --Str ext }
 | 
 |  group using a user-defined type
 |  => ls | grp-by { Point { get size } }
"
    );
}

#[test]
fn grpby_testing() {
    let defs = &Definitions::new();

    let x = process_w_table(
        "grp-by {get --Str 'Heading 3'} | 
fold {range 0 0} { let $acc | \\$row | get value --Table | pick first | let $x | \\$acc | + $x}",
        defs,
    );
    let exp = vec![vec![o("i")], vec![n(0)], vec![n(1)], vec![n(-30)]];
    check_is_table(x, exp);
    let x = process_w_table("grp-by {get first | >= 0} | map value --Table len", defs);
    let exp = vec![
        vec![o("key"), o("value")],
        vec![Entry::from(Value::Bool(false)), n(1)],
        vec![Entry::from(Value::Bool(true)), n(2)],
    ];
    check_is_table(x, exp);
}

// ------ Map ------------------------------------------------------------------
#[test]
fn map_help_msg() {
    let src = "map --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `map`
--> shell:0
 | ---- Input Type: Table ----
 | replace entry in column with result of an expression
 | `map` provides the variable `$row` which is the TableRow
 | the input into the expression is the value of the entry
 | 
 | Usage:
 |  => map col-name value
 | 
 | Flags:
 |  --<type>: the type that entry has
 |  --force: ignore entry types
 | 
 | Examples:
 |  scale 'size' by dividing by one million
 |  => ls | map size / 1e6
 | 
 |  use a different column and result type
 |  => ls | map type --Str { \\$row.size | + 100 }
"
    );
}

#[test]
fn map_testing() {
    let defs = &Definitions::new();
    let x = process_w_table("map first + 1", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(1), n(3), o("a")],
        vec![n(2), n(20), o("b")],
        vec![n(-29), n(100), o("z")],
    ];
    check_is_table(x, exp);
    let x = process_w_table("map 'Heading 3' --Str { \\$row.first:Num | + 1 }", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), n(1)],
        vec![n(1), n(20), n(2)],
        vec![n(-30), n(100), n(-29)],
    ];
    check_is_table(x, exp);

    // check we can use variables/exprs in column heading
    let x = process_w_table(
        "map { \\ 'Heading 3' } --Str { \\$row.first:Num | + 1 }",
        defs,
    );
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), n(1)],
        vec![n(1), n(20), n(2)],
        vec![n(-30), n(100), n(-29)],
    ];
    check_is_table(x, exp);
    let x = process_w_table(
        "let {\\ 'Heading 3'} $x | map $x --Str { \\$row.first:Num | + 1 }",
        defs,
    );
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), n(1)],
        vec![n(1), n(20), n(2)],
        vec![n(-30), n(100), n(-29)],
    ];
    check_is_table(x, exp);

    // check parallelsiation doesn't wreak havoc
    let x = process_w_nil(
        "range 1 100 | map i --Num { \\$row | let {get i --Num} $i | get i | + $i }",
        defs,
    );
    let mut exp = vec![vec![o("i")]];
    exp.extend((1..100).map(|i| vec![n(i * 2)]).collect::<Vec<_>>());
    check_is_table(x, exp);

    // check ignore flag
    let x = process_w_table("map 'Heading 3' --force $row.first:Num", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), n(0)],
        vec![n(1), n(20), n(1)],
        vec![n(-30), n(100), n(-30)],
    ];
    check_is_table(x, exp);
}

// ------ Pick -----------------------------------------------------------------
#[test]
fn pick_help_msg() {
    let src = "pick --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `pick`
--> shell:0
 | ---- Input Type: Table ----
 | pick out columns to keep in a table, in order
 | 
 | Usage:
 |  => pick col-name..
 | 
 | Flags:
 |  --add: add a blank column if it does not exist in the table
 |  --trail: append any remaining columns in order
 | 
 | Examples:
 |  choose the size, name, and type columns
 |  => ls | pick name size type
"
    );
}

#[test]
fn pick_testing() {
    let defs = &Definitions::new();

    let x = process_w_table("pick first snd 'Heading 3'", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    check_is_table(x, exp);

    let x = process_w_table("pick snd first 'Heading 3'", defs);
    let exp = vec![
        vec![o("snd"), o("first"), o("Heading 3")],
        vec![n(3), n(0), o("a")],
        vec![n(20), n(1), o("b")],
        vec![n(100), n(-30), o("z")],
    ];
    check_is_table(x, exp);

    let x = process_w_table("pick 'Heading 3' snd snd", defs);
    let exp = vec![
        vec![o("Heading 3"), o("snd"), o("snd")],
        vec![o("a"), n(3), n(3)],
        vec![o("b"), n(20), n(20)],
        vec![o("z"), n(100), n(100)],
    ];
    check_is_table(x, exp);
}

#[test]
fn pick_add_testing() {
    let defs = &Definitions::new();

    let x = process_w_table("pick --add a first b", defs);
    let exp = vec![
        vec![o("a"), o("first"), o("b")],
        vec![Nil, n(0), Nil],
        vec![Nil, n(1), Nil],
        vec![Nil, n(-30), Nil],
    ];
    check_is_table(x, exp);
}

#[test]
fn pick_trail_testing() {
    let defs = &Definitions::new();

    let x = process_w_table("pick --trail snd", defs);
    let exp = vec![
        vec![o("snd"), o("first"), o("Heading 3")],
        vec![n(3), n(0), o("a")],
        vec![n(20), n(1), o("b")],
        vec![n(100), n(-30), o("z")],
    ];
    check_is_table(x, exp);

    let x = process_w_table("pick --add --trail snd snd a b", defs);
    let exp = vec![
        vec![
            o("snd"),
            o("snd"),
            o("a"),
            o("b"),
            o("first"),
            o("Heading 3"),
        ],
        vec![n(3), n(3), Nil, Nil, n(0), o("a")],
        vec![n(20), n(20), Nil, Nil, n(1), o("b")],
        vec![n(100), n(100), Nil, Nil, n(-30), o("z")],
    ];
    check_is_table(x, exp);
}

#[test]
fn pick_err_testing() {
    let defs = &Definitions::new();

    let x = process_w_table("pick first snd third", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Evaluation Error: header `third` not found in table
--> shell:15
 | pick first snd third
 |                ^^^^^ `third` resolves to `third`
"
    );
}

// ------ Ren ------------------------------------------------------------------
#[test]
fn ren_help_msg() {
    let src = "ren --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `ren`
--> shell:0
 | ---- Input Type: Table ----
 | rename column headers
 | each binding takes the form `<col-ref> <name>`
 | `<col-ref>` can be a string or a column index number
 | 
 | Usage:
 |  => ren [<col-ref-1> <name-1>] [<col-ref-2> <name-2>] ...
 | 
 | Examples:
 |  rename foo to bar and bar to foo
 |  => ren foo bar bar foo
 | 
 |  rename idx 0 to foo
 |  => ren 0 foo
"
    );
}

#[test]
fn ren_testing() {
    let defs = &Definitions::new();

    let x = process_w_table("ren first hello", defs);
    let exp = vec![
        vec![o("hello"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    check_is_table(x, exp);

    let x = process_w_table("ren first hello snd hello2", defs);
    let exp = vec![
        vec![o("hello"), o("hello2"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    check_is_table(x, exp);

    let x = process_w_table("ren 0 hello snd hello2", defs);
    let exp = vec![
        vec![o("hello"), o("hello2"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    check_is_table(x, exp);
}

#[test]
fn ren_err_testing() {
    let defs = &Definitions::new();

    let x = process_w_table("ren frist hello", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Evaluation Error: header `frist` not found in table
--> shell:4
 | ren frist hello
 |     ^^^^^ `frist` resolves to `frist`
"
    );

    let x = process_w_table("ren first", defs).unwrap_err().to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Semantics Error: too many arguments supplied
--> shell:4
 | ren first
 |     ^^^^^ this argument is unnecessary
"
    );
}

// ------ Ren-With -------------------------------------------------------------
#[test]
fn ren_with_help_msg() {
    let src = "ren-with --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `ren-with`
--> shell:0
 | ---- Input Type: Table ----
 | rename column headers using a row as a seed
 | each entry is fed into the expression, which returns a string
 | the default entry type required is a string
 | 
 | Usage:
 |  => ren-with row-idx name-expr
 | 
 | Flags:
 |  --<type>: the type of the entry
 | 
 | Examples:
 |  rename the header with what is in row 2
 |  => ren-with 2 #i
 | 
 |  append the headers with something
 |  => ren-with 0 + ' bar'
 | 
 |  use the first row as a header and forget the old one
 |  => ren-with 1 #i | skip 1
"
    );
}

#[test]
fn ren_with_testing() {
    let defs = &Definitions::new();

    let x = process_w_table(
        "map --Num first to-str | map --Num snd to-str | ren-with --Str 1 { \\ #i }",
        defs,
    );
    let exp = vec![
        vec![o("0"), o("3"), o("a")],
        vec![o("0"), o("3"), o("a")],
        vec![o("1"), o("20"), o("b")],
        vec![o("-30"), o("100"), o("z")],
    ];
    check_is_table(x, exp);

    // test the derived impl skip-hdrs
    let x = process_w_table(
        "map --Num first to-str | map --Num snd to-str | skip-hdrs 2",
        defs,
    );
    let exp = vec![
        vec![o("1"), o("20"), o("b")],
        vec![o("-30"), o("100"), o("z")],
    ];
    check_is_table(x, exp);
}

#[test]
fn ren_with_err_testing() {
    let defs = &Definitions::new();

    let x = process_w_table("ren-with --Str 1 hello", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Evaluation Error: table entry for [row:1,col:'0'] did not have expected type
expected `String`, found `Number`
--> shell:15
 | ren-with --Str 1 hello
 |                ^
--> help: column entries must have a matching type
"
    );

    let x = process_w_table("ren-with --Str 100 foo", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Evaluation Error: row index `100` is outside table bounds
--> shell:15
 | ren-with --Str 100 foo
 |                ^^^ `100` resolves to 100
--> help: use `len` command to check the size of the table
"
    );

    let x = process_w_table("\\Table | ren-with --Str 100 foo", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Evaluation Error: empty table
--> shell:9
 | \\Table | ren-with --Str 100 foo
 |          ^^^^^^^^^^^^^^^^^^^^^^
"
    );
}

// ------ Rev ------------------------------------------------------------------
#[test]
fn rev_help_msg() {
    let src = "rev --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        r#"Help: `rev`
--> shell:0
 | ---- Input Type: String ----
 | reverse the order of characters
 | 
 | Usage:
 |  => rev
 | 
 | Examples:
 |  reverse string character ordering
 |  => \ '!dlrow ,olleH' | rev
 | 
 | ---- Input Type: Table ----
 | reverse the order of table rows or columns
 | 
 | Usage:
 |  => rev
 | 
 | Flags:
 |  --cols: reverse table column ordering
 | 
 | Examples:
 |  reverse table row ordering
 |  => ls | rev
"#
    );
}

#[test]
fn rev_testing() {
    let defs = &Definitions::new();

    let x = process_w_table("rev", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(-30), n(100), o("z")],
        vec![n(1), n(20), o("b")],
        vec![n(0), n(3), o("a")],
    ];
    check_is_table(x, exp);

    let x = process_w_table("rev --cols", defs);
    let exp = vec![
        vec![o("Heading 3"), o("snd"), o("first")],
        vec![o("a"), n(3), n(0)],
        vec![o("b"), n(20), n(1)],
        vec![o("z"), n(100), n(-30)],
    ];
    check_is_table(x, exp);

    let x = process_w_table("sort 'Heading 3' | rev", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(-30), n(100), o("z")],
        vec![n(1), n(20), o("b")],
        vec![n(0), n(3), o("a")],
    ];
    check_is_table(x, exp);

    let x = process_w_str("rev", defs);
    assert_eq!(x, Ok(Value::Str(Str::from("olleH"))));
}

// ------ Skip -----------------------------------------------------------------
#[test]
fn skip_help_msg() {
    let src = "skip --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `skip`
--> shell:0
 | ---- Input Type: <any> ----
 | skip the first n elements of a data structure
 | 
 | Usage:
 |  => skip count
 | 
 | Examples:
 |  skip the first 10 rows of a table
 |  => skip 10
 | 
 |  skip the first 5 characters of a string
 |  => \\ 'Hello, world!' | skip 5
 | 
 |  skip and take can be used to slice into a string
 |  => \\ 'Hello, world!' | skip 7 | take 5
"
    );
}

#[test]
fn skip_testing() {
    let defs = &Definitions::new();

    // table
    let x = process_w_table("skip 0", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    check_is_table(x, exp);

    let x = process_w_table("skip 2", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(-30), n(100), o("z")],
    ];
    check_is_table(x, exp);
    let x = process_w_table("let $n | skip 2", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(-30), n(100), o("z")],
    ];
    check_is_table(x, exp);

    let x = process_w_table("skip 5", defs);
    let exp = vec![vec![o("first"), o("snd"), o("Heading 3")]];
    check_is_table(x, exp);

    // string
    let x = process_w_str("skip 0", defs);
    assert_eq!(x, Ok(Value::Str("Hello".into())));
    let x = process_w_str("skip 2", defs);
    assert_eq!(x, Ok(Value::Str("llo".into())));
    let x = process_w_str("skip 5", defs);
    assert_eq!(x, Ok(Value::Str("".into())));
}

// ------ Sort -----------------------------------------------------------------
#[test]
fn sort_help_msg() {
    let src = "sort --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `sort`
--> shell:0
 | ---- Input Type: <any> ----
 | sort a table by column headers
 | each header sorts the rows lowest to highest in a canonical fashion,
 | in order specified (1st column is sorted first)
 | this sorts different value types, but NOT user-defined types. see `sort-by`
 | 
 | Usage:
 |  => sort col-name..
 | 
 | Examples:
 |  sort ls by file size
 |  => ls | sort size
 | 
 |  sort ls by ext, THEN by size (notice the inverted order)
 |  => ls | sort size ext
"
    );
}

#[test]
fn sort_testing() {
    let defs = &Definitions::new();

    let x = process_w_table("sort first", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(-30), n(100), o("z")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
    ];
    check_is_table(x, exp);
    let x = process_w_table("sort first 'Heading 3'", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    check_is_table(x, exp);
}

#[test]
fn empty_sort_err() {
    let defs = &Definitions::new();
    let x = process_w_table("sort", defs).unwrap_err().to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Semantics Error: expecting more than 0 arguments
--> shell:0
 | sort
 | ^^^^ expecting additional argument(s)
--> help: try using the `--help` flag to view requirements
"
    );
}

// ------ Sort-by --------------------------------------------------------------
#[test]
fn sortby_help_msg() {
    let src = "sort-by --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `sort-by`
--> shell:0
 | ---- Input Type: <any> ----
 | sort table using an expression
 | the result of the expression must define a `cmp` implementation
 | this can be used to sort user-defined types
 | 
 | Usage:
 |  => sort-by <expr>
 | 
 | Examples:
 |  sort ls by file size
 |  => ls | sort-by { get size }
 | 
 |  sort using a user-defined type
 |  => ls | sort-by { Point { get size } }
"
    );
}

#[test]
fn sortby_testing() {
    let defs = &Definitions::new();

    let x = process_w_table("sort-by { get first --Num }", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(-30), n(100), o("z")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
    ];
    check_is_table(x, exp);

    let x = process_w_table("sort-by { get first | if { < 0 } { * -1 } { + 0 } }", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    check_is_table(x, exp);

    let x = process_w_table("sort-by { get snd --Num | * -1 }", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(-30), n(100), o("z")],
        vec![n(1), n(20), o("b")],
        vec![n(0), n(3), o("a")],
    ];
    check_is_table(x, exp);

    let x = process_w_table("let $x | sort-by { get snd --Num | * -1 }", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(-30), n(100), o("z")],
        vec![n(1), n(20), o("b")],
        vec![n(0), n(3), o("a")],
    ];
    check_is_table(x, exp);
}

#[test]
fn sortby_errors() {
    let defs = &mut Definitions::new();

    process_definition("def-ty Point { x:Num y:Num }", Location::Shell, None, defs).unwrap();

    let x = process_w_table("sort-by Point 1 0", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Semantics Error: `cmp` does not support `Point` input data
--> <ogma>:0
 | cmp $rhs
 | ^^^
--> shell:0
 | sort-by Point 1 0
 | ^^^^^^^ sort-by requires expression output to implement `cmp` with a single argument
--> shell:8
 | sort-by Point 1 0
 |         ^^^^^^^^^ expression returns `Point`
--> help: use `cmp --help` to view requirements. consider implementing `def cmp`
"
    );

    process_definition(
        "def cmp Point (rhs x) { \\ $x }",
        Location::Shell,
        None,
        defs,
    )
    .unwrap();

    let x = process_w_table("sort-by Point 1 0", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Semantics Error: expecting more than 1 arguments
--> <ogma>:0
 | cmp $rhs
 | ^^^^^^^^ expecting additional argument(s)
--> shell:0
 | sort-by Point 1 0
 | ^^^^^^^ sort-by requires expression output to implement `cmp` with a single argument
--> shell:8
 | sort-by Point 1 0
 |         ^^^^^^^^^ expression returns `Point`
--> help: try using the `--help` flag to view requirements.
          `cmp` is defined to accept parameters `(rhs x)`
"
    );

    process_definition(
        "def cmp Point (rhs) { \\ $rhs }",
        Location::Shell,
        None,
        defs,
    )
    .unwrap();

    let x = process_w_table("sort-by Point 1 0", defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    assert_eq!(
        &x,
        "Semantics Error: `Point`'s `cmp` impl returns `Point`, expecting `Ord`
--> shell:0
 | sort-by Point 1 0
 | ^^^^^^^ sort-by requires expression output to implement `cmp` with a single argument
--> shell:8
 | sort-by Point 1 0
 |         ^^^^^^^^^ expression returns `Point`
"
    );
}

// ------ Take -----------------------------------------------------------------
#[test]
fn take_help_msg() {
    let src = "take --help";
    let x = print_help(src, &Definitions::new());
    assert_eq!(
        &x,
        "Help: `take`
--> shell:0
 | ---- Input Type: <any> ----
 | take the first n elements of a data structure
 | 
 | Usage:
 |  => take count
 | 
 | Examples:
 |  take the first 10 rows of a table
 |  => take 10
 | 
 |  take the first 5 characters of a string
 |  => \\ 'Hello, world!' | take 5
 | 
 |  skip and take can be used to slice into a string
 |  => \\ 'Hello, world!' | skip 7 | take 5
"
    );
}

#[test]
fn take_testing() {
    let defs = &Definitions::new();

    // table
    let x = process_w_table("take 0", defs);
    let exp = vec![vec![o("first"), o("snd"), o("Heading 3")]];
    check_is_table(x, exp);

    let x = process_w_table("take 2", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
    ];
    check_is_table(x, exp);
    let x = process_w_table("let $n | take 2", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
    ];
    check_is_table(x, exp);

    let x = process_w_table("take 5", defs);
    let exp = vec![
        vec![o("first"), o("snd"), o("Heading 3")],
        vec![n(0), n(3), o("a")],
        vec![n(1), n(20), o("b")],
        vec![n(-30), n(100), o("z")],
    ];
    check_is_table(x, exp);

    // string
    let x = process_w_str("take 0", defs);
    assert_eq!(x, Ok(Value::Str("".into())));
    let x = process_w_str("take 2", defs);
    assert_eq!(x, Ok(Value::Str("He".into())));
    let x = process_w_str("take 5", defs);
    assert_eq!(x, Ok(Value::Str("Hello".into())));
}
