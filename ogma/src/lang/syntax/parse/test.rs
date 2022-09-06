use super::*;
use nom::Err as E;
use Argument::*;
use Expecting as Ex;
use Term::*;

fn tag_eq(tag: &Tag, s: &str) -> bool {
    tag.str() == s
}

fn line(s: &str) -> Line {
    Line {
        loc: Location::Shell,
        line: Arc::from(s),
    }
}

fn tt(s: &str) -> Tag {
    Tag_ {
        anchor: Location::Shell,
        line: Arc::from(s),
        start: 0,
        end: s.len(),
    }
    .into()
}

fn ops(s: &str) -> Op {
    Op::Single(tt(s))
}

#[test]
fn input_expr() {
    let d = &Definitions::new();
    let x = expression("in", Location::Shell, d);
    assert_eq!(
        x,
        Ok(Expression {
            tag: tt("in"),
            blocks: vec![PrefixBlock {
                op: ops("in"),
                terms: vec![],
                in_ty: None,
                out_ty: None
            }
            .into()],
            out_ty: None
        })
    );

    let x = expression("in file.csv", Location::Shell, d);
    assert_eq!(
        x,
        Ok(Expression {
            tag: tt("in file.csv"),
            blocks: vec![PrefixBlock {
                op: ops("in"),
                terms: vec![Arg(Ident(tt("file.csv")))],
                in_ty: None,
                out_ty: None
            }
            .into()],
            out_ty: None
        })
    );
}

#[test]
fn empty_expr() {
    let d = &Definitions::new();
    let x = expression("", Location::Shell, d)
        .unwrap_err()
        .0
        .to_string();
    println!("{x}");
    assert_eq!(
        &x,
        "Parsing Error: could not parse input line
--> shell:0
--> shell:0
"
    );

    let x = line(" { asdf {  }  } ");
    let x = expr(&x, d)(&x.line);
    assert_eq!(
        x,
        Err(E::Error(ParsingError {
            locs: vec![
                (
                    "{".into(),
                    "invalid identifier, expecting alphabetic character, found `{`".into()
                ),
                (" { asdf {  }  } ".into(), "no command".into())
            ],
            expecting: Ex::Impl,
        }))
    );

    let l = line("{  }");
    let x = term(&l, d)(&l.line);
    assert_eq!(
        x,
        Err(ParsingError::failure("{  }", "empty block", Ex::Impl))
    );
}

#[test]
fn after_pipe_error() {
    let d = &Definitions::new();

    let src = "\\ | ";
    let x = expression(src, Location::Shell, d)
        .unwrap_err()
        .0
        .to_string();
    println!("{x}");
    assert_eq!(
        &x,
        r#"Parsing Error: could not parse input line
--> shell:4
 | \ | 
 |     ^ empty identifier
--> shell:3
 | \ | 
 |    ^ no command
"#
    );

    let src = "\\ { \\ | }";
    let x = expression(src, Location::Shell, d)
        .unwrap_err()
        .0
        .to_string();
    println!("{x}");
    assert_eq!(
        &x,
        r#"Parsing Error: could not parse input line
--> shell:8
 | \ { \ | }
 |         ^ invalid identifier, expecting alphabetic character, found `}`
--> shell:7
 | \ { \ | }
 |        ^^ no command
--> shell:0
 | \ { \ | }
 | ^^^^^^^^^ no command
"#
    );
}

#[test]
fn op_ident_test() {
    let x = line("valid second");
    let x = op_ident(&x)(&x.line);
    assert_eq!(x, Ok((" second", tt("valid"))));
    let x = line("0-invalid second");
    let x = op_ident(&x)(&x.line);
    assert_eq!(
        x,
        Err(ParsingError::err(
            "0",
            "invalid identifier, expecting alphabetic character, found `0`",
            Ex::None,
        ))
    );
}

#[test]
fn broken_expr_delimiter() {
    let d = &Definitions::new();
    let src = "\\ { cmd ident ";
    let x = expression(src, Location::Shell, d)
        .unwrap_err()
        .0
        .to_string();
    println!("{x}");
    assert_eq!(
        &x,
        r#"Parsing Error: could not parse input line
--> shell:14
 | \ { cmd ident 
 |               ^ expected `}`
--> shell:0
 | \ { cmd ident 
 | ^^^^^^^^^^^^^^ no command
"#
    );

    let src = "\\ { cmd { ident }";
    let x = expression(src, Location::Shell, d)
        .unwrap_err()
        .0
        .to_string();
    println!("{x}");
    assert_eq!(
        &x,
        r#"Parsing Error: could not parse input line
--> shell:17
 | \ { cmd { ident }
 |                  ^ expected `}`
--> shell:0
 | \ { cmd { ident }
 | ^^^^^^^^^^^^^^^^^ no command
"#
    );

    let src = "\\ f | asdf { cmd { ident } ";
    let x = expression(src, Location::Shell, d)
        .unwrap_err()
        .0
        .to_string();
    println!("{x}");
    assert_eq!(
        &x,
        r#"Parsing Error: could not parse input line
--> shell:27
 | \ f | asdf { cmd { ident } 
 |                            ^ expected `}`
--> shell:5
 | \ f | asdf { cmd { ident } 
 |      ^^^^^^^^^^^^^^^^^^^^^^ no command
"#
    );

    let src = "\\ file.csv | asdf { cmd {   } ";
    let x = expression(src, Location::Shell, d)
        .unwrap_err()
        .0
        .to_string();
    println!("{x}");
    assert_eq!(
        &x,
        r#"Parsing Error: could not parse input line
--> shell:24
 | \ file.csv | asdf { cmd {   } 
 |                         ^^^^^ empty block
--> shell:20
 | \ file.csv | asdf { cmd {   } 
 |                     ^^^^^^^^^^ no command
--> shell:12
 | \ file.csv | asdf { cmd {   } 
 |             ^^^^^^^^^^^^^^^^^^ no command
"#
    );

    let src = "\\ adsf | cmd { \\ |";
    let x = expression(src, Location::Shell, d)
        .unwrap_err()
        .0
        .to_string();
    println!("{x}");
    assert_eq!(
        &x,
        r#"Parsing Error: could not parse input line
--> shell:18
 | \ adsf | cmd { \ |
 |                   ^ empty identifier
--> shell:18
 | \ adsf | cmd { \ |
 |                   ^ no command
--> shell:8
 | \ adsf | cmd { \ |
 |         ^^^^^^^^^^ no command
"#
    );
}

#[test]
fn arguments() {
    let src = line("{ \\ asdf } remaining");
    let x = term(&src, &Definitions::new())(&src.line);
    assert_eq!(
        x,
        Ok((
            " remaining",
            Arg(Expr(Expression {
                tag: tt("{ \\ asdf }"),
                blocks: vec![PrefixBlock {
                    op: ops("\\"),
                    terms: vec![Arg(Ident(tt("asdf")))],
                    in_ty: None,
                    out_ty: None
                }
                .into()],
                out_ty: None
            }))
        ))
    );
}

#[test]
fn pipelining() {
    let src = "\\ test.csv | cmd { \\ asdf }";
    let x = expression(src, Location::Shell, &Definitions::new());
    assert_eq!(
        x,
        Ok(Expression {
            tag: tt("\\ test.csv | cmd { \\ asdf }"),
            blocks: vec![
                PrefixBlock {
                    op: ops("\\"),
                    terms: vec![Arg(Ident(tt("test.csv")))],
                    in_ty: None,
                    out_ty: None
                }
                .into(),
                PrefixBlock {
                    op: ops("cmd"),
                    terms: vec![Arg(Expr(Expression {
                        tag: tt("{ \\ asdf }"),
                        blocks: vec![PrefixBlock {
                            op: ops("\\"),
                            terms: vec![Arg(Ident(tt("asdf")))],
                            in_ty: None,
                            out_ty: None
                        }
                        .into()],
                        out_ty: None
                    }))],
                    in_ty: None,
                    out_ty: None
                }
                .into()
            ],
            out_ty: None
        })
    );
}

#[test]
fn variable_parsing() {
    let l = line("$in");
    assert_eq!(var(&l)(&l.line), Ok(("", tt("in"))));
    let l = line("in");
    assert!(var(&l)(&l.line).is_err());
}

#[test]
fn variable_term() {
    let l = line("$in");
    assert_eq!(
        term(&l, &Definitions::new())(&l.line),
        Ok(("", Arg(Var(tt("in")))))
    );
}

#[test]
fn identifiers() {
    let i = |s| {
        let line = line(s);
        let x = ident(&line)(&line.line).unwrap().1;
        x
    };

    assert_eq!(i("hello"), tt("hello"));
    assert_eq!(i("hello world"), tt("hello"));
    assert_eq!(i("'hello world'"), tt("hello world"));
    assert_eq!(i(r#""hello world""#), tt("hello world"));
    assert_eq!(i(r#"'hello "world"'"#), tt("hello \"world\""));
    assert_eq!(i(r#""hello 'world'""#), tt(r#"hello 'world'"#));
    let x = line("'hello world");
    let x = ident(&x)(&x.line);
    assert_eq!(
        x,
        Err(ParsingError::err("", "expected `\'`", Expecting::None,))
    );
}

#[test]
fn numbers() {
    let l = line("3.14 else");
    let (nan, inf) = (std::f64::NAN, std::f64::INFINITY);
    assert_eq!(
        num(&l)(&l.line),
        Ok((" else", (Number::from(3.14), tt("3.14"))))
    );
    let l = line("-1e6");
    assert_eq!(
        num(&l)(&l.line),
        Ok(("", (Number::from(-1_000_000), tt("-1e6"))))
    );
    let l = line("inf else");
    assert_eq!(
        num(&l)(&l.line),
        Ok((" else", (Number::from(inf), tt("inf"))))
    );
    let l = line("-inf else");
    assert_eq!(
        num(&l)(&l.line),
        Ok((" else", (Number::from(-inf), tt("-inf"))))
    );
    let l = line("∞ else");
    assert_eq!(
        num(&l)(&l.line),
        Ok((" else", (Number::from(inf), tt("∞"))))
    );
    let l = line("-∞ else");
    assert_eq!(
        num(&l)(&l.line),
        Ok((" else", (Number::from(-inf), tt("-∞"))))
    );
    let l = line("nan else");
    assert_eq!(
        num(&l)(&l.line),
        Ok((" else", (Number::from(nan), tt("nan"))))
    );
}

#[test]
fn flags() {
    let defs = &Definitions::new();
    let i = |s| {
        let line = line(s);
        let x = term(&line, defs)(&line.line).unwrap().1;
        x
    };

    assert_eq!(i("--hello"), Term::Flag(tt("hello")));
    assert_eq!(i("--'i!'"), Term::Flag(tt("i!")));
    assert_eq!(i("--\"foo bar'\""), Term::Flag(tt("foo bar'")));
}

#[test]
fn term_parsing_which_is_cmd() {
    let d = &Definitions::new();
    let l = line("filter adsf cdx | ls");
    let x = term(&l, d)(&l.line);
    assert_eq!(
        x,
        Ok((
            "| ls",
            Arg(Expr(Expression {
                tag: tt("filter adsf cdx "),
                blocks: vec![PrefixBlock {
                    op: ops("filter"),
                    terms: vec![Arg(Ident(tt("adsf"))), Arg(Ident(tt("cdx")))],
                    in_ty: None,
                    out_ty: None
                }
                .into()],
                out_ty: None
            }))
        ))
    );

    let l = line("filter > col-name 1");
    let x = term(&l, d)(&l.line);
    assert_eq!(
        x,
        Ok((
            "",
            Arg(Expr(Expression {
                tag: tt("filter > col-name 1"),
                blocks: vec![PrefixBlock {
                    op: ops("filter"),
                    terms: vec![Arg(Expr(Expression {
                        tag: tt("> col-name 1"),
                        blocks: vec![PrefixBlock {
                            op: ops(">"),
                            terms: vec![Arg(Ident(tt("col-name"))), Arg(Num(1.into(), tt("1")))],
                            in_ty: None,
                            out_ty: None
                        }
                        .into()],
                        out_ty: None
                    }))],
                    in_ty: None,
                    out_ty: None
                }
                .into()],
                out_ty: None
            }))
        ))
    );
}

#[test]
fn nested_expressions_without_braces() {
    let d = &Definitions::new();
    let src = line("filter > col-name 1e3");
    let b = block(&src, d)(&src.line);
    assert_eq!(
        b,
        Ok((
            "",
            PrefixBlock {
                op: ops("filter"),
                terms: vec![Arg(Expr(Expression {
                    tag: tt("> col-name 1e3"),
                    blocks: vec![PrefixBlock {
                        op: ops(">"),
                        terms: vec![Arg(Ident(tt("col-name"))), Arg(Num(1000.into(), tt("1e3")))],
                        in_ty: None,
                        out_ty: None
                    }
                    .into()],
                    out_ty: None
                }))],
                in_ty: None,
                out_ty: None
            }
        ))
    );

    let src = line("in asdf | filter > col-name 1e3");
    let e = expr(&src, d)(&src.line);
    assert_eq!(
        e,
        Ok((
            "",
            Expression {
                tag: tt(&src.line),
                blocks: vec![
                    PrefixBlock {
                        op: ops("in"),
                        terms: vec![Arg(Ident(tt("asdf")))],
                        in_ty: None,
                        out_ty: None
                    }
                    .into(),
                    PrefixBlock {
                        op: ops("filter"),
                        terms: vec![Arg(Expr(Expression {
                            tag: tt("> col-name 1e3"),
                            blocks: vec![PrefixBlock {
                                op: ops(">"),
                                terms: vec![
                                    Arg(Ident(tt("col-name"))),
                                    Arg(Num(1000.into(), tt("1e3")))
                                ],
                                in_ty: None,
                                out_ty: None
                            }
                            .into()],
                            out_ty: None
                        }))],
                        in_ty: None,
                        out_ty: None
                    }
                    .into()
                ],
                out_ty: None
            }
        ))
    );

    let src = line("in asdf | filter > col-name 1e3 | ls");
    let e = expr(&src, d)(&src.line);
    assert_eq!(
        e,
        Ok((
            "",
            Expression {
                tag: tt(&src.line),
                blocks: vec![
                    PrefixBlock {
                        op: ops("in"),
                        terms: vec![Arg(Ident(tt("asdf")))],
                        in_ty: None,
                        out_ty: None
                    }
                    .into(),
                    PrefixBlock {
                        op: ops("filter"),
                        terms: vec![Arg(Expr(Expression {
                            tag: tt("> col-name 1e3 "),
                            blocks: vec![PrefixBlock {
                                op: ops(">"),
                                terms: vec![
                                    Arg(Ident(tt("col-name"))),
                                    Arg(Num(1000.into(), tt("1e3")))
                                ],
                                in_ty: None,
                                out_ty: None
                            }
                            .into()],
                            out_ty: None
                        }))],
                        in_ty: None,
                        out_ty: None
                    }
                    .into(),
                    PrefixBlock {
                        op: ops("ls"),
                        terms: vec![],
                        in_ty: None,
                        out_ty: None
                    }
                    .into()
                ],
                out_ty: None
            }
        ))
    );
}

#[test]
fn known_op_test() {
    let d = &Definitions::new();
    let known_op = |s| {
        let line = line(s);
        let x = known_op(&line, d)(&line.line);
        x
    };
    assert!(known_op("> foo"));
    assert!(known_op("\\ foo"));
    assert!(known_op("filter foo"));
    assert!(!known_op("what foo"));
}

#[test]
fn def_param_test() {
    let l = line("--not");
    let x = def_param(&l)(&l.line);
    assert_eq!(
        x,
        Err(ParsingError::err(
            "-",
            "invalid identifier, expecting alphabetic character, found `-`",
            Expecting::None
        ))
    );

    let x = line("var rem");
    let x = def_param(&x)(&x.line);
    assert_eq!(
        x,
        Ok((
            " rem",
            Parameter {
                ident: tt("var"),
                ty: None
            }
        ))
    );

    let x = line("var:Num rem");
    let x = def_param(&x)(&x.line);
    assert_eq!(
        x,
        Ok((
            " rem",
            Parameter {
                ident: tt("var"),
                ty: Some(tt("Num"))
            }
        ))
    );
}

#[test]
fn def_params_test() {
    let x = line("asdf");
    let x = def_params(&x)(&x.line);
    assert_eq!(
        x,
        Err(ParsingError::err("asdf", "expected `(`", Expecting::None,))
    );

    let x = line("(asdf ");
    let x = def_params(&x)(&x.line);
    assert_eq!(
        x,
        Err(ParsingError::err("", "expected `)`", Expecting::None,))
    );

    let x = line("( asdf )");
    let x = def_params(&x)(&x.line).unwrap().1;
    assert_eq!(x.len(), 1);
    assert!(tag_eq(&x[0].ident, "asdf"));

    let x = line("( asdf test )");
    let x = def_params(&x)(&x.line).unwrap().1;
    assert_eq!(x.len(), 2);
    assert!(tag_eq(&x[0].ident, "asdf"));
    assert!(tag_eq(&x[1].ident, "test"));

    let x = line("( asdf test )");
    let x = def_params(&x)(&x.line).unwrap().1;
    assert_eq!(x.len(), 2);
    assert!(tag_eq(&x[0].ident, "asdf"));
    assert!(tag_eq(&x[1].ident, "test"));

    // errors
    let x = line("(test asdf test)");
    let x = def_params(&x)(&x.line);
    assert_eq!(
        x,
        Err(ParsingError::err(
            tt("test"),
            "parameters must be distinct: `test` has been previously defined",
            Expecting::None,
        ))
    );
}

#[test]
fn full_op_str() {
    // test that commands such as ls-files won't be recognised as `ls`.
    let x = line("ls what");
    let x = op(&x)(&x.line);
    assert_eq!(x, Ok((" what", ops("ls"))));
    let x = line("ls-files what");
    let x = op(&x)(&x.line);
    assert_eq!(x, Ok((" what", ops("ls-files"))));
}

#[test]
fn spec_op_chars() {
    let x = expression("+ 101 ", Location::Shell, &Definitions::new());
    assert_eq!(
        x,
        Ok(Expression {
            tag: tt("+ 101 "),
            blocks: vec![PrefixBlock {
                op: ops("+"),
                terms: vec![Arg(Num(101.into(), tt("101")))],
                in_ty: None,
                out_ty: None
            }
            .into()],
            out_ty: None
        })
    );
}

#[test]
fn def_ty_testing() {
    let x = definition_type("def-ty Ord::Lt|Eq|Gt", Location::Shell);
    assert_eq!(
        x,
        Ok(DefinitionType {
            loc: Location::Shell,
            src: "def-ty Ord::Lt|Eq|Gt".to_string(),
            name: tt("Ord"),
            ty: TypeVariant::Sum(vec![
                Variant {
                    name: tt("Lt"),
                    fields: None
                },
                Variant {
                    name: tt("Eq"),
                    fields: None
                },
                Variant {
                    name: tt("Gt"),
                    fields: None
                }
            ])
        })
    );

    let x = definition_type("def-ty Ord :: Lt | Eq | Gt", Location::Shell);
    assert_eq!(
        x,
        Ok(DefinitionType {
            loc: Location::Shell,
            src: "def-ty Ord :: Lt | Eq | Gt".to_string(),
            name: tt("Ord"),
            ty: TypeVariant::Sum(vec![
                Variant {
                    name: tt("Lt"),
                    fields: None
                },
                Variant {
                    name: tt("Eq"),
                    fields: None
                },
                Variant {
                    name: tt("Gt"),
                    fields: None
                }
            ])
        })
    );

    let x = definition_type("def-ty Point { x:Num y:Num }", Location::Shell);
    assert_eq!(
        x,
        Ok(DefinitionType {
            loc: Location::Shell,
            src: "def-ty Point { x:Num y:Num }".to_string(),
            name: tt("Point"),
            ty: TypeVariant::Product(vec![
                Field {
                    name: tt("x"),
                    ty: tt("Num"),
                    params: vec![]
                },
                Field {
                    name: tt("y"),
                    ty: tt("Num"),
                    params: vec![]
                },
            ])
        })
    );

    let x = definition_type("def-ty Eg :: N { v:Num } | S { s:Str }", Location::Shell);
    assert_eq!(
        x,
        Ok(DefinitionType {
            loc: Location::Shell,
            src: "def-ty Eg :: N { v:Num } | S { s:Str }".to_string(),
            name: tt("Eg"),
            ty: TypeVariant::Sum(vec![
                Variant {
                    name: tt("N"),
                    fields: Some(vec![Field {
                        name: tt("v"),
                        ty: tt("Num"),
                        params: vec![]
                    },])
                },
                Variant {
                    name: tt("S"),
                    fields: Some(vec![Field {
                        name: tt("s"),
                        ty: tt("Str"),
                        params: vec![]
                    },])
                }
            ])
        })
    );

    let x = definition_type(
        "def-ty Eg :: N { v:Num<A B C> } | S { s:Str }",
        Location::Shell,
    );
    assert_eq!(
        x,
        Ok(DefinitionType {
            loc: Location::Shell,
            src: "def-ty Eg :: N { v:Num<A B C> } | S { s:Str }".to_string(),
            name: tt("Eg"),
            ty: TypeVariant::Sum(vec![
                Variant {
                    name: tt("N"),
                    fields: Some(vec![Field {
                        name: tt("v"),
                        ty: tt("Num"),
                        params: vec![tt("A"), tt("B"), tt("C")]
                    },])
                },
                Variant {
                    name: tt("S"),
                    fields: Some(vec![Field {
                        name: tt("s"),
                        ty: tt("Str"),
                        params: vec![]
                    },])
                }
            ])
        })
    );
}

#[test]
fn no_type_on_field() {
    let x = definition_type("def-ty Point { x y }", Location::Shell)
        .unwrap_err()
        .0
        .to_string();
    println!("{x}");
    assert_eq!(
        x,
        "Parsing Error: could not parse input line
--> shell:16
 | def-ty Point { x y }
 |                 ^^^^ expected `:`
--> shell:16
 | def-ty Point { x y }
 |                 ^^^^ a field requires a type assignment: `field:Type`
"
    );

    let x = definition_type("def-ty Point { x: y:Num }", Location::Shell)
        .unwrap_err()
        .0
        .to_string();
    println!("{x}");
    assert_eq!(
        x,
        "Parsing Error: could not parse input line
--> shell:17
 | def-ty Point { x: y:Num }
 |                  ^ invalid identifier, expecting alphabetic character, found ` `
--> shell:17
 | def-ty Point { x: y:Num }
 |                  ^^^^^^^^ missing a valid type specifier: `field:Type`
"
    );

    let x = definition_type("def-ty Point { x:Num<A y:Num }", Location::Shell)
        .unwrap_err()
        .0
        .to_string();
    assert_eq!(
        x,
        "Parsing Error: could not parse input line
--> shell:24
 | def-ty Point { x:Num<A y:Num }
 |                         ^^^^^^ expected `>`
"
    );
}

#[test]
fn def_impl_on_ty() {
    let y = "def add Point () { in }";
    let x = definition_impl(y, Location::Shell, &Definitions::new());
    assert_eq!(
        x,
        Ok(DefinitionImpl {
            loc: Location::Shell,
            src: Arc::from(y),
            name: tt("add"),
            in_ty: Some(tt("Point")),
            params: vec![],
            expr: Expression {
                blocks: vec![PrefixBlock {
                    op: ops("in"),
                    terms: vec![],
                    in_ty: None,
                    out_ty: None
                }
                .into()],
                tag: tt("in "),
                out_ty: None
            }
        })
    );

    let y = "def + Point () { in }";
    let x = definition_impl(y, Location::Shell, &Definitions::new());
    assert_eq!(
        x,
        Ok(DefinitionImpl {
            loc: Location::Shell,
            src: Arc::from(y),
            name: tt("+"),
            in_ty: Some(tt("Point")),
            params: vec![],
            expr: Expression {
                blocks: vec![PrefixBlock {
                    op: ops("in"),
                    terms: vec![],
                    in_ty: None,
                    out_ty: None
                }
                .into()],
                tag: tt("in "),
                out_ty: None
            }
        })
    );
}

#[test]
fn op_with_path() {
    let x = line("Ord:Gt");
    let x = op(&x)(&x.line);
    assert_eq!(x, Ok((":Gt", ops("Ord"))));

    let x = line("Ord::Gt what");
    let x = op_ident(&x)(&x.line);
    assert_eq!(x, Ok(("::Gt what", tt("Ord"))));

    let x = line("Ord::Gt what");
    let x = op(&x)(&x.line);
    assert_eq!(x, Ok((" what", ops("Ord::Gt"))));

    let x = line("Ord:: what");
    let x = op(&x)(&x.line);
    assert_eq!(x, Ok((":: what", ops("Ord"))));
}

// -- partial parsing expecting checks
#[test]
fn incomplete_expecting_tests() {
    let exp = |s| parse(s, &Definitions::default()).map(|_| ()).unwrap_err().1;

    assert_eq!(exp("foo-bar | "), Expecting::Impl);
    assert_eq!(exp("foo-bar | in 5 {"), Expecting::Impl);
    assert_eq!(exp("def foo-bar "), Expecting::Type);
    assert_eq!(exp("def foo-bar Num "), Expecting::None);
}

#[test]
fn empty_string() {
    let l = line("'' else");
    assert_eq!(ident(&l)(&l.line), Ok((" else", tt(""))));
    let l = line(r#""""#);
    assert_eq!(ident(&l)(&l.line), Ok(("", tt(""))));
}

#[test]
fn brace_ends_arg() {
    let src = line("ident{in asdf } remaining");
    let x = ident(&src)(&src.line);
    assert_eq!(x, Ok(("{in asdf } remaining", tt("ident"))));

    let src = line("$rhs{in asdf } remaining");
    let x = term(&src, &Definitions::new())(&src.line);
    assert_eq!(x, Ok(("{in asdf } remaining", Arg(Var(tt("rhs"))))));

    let src = line("3.14{in asdf } remaining");
    let x = num(&src)(&src.line);
    assert_eq!(
        x,
        Ok(("{in asdf } remaining", (Number::from(3.14), tt("3.14"))))
    );
}

#[test]
fn no_padding() {
    let src = line("{in asdf } remaining");
    let x = term(&src, &Definitions::new())(&src.line);
    assert_eq!(
        x,
        Ok((
            " remaining",
            Arg(Expr(Expression {
                tag: tt("{in asdf }"),
                blocks: vec![PrefixBlock {
                    op: ops("in"),
                    terms: vec![Arg(Ident(tt("asdf")))],
                    in_ty: None,
                    out_ty: None
                }
                .into()],
                out_ty: None
            }))
        ))
    );

    let src = line("{in asdf} remaining");
    let x = term(&src, &Definitions::new())(&src.line);
    assert_eq!(
        x,
        Ok((
            " remaining",
            Arg(Expr(Expression {
                tag: tt("{in asdf}"),
                blocks: vec![PrefixBlock {
                    op: ops("in"),
                    terms: vec![Arg(Ident(tt("asdf")))],
                    in_ty: None,
                    out_ty: None
                }
                .into()],
                out_ty: None
            }))
        ))
    );

    let src = line("foo|bar|zog");
    let x = expr(&src, &Definitions::new())(&src.line);
    assert_eq!(
        x,
        Ok((
            "",
            Expression {
                tag: tt("foo|bar|zog"),
                blocks: vec![
                    PrefixBlock {
                        op: ops("foo"),
                        terms: vec![],
                        in_ty: None,
                        out_ty: None
                    }
                    .into(),
                    PrefixBlock {
                        op: ops("bar"),
                        terms: vec![],
                        in_ty: None,
                        out_ty: None
                    }
                    .into(),
                    PrefixBlock {
                        op: ops("zog"),
                        terms: vec![],
                        in_ty: None,
                        out_ty: None
                    }
                    .into()
                ],
                out_ty: None
            }
        ))
    );
}

#[test]
fn no_padding_integration() {
    let src = line("append{get first|if{= 0}{+ 100}{- 100}}");
    let x = expr(&src, &Definitions::new())(&src.line);
    assert_eq!(
        x,
        Ok((
            "",
            Expression {
                tag: tt("append{get first|if{= 0}{+ 100}{- 100}}"),
                blocks: vec![PrefixBlock {
                    op: ops("append"),
                    terms: vec![Arg(Expr(Expression {
                        tag: tt("{get first|if{= 0}{+ 100}{- 100}}"),
                        blocks: vec![
                            PrefixBlock {
                                op: ops("get"),
                                terms: vec![Arg(Ident(tt("first")))],
                                in_ty: None,
                                out_ty: None
                            }
                            .into(),
                            PrefixBlock {
                                op: ops("if"),
                                terms: vec![
                                    Arg(Expr(Expression {
                                        tag: tt("{= 0}"),
                                        blocks: vec![PrefixBlock {
                                            op: ops("="),
                                            terms: vec![Arg(Num(0.into(), tt("0")))],
                                            in_ty: None,
                                            out_ty: None
                                        }
                                        .into()],
                                        out_ty: None
                                    })),
                                    Arg(Expr(Expression {
                                        tag: tt("{+ 100}"),
                                        blocks: vec![PrefixBlock {
                                            op: ops("+"),
                                            terms: vec![Arg(Num(100.into(), tt("100")))],
                                            in_ty: None,
                                            out_ty: None
                                        }
                                        .into()],
                                        out_ty: None
                                    })),
                                    Arg(Expr(Expression {
                                        tag: tt("{- 100}"),
                                        blocks: vec![PrefixBlock {
                                            op: ops("-"),
                                            terms: vec![Arg(Num(100.into(), tt("100")))],
                                            in_ty: None,
                                            out_ty: None
                                        }
                                        .into()],
                                        out_ty: None
                                    }))
                                ],
                                in_ty: None,
                                out_ty: None
                            }
                            .into()
                        ],
                        out_ty: None
                    }))],
                    in_ty: None,
                    out_ty: None
                }
                .into()],
                out_ty: None
            }
        ))
    );
}

#[test]
fn no_padding_defty() {
    let src = line("def-ty Ord::Lt|Eq{x:Num y:Num}|Gt");
    let x = def_type_inner(&src.line, &src, Location::Shell);
    assert_eq!(
        x,
        Ok((
            "",
            DefinitionType {
                loc: Location::Shell,
                name: tt("Ord"),
                src: "def-ty Ord::Lt|Eq{x:Num y:Num}|Gt".to_string(),
                ty: TypeVariant::Sum(vec![
                    Variant {
                        name: tt("Lt"),
                        fields: None
                    },
                    Variant {
                        name: tt("Eq"),
                        fields: Some(vec![
                            Field {
                                name: tt("x"),
                                ty: tt("Num"),
                                params: vec![],
                            },
                            Field {
                                name: tt("y"),
                                ty: tt("Num"),
                                params: vec![],
                            }
                        ])
                    },
                    Variant {
                        name: tt("Gt"),
                        fields: None
                    },
                ])
            }
        ))
    );
}

#[test]
fn dot_infix_sml() {
    // works on the dot_infixed call
    let src = line("$x.y");
    let x = dot_infixed(Ident(tt("foo")), &src)(&src.line);
    assert_eq!(x, Err(ParsingError::err("$x.y", "", Expecting::None)));

    let src = line(".y remaining");
    let x = dot_infixed(Ident(tt("foo")), &src)(&src.line);
    assert_eq!(
        x,
        Ok((
            " remaining",
            DotOperatorBlock {
                op: tt("."),
                lhs: Ident(tt("foo")),
                rhs: tt("y"),
                out_ty: None
            }
        ))
    );

    let src = line(".y.z remaining");
    let x = dot_infixed(Ident(tt("foo")), &src)(&src.line);
    assert_eq!(
        x,
        Ok((
            ".z remaining",
            DotOperatorBlock {
                op: tt("."),
                lhs: Ident(tt("foo")),
                rhs: tt("y"),
                out_ty: None
            }
        ))
    );

    let src = line(".$y remaining");
    let x = dot_infixed(Ident(tt("foo")), &src)(&src.line);
    assert_eq!(
        x,
        Err(ParsingError::failure(
            ErrIn::S("$"),
            "invalid identifier, expecting alphabetic character, found `$`",
            Expecting::None,
        ))
    );

    // Below we test if encasing identifiers works
    let src = line(".'y y'.z remaining");
    let x = dot_infixed(Ident(tt("foo")), &src)(&src.line);
    assert_eq!(
        x,
        Ok((
            ".z remaining",
            DotOperatorBlock {
                op: tt("."),
                lhs: Ident(tt("foo")),
                rhs: tt("y y"),
                out_ty: None
            }
        ))
    );

    let src = line(r#"."y y".z remaining"#);
    let x = dot_infixed(Ident(tt("foo")), &src)(&src.line);
    assert_eq!(
        x,
        Ok((
            ".z remaining",
            DotOperatorBlock {
                op: tt("."),
                lhs: Ident(tt("foo")),
                rhs: tt("y y"),
                out_ty: None
            }
        ))
    );
}

#[test]
fn dot_infix_large() {
    let d = &Definitions::new();

    let src = line("$x.y");
    let x = term(&src, d)(&src.line);
    assert_eq!(
        x,
        Ok((
            "",
            Arg(Expr(Expression {
                tag: tt("$x.y"),
                blocks: vec![DotOperatorBlock {
                    op: tt("."),
                    lhs: Var(tt("x")),
                    rhs: tt("y"),
                    out_ty: None
                }
                .into()],
                out_ty: None
            }))
        ))
    );

    let src = line("$x.foo-bar.'foo bar/zog'");
    let x = term(&src, d)(&src.line);
    assert_eq!(
        x,
        Ok((
            "",
            Arg(Expr(Expression {
                tag: tt("$x.foo-bar.'foo bar/zog"),
                blocks: vec![DotOperatorBlock {
                    op: tt("."),
                    lhs: Expr(Expression {
                        tag: tt("$x.foo-bar"),
                        blocks: vec![DotOperatorBlock {
                            op: tt("."),
                            lhs: Var(tt("x")),
                            rhs: tt("foo-bar"),
                            out_ty: None,
                        }
                        .into()],
                        out_ty: None
                    }),
                    rhs: tt("foo bar/zog"),
                    out_ty: None
                }
                .into()],
                out_ty: None
            }))
        ))
    );
}

#[test]
fn boolean_parsing() {
    let d = &Definitions::new();
    let src = line("#t foo");
    let x = term(&src, d)(&src.line);
    assert_eq!(x, Ok((" foo", Arg(Pound('t', tt("#t"))))));
    let src = line("#tfoo");
    let x = term(&src, d)(&src.line);
    assert_eq!(
        x,
        Err(ParsingError::failure(
            tt("tfoo"),
            "special literals only have one character",
            Expecting::SpecLiteral
        ))
    );

    let src = line("in #tfoo zog");
    let x = expr(&src, d)(&src.line);
    assert_eq!(
        x,
        Err(E::Failure(ParsingError {
            locs: vec![
                (
                    tt("tfoo").into(),
                    "special literals only have one character".into()
                ),
                ("in #tfoo zog".into(), "no command".into()),
            ],

            expecting: Expecting::SpecLiteral,
        }))
    );

    let src = line("in #");
    let x = expr(&src, d)(&src.line);
    assert_eq!(
        x,
        Err(E::Failure(ParsingError {
            locs: vec![
                ("".into(), "empty identifier".into()),
                ("in #".into(), "no command".into()),
            ],

            expecting: Expecting::SpecLiteral,
        }))
    );
}

#[test]
fn multiline_def_expecting_impl() {
    let d = &Definitions::new();
    let x = definition_impl(
        "def foo Zog () {
    ",
        Location::Shell,
        d,
    );
    assert!(matches!(x, Err((_, Expecting::Impl))));
}

#[test]
fn spec_ops_dont_need_trailing_space() {
    let src = line("\\#t");
    let x = op(&src)(&src.line);
    assert_eq!(x, Ok(("#t", ops("\\"))));
    let src = line("+#t");
    let x = op(&src)(&src.line);
    assert_eq!(x, Ok(("#t", ops("+"))));

    let defs = &Definitions::new();
    let src = line("\\#t");
    let x = block(&src, defs)(&src.line);
    assert_eq!(
        x,
        Ok((
            "",
            PrefixBlock {
                op: ops("\\"),
                terms: vec![Arg(Pound('t', tt("#t")))],
                in_ty: None,
                out_ty: None
            }
        ))
    );
    let src = line("+#t");
    let x = block(&src, defs)(&src.line);
    assert_eq!(
        x,
        Ok((
            "",
            PrefixBlock {
                op: ops("+"),
                terms: vec![Arg(Pound('t', tt("#t")))],
                in_ty: None,
                out_ty: None
            }
        ))
    );
}

#[test]
fn backslash_str() {
    let l = line("foo\\bar else");
    assert_eq!(ident(&l)(&l.line), Ok((" else", tt("foo\\bar"))));
    let l = line("'foo bar\\zog' else");
    assert_eq!(ident(&l)(&l.line), Ok((" else", tt("foo bar\\zog"))));
    let l = line(r#""foo bar\zog""#);
    assert_eq!(ident(&l)(&l.line), Ok(("", tt("foo bar\\zog"))));
}

#[test]
fn ty_annotation_01_op() {
    let defs = &Definitions::new();

    let l = line(":Num foo:Bar zog");
    assert_eq!(
        block(&l, defs)(&l.line),
        Ok((
            "",
            PrefixBlock {
                op: ops("foo"),
                terms: vec![Arg(Ident(tt("zog")))],
                in_ty: Some(tt("Num")),
                out_ty: Some(tt("Bar")),
            }
        ))
    );

    let l = line(":Num foo zog");
    assert_eq!(
        block(&l, defs)(&l.line),
        Ok((
            "",
            PrefixBlock {
                op: ops("foo"),
                terms: vec![Arg(Ident(tt("zog")))],
                in_ty: Some(tt("Num")),
                out_ty: None,
            }
        ))
    );

    let l = line("foo:Bar zog");
    assert_eq!(
        block(&l, defs)(&l.line),
        Ok((
            "",
            PrefixBlock {
                op: ops("foo"),
                terms: vec![Arg(Ident(tt("zog")))],
                in_ty: None,
                out_ty: Some(tt("Bar")),
            }
        ))
    );
}

#[test]
fn ty_annotation_02_err() {
    let defs = &Definitions::new();

    let l = line(": foo:Bar zog");
    let x = block(&l, defs)(&l.line);
    let (e, exp) = convert_parse_error(x.unwrap_err(), &l.line, Location::Ogma);
    let x = e.to_string();
    println!("{}", x);
    assert_eq!(exp, Expecting::Type);
    assert_eq!(
        &x,
        "Parsing Error: could not parse input line
--> <ogma>:1
 | : foo:Bar zog
 |  ^ invalid identifier, expecting alphabetic character, found ` `
--> <ogma>:1
 | : foo:Bar zog
 |  ^^^^^^^^^^^^ expecting a type identifier
"
    );

    let l = line(":Num foo: zog");
    let x = block(&l, defs)(&l.line);
    let (e, exp) = convert_parse_error(x.unwrap_err(), &l.line, Location::Ogma);
    let x = e.to_string();
    println!("{}", x);
    assert_eq!(exp, Expecting::Type);
    assert_eq!(
        &x,
        "Parsing Error: could not parse input line
--> <ogma>:9
 | :Num foo: zog
 |          ^ invalid identifier, expecting alphabetic character, found ` `
--> <ogma>:9
 | :Num foo: zog
 |          ^^^^ expecting a type identifier
"
    );

    let l = line(":Num foo zog:Bar");
    let x = block(&l, defs)(&l.line);
    let (e, exp) = convert_parse_error(x.unwrap_err(), &l.line, Location::Ogma);
    let x = e.to_string();
    println!("{}", x);
    assert_eq!(exp, Expecting::Term);
    assert_eq!(
        &x,
        "Parsing Error: could not parse input line
--> <ogma>:12
 | :Num foo zog:Bar
 |             ^^^^ unexpected type identifier
"
    );
}

#[test]
fn ty_annotation_03_nested() {
    let defs = &Definitions::new();

    let l = line(":Num foo:Bar ls");
    assert_eq!(
        block(&l, defs)(&l.line),
        Ok((
            "",
            PrefixBlock {
                op: ops("foo"),
                terms: vec![Arg(Expr(Expression {
                    tag: tt("ls"),
                    blocks: vec![PrefixBlock {
                        op: ops("ls"),
                        terms: vec![],
                        in_ty: None,
                        out_ty: None
                    }
                    .into()],
                    out_ty: None
                }))],
                in_ty: Some(tt("Num")),
                out_ty: Some(tt("Bar")),
            }
        ))
    );

    let l = line("foo zog ls:Bar");
    assert_eq!(
        block(&l, defs)(&l.line),
        Ok((
            "",
            PrefixBlock {
                op: ops("foo"),
                terms: vec![
                    Arg(Ident(tt("zog"))),
                    Arg(Expr(Expression {
                        tag: tt("ls:Bar"),
                        blocks: vec![PrefixBlock {
                            op: ops("ls"),
                            terms: vec![],
                            in_ty: None,
                            out_ty: Some(tt("Bar")),
                        }
                        .into(),],
                        out_ty: None
                    }))
                ],
                in_ty: None,
                out_ty: None,
            }
        ))
    );

    let l = line("foo :Bar ls:Zog"); // error!
    let x = block(&l, defs)(&l.line);
    let (e, exp) = convert_parse_error(x.unwrap_err(), &l.line, Location::Ogma);
    let x = e.to_string();
    println!("{}", x);
    assert_eq!(exp, Expecting::Term);
    assert_eq!(
        &x,
        "Parsing Error: could not parse input line
--> <ogma>:4
 | foo :Bar ls:Zog
 |     ^^^^ unexpected type identifier
"
    );

    let l = line("foo:Num ls:Zog"); // okay!
    assert_eq!(
        block(&l, defs)(&l.line),
        Ok((
            "",
            PrefixBlock {
                op: ops("foo"),
                terms: vec![Arg(Expr(Expression {
                    tag: tt("ls:Zog"),
                    blocks: vec![PrefixBlock {
                        op: ops("ls"),
                        terms: vec![],
                        in_ty: None,
                        out_ty: Some(tt("Zog")),
                    }
                    .into(),],
                    out_ty: None
                }))],
                in_ty: None,
                out_ty: Some(tt("Num")),
            }
        ))
    );
}

#[test]
fn ty_annotation_04_dotop() {
    let defs = &Definitions::new();

    let l = line("foo $row.var:Str");
    assert_eq!(
        block(&l, defs)(&l.line),
        Ok((
            "",
            PrefixBlock {
                op: ops("foo"),
                terms: vec![Arg(Expr(Expression {
                    tag: tt("$row.var:Str"),
                    blocks: vec![DotOperatorBlock {
                        lhs: Var(tt("row")),
                        op: tt("."),
                        rhs: tt("var"),
                        out_ty: Some(tt("Str")),
                    }
                    .into()],
                    out_ty: None
                }))],
                in_ty: None,
                out_ty: None,
            }
        ))
    );

    let l = line("foo $row.var :Bar"); // error!
    let x = block(&l, defs)(&l.line);
    let (e, exp) = convert_parse_error(x.unwrap_err(), &l.line, Location::Ogma);
    let x = e.to_string();
    println!("{}", x);
    assert_eq!(exp, Expecting::Term);
    assert_eq!(
        &x,
        "Parsing Error: could not parse input line
--> <ogma>:13
 | foo $row.var :Bar
 |              ^^^^ unexpected type identifier
"
    );

    let l = line("foo $row.:Bar var"); // error!
    let x = block(&l, defs)(&l.line);
    let (e, exp) = convert_parse_error(x.unwrap_err(), &l.line, Location::Ogma);
    let x = e.to_string();
    println!("{}", x);
    assert_eq!(exp, Expecting::None);
    assert_eq!(
        &x,
        "Parsing Error: could not parse input line
--> <ogma>:9
 | foo $row.:Bar var
 |          ^ invalid identifier, expecting alphabetic character, found `:`
"
    );
}

#[test]
fn ty_annotation_05_expr() {
    let defs = &Definitions::new();

    let l = line("foo {:Bar zog:Num }:Bool");
    assert_eq!(
        block(&l, defs)(&l.line),
        Ok((
            "",
            PrefixBlock {
                op: ops("foo"),
                terms: vec![Arg(Expr(Expression {
                    tag: tt("{:Bar zog:Num }:Bool"),
                    blocks: vec![PrefixBlock {
                        op: ops("zog"),
                        terms: vec![],
                        in_ty: Some(tt("Bar")),
                        out_ty: Some(tt("Num")),
                    }
                    .into()],
                    out_ty: Some(tt("Bool")),
                }))],
                in_ty: None,
                out_ty: None,
            }
        ))
    );

    let l = line("foo {:Bar zog:Num |:Fog hir:Str }:Bool");
    assert_eq!(
        block(&l, defs)(&l.line),
        Ok((
            "",
            PrefixBlock {
                op: ops("foo"),
                terms: vec![Arg(Expr(Expression {
                    tag: tt("{:Bar zog:Num |:Fog hir:Str }:Bool"),
                    blocks: vec![
                        PrefixBlock {
                            op: ops("zog"),
                            terms: vec![],
                            in_ty: Some(tt("Bar")),
                            out_ty: Some(tt("Num")),
                        }
                        .into(),
                        PrefixBlock {
                            op: ops("hir"),
                            terms: vec![],
                            in_ty: Some(tt("Fog")),
                            out_ty: Some(tt("Str")),
                        }
                        .into()
                    ],
                    out_ty: Some(tt("Bool")),
                }))],
                in_ty: None,
                out_ty: None,
            }
        ))
    );

    let l = line("foo {:Bar zog:Num} :Bool"); // error!
    let x = block(&l, defs)(&l.line);
    let (e, exp) = convert_parse_error(x.unwrap_err(), &l.line, Location::Ogma);
    let x = e.to_string();
    println!("{}", x);
    assert_eq!(exp, Expecting::Term);
    assert_eq!(
        &x,
        "Parsing Error: could not parse input line
--> <ogma>:19
 | foo {:Bar zog:Num} :Bool
 |                    ^^^^^ unexpected type identifier
"
    );
}

#[test]
fn iblock_impls() {
    let defs = &Definitions::new();

    let l = line(":Num foo:Bar");
    let (_, b) = block(&l, defs)(&l.line).unwrap();
    assert_eq!(b.block_tag(), tt(":Num foo:Bar"));
}

#[test]
fn path_parsing() {
    let l = line("path/to/something");
    let (_, x) = path(&l)(&l.line).unwrap();
    assert_eq!(
        x,
        Path {
            components: vec![tt("path"), tt("to"), tt("something")].into(),
            idx: 0,
            rooted: false,
        }
    );

    let l = line("path/to /something");
    let (_, x) = path(&l)(&l.line).unwrap();
    assert_eq!(
        x,
        Path {
            components: vec![tt("path"), tt("to")].into(),
            idx: 0,
            rooted: false,
        }
    );

    let l = line("/path/to/something");
    let (_, x) = path(&l)(&l.line).unwrap();
    assert_eq!(
        x,
        Path {
            components: vec![tt("path"), tt("to"), tt("something")].into(),
            idx: 0,
            rooted: true,
        }
    );
}

#[test]
fn path_parsing_errs() {
    let l = line("path/to/");
    let x = path(&l)(&l.line).unwrap_err();
    assert_eq!(
        x,
        E::Error(ParsingError {
            expecting: Expecting::Path,
            locs: vec![("path/to/".into(), "trailing partition delimiter".into())]
        })
    );

    let l = line("path/1");
    let x = path(&l)(&l.line).unwrap_err();
    assert_eq!(
        x,
        E::Error(ParsingError {
            expecting: Expecting::None,
            locs: vec![("1".into(), "not a valid partition component".into()),]
        })
    );

    let l = line("path/to/ ");
    let x = path(&l)(&l.line).unwrap_err();
    assert_eq!(
        x,
        E::Error(ParsingError {
            expecting: Expecting::None,
            locs: vec![(" ".into(), "not a valid partition component".into())]
        })
    );

    let l = line("path/1 foo bar");
    let x = path(&l)(&l.line).unwrap_err();
    assert_eq!(
        x,
        E::Error(ParsingError {
            expecting: Expecting::None,
            locs: vec![("1".into(), "not a valid partition component".into())]
        })
    );
}
