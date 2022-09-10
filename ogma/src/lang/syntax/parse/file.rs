use super::*;

/// File constituents.
#[derive(Debug)]
pub struct File {
    /// A document string.
    pub doc: Option<String>,
    /// Any [Directive]s.
    pub directives: Vec<Directive>,
    /// All type definitions.
    ///
    /// Each type is keyed with it's name.
    pub types: Vec<(String, Item)>,
    /// All implementation definitions.
    ///
    /// Each impl is keyed with it's name.
    pub impls: Vec<(String, Item)>,
    /// All expressions _in definition order_.
    pub exprs: Vec<Item>,
}

/// File directives.
#[derive(PartialEq, Eq, Debug)]
pub enum Directive {
    /// Evaluate expressions in order.
    NoParallelise,
    /// Stop processing if an expression fails.
    FailFast,
    /// Import items.
    Import(Vec<Import>),
    /// Export items.
    Export(Vec<Glob>),
}

/// An item contains code and an optional documentation string.
#[derive(PartialEq, Eq, Debug)]
pub struct Item {
    /// Documentation string.
    pub doc: Option<String>,
    /// Code, including the keywords for types and impls.
    pub code: String,
}

type Glob = Tag;

/// Import path.
#[derive(PartialEq, Eq, Debug)]
pub struct Import {
    /// The leading partition path.
    pub path: Vec<Tag>,
    /// The items glob pattern.
    pub glob: Glob,
}

/// Parse a complete file to return the _item pointers_ and directives that exist in the file.
///
/// Note that the items themselves are not parsed, only the outline of the file.
pub fn file(text: &str, loc: Location) -> Result<File, err::Error> {
    let line = Line {
        loc: loc.clone(),
        line: text.clone().into(),
    };

    // first, get all the lines that are comments
    let (doc, mut text) = doc_comment(line.line.trim_start());
    let doc = (!doc.is_empty()).then_some(doc);

    let mut directives = Vec::new();
    let text = loop {
        let (t, ds) = opt(terminated(directive_line(&line), cut(line_ending)))(text)
            .map_err(|e| convert_parse_error(e, &line.line, loc.clone()).0)?;
        match ds {
            Some(ds) => {
                directives.extend(ds.into_iter());
                text = t;
            }
            None => break t,
        }
    };

    let items = split_items(text);

    let mut impls = Vec::new();
    let mut types = Vec::new();
    let mut exprs = Vec::new();

    for item in items {
        let (doc, code) = doc_comment(item);
        let code = code.trim();

        if code.starts_with("def-ty") {
            let (_, name) = defty_name(&line)(code)
                .map_err(|e| convert_parse_error(e, &line.line, loc.clone()).0)?;
            types.push((
                name.to_string(),
                Item {
                    doc: (!doc.is_empty()).then_some(doc),
                    code: code.to_owned(),
                },
            ));
        } else if code.starts_with("def") {
            let (_, name) = def_op(&line)(code)
                .map_err(|e| convert_parse_error(e, &line.line, loc.clone()).0)?;
            impls.push((
                name.to_string(),
                Item {
                    doc: (!doc.is_empty()).then_some(doc),
                    code: code.to_owned(),
                },
            ));
        } else {
            exprs.push(Item {
                doc: (!doc.is_empty()).then_some(doc),
                code: code.to_owned(),
            });
        }
    }

    Ok(File {
        doc,
        directives,
        impls,
        types,
        exprs,
    })
}

fn doc_comment(text: &str) -> (String, &str) {
    let mut lines = text.lines();
    let mut t = text;
    let mut doc = String::new();
    while let Some(line) = lines.next() {
        match line.trim().strip_prefix('#') {
            Some(l) => {
                doc.push_str(l.trim());
                doc.push('\n');
                t = &text[text.offset(line) + line.len()..];
            }
            None => break,
        }
    }

    doc.pop();

    (doc, t)
}

fn directive_line(
    line: &Line,
) -> impl FnMut(&str) -> IResult<&str, Vec<Directive>, ParsingError> + '_ {
    move |i| {
        let i = i.trim_start();
        delimited(
            char('['),
            separated_list1(space1, directive(line)),
            cut(preceded(space0, char(']'))),
        )(i)
    }
}

fn directive(line: &Line) -> impl FnMut(&str) -> IResult<&str, Directive, ParsingError> + '_ {
    move |i| {
        let (i, _) = space0(i)?;
        let x = map(tag("no-parallelise"), |_| Directive::NoParallelise)(i);
        if x.is_ok() {
            return x;
        }

        let x = map(tag("fail-fast"), |_| Directive::FailFast)(i);
        if x.is_ok() {
            return x;
        }

        if let Ok((i, _)) = tag::<_, _, ()>("import")(i) {
            return map(imports(line), Directive::Import)(i);
        }

        if let Ok((i, _)) = tag::<_, _, ()>("export")(i) {
            return map(exports(line), Directive::Export)(i);
        }

        Err(ParsingError::err(
            i,
            "unrecognised directive",
            Expecting::NONE,
        ))
    }
}

fn exports(line: &Line) -> impl FnMut(&str) -> IResult<&str, Vec<Glob>, ParsingError> + '_ {
    move |i| {
        delimited(
            char('('),
            separated_list1(space1, preceded(space0, glob(line))),
            preceded(space0, char(')')),
        )(i)
    }
}

fn glob(line: &Line) -> impl FnMut(&str) -> IResult<&str, Glob, ParsingError> + '_ {
    move |i| {
        map(take_till1(|c: char| c.is_whitespace() || c == ')'), |x| {
            line.create_tag(x)
        })(i)
    }
}

fn imports(line: &Line) -> impl FnMut(&str) -> IResult<&str, Vec<Import>, ParsingError> + '_ {
    move |i| {
        delimited(
            char('('),
            separated_list1(space1, preceded(space0, import(line))),
            preceded(space0, char(')')),
        )(i)
    }
}

fn import(line: &Line) -> impl FnMut(&str) -> IResult<&str, Import, ParsingError> + '_ {
    move |i| {
        let (i, mut path) = separated_list1(
            char('/'),
            take_till1(|c: char| c.is_whitespace() || c == ')' || c == '/'),
        )(i)?;

        let (_, glob) = glob(line)(path.pop().expect("at least one"))?;

        let path = path
            .into_iter()
            .map(|p| op_ident(line)(p).map(|(_, x)| x))
            .collect::<Result<_, _>>()?;

        Ok((i, Import { path, glob }))
    }
}

fn split_items(text: &str) -> Vec<&str> {
    let lines = text.lines();
    let mut ss = Vec::new();

    let mut new = true;
    for line in lines {
        if line.trim().is_empty() {
            new = true;
            continue;
        }

        // line is not empty
        if new {
            ss.push(line); // push a new item block
            new = false;
        } else {
            // update last block
            let last = ss.last_mut().expect("should at least have a new block");
            // update to start of block (remains the same) to the offset of this
            // lines end
            *last = &text[text.offset(last)..text.offset(line) + line.len()];
        }
    }

    ss
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn doc_comment_test() {
        let (d, s) = doc_comment("");
        assert_eq!(&d, "");
        assert_eq!(s, "");

        let (d, s) = doc_comment("no comment");
        assert_eq!(&d, "");
        assert_eq!(s, "no comment");

        let (d, s) = doc_comment("# A doc comment!");
        assert_eq!(&d, "A doc comment!");
        assert_eq!(s, "");

        let (d, s) = doc_comment(
            "# A doc comment!
with something below",
        );
        assert_eq!(&d, "A doc comment!");
        assert_eq!(s, "\nwith something below");

        let (d, s) = doc_comment(
            "# A doc comment!
# on more lines
with something below
after that",
        );
        assert_eq!(
            &d,
            "A doc comment!
on more lines"
        );
        assert_eq!(
            s,
            "\nwith something below
after that"
        );
    }

    fn test_directive_line(s: &str, exp: Option<Vec<Directive>>) {
        let l = Line::from(s);
        let x = directive_line(&l)(&l.line);
        match exp {
            Some(exp) => assert_eq!(x, Ok(("", exp))),
            None => assert!(x.is_err()),
        }
    }

    #[test]
    fn directive_line_test_01() {
        test_directive_line("[no-parallelise]", Some(vec![Directive::NoParallelise]));
        test_directive_line("[fail-fast]", Some(vec![Directive::FailFast]));
        test_directive_line(
            "[no-parallelise fail-fast]",
            Some(vec![Directive::NoParallelise, Directive::FailFast]),
        );
        test_directive_line("[no-parallelise, fail-fast]", None);
        test_directive_line("[]", None);
        test_directive_line("[no-parallelise, fail-fast", None);
        test_directive_line("[no-parallelise, fail-fast", None);
        test_directive_line(
            "[ no-parallelise fail-fast  ]",
            Some(vec![Directive::NoParallelise, Directive::FailFast]),
        );
        test_directive_line(
            "[no-parallelise, fail-fast
]",
            None,
        );
    }

    #[test]
    fn directive_line_test_02() {
        test_directive_line(
            "[export(foo bar ?zog)]",
            Some(vec![Directive::Export(vec![
                tt("foo"),
                tt("bar"),
                tt("?zog"),
            ])]),
        );
        test_directive_line("[export()]", None);
        test_directive_line("[export(foo bar]", None);
        test_directive_line(
            "[ export( foo ) ]",
            Some(vec![Directive::Export(vec![tt("foo")])]),
        );
    }

    #[test]
    fn directive_line_test_03() {
        test_directive_line(
            "[import(yo yo/path path/?zog)]",
            Some(vec![Directive::Import(vec![
                Import {
                    path: vec![],
                    glob: tt("yo"),
                },
                Import {
                    path: vec![tt("yo")],
                    glob: tt("path"),
                },
                Import {
                    path: vec![tt("path")],
                    glob: tt("?zog"),
                },
            ])]),
        );
        test_directive_line("[import()]", None);
        test_directive_line("[export(foo bar]", None);
        test_directive_line(
            "[ import( foo ) ]",
            Some(vec![Directive::Import(vec![Import {
                path: vec![],
                glob: tt("foo"),
            }])]),
        );
    }

    #[test]
    fn split_items_test() {
        let s = "
Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua.
Nunc aliquet bibendum enim facilisis gravida neque.
Orci sagittis eu volutpat odio facilisis mauris sit.
Aliquam faucibus purus in massa tempor nec feugiat nisl pretium.



Ornare lectus sit amet est placerat in egestas erat imperdiet.

Dolor sit amet consectetur adipiscing elit ut aliquam purus.
Amet mauris commodo quis imperdiet massa tincidunt nunc.

Vitae turpis massa sed elementum tempus egestas sed.
Cursus eget nunc scelerisque viverra mauris.



Turpis in eu mi bibendum neque egestas congue quisque egestas.
Eget aliquet nibh praesent tristique magna sit.
Ultrices sagittis orci a scelerisque purus.
Natoque penatibus et magnis dis parturient montes.


Lectus arcu bibendum at varius vel.

Dignissim cras tincidunt lobortis feugiat vivamus at augue eget arcu.
Bibendum at varius vel pharetra vel turpis.
Morbi tempus iaculis urna id volutpat lacus laoreet non.
Neque volutpat ac tincidunt vitae semper quis lectus.


";

        let ss = split_items(s);

        assert_eq!(ss, vec![
            "Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua.
Nunc aliquet bibendum enim facilisis gravida neque.
Orci sagittis eu volutpat odio facilisis mauris sit.
Aliquam faucibus purus in massa tempor nec feugiat nisl pretium.",
"Ornare lectus sit amet est placerat in egestas erat imperdiet.",
"Dolor sit amet consectetur adipiscing elit ut aliquam purus.
Amet mauris commodo quis imperdiet massa tincidunt nunc.",
"Vitae turpis massa sed elementum tempus egestas sed.
Cursus eget nunc scelerisque viverra mauris.",
"Turpis in eu mi bibendum neque egestas congue quisque egestas.
Eget aliquet nibh praesent tristique magna sit.
Ultrices sagittis orci a scelerisque purus.
Natoque penatibus et magnis dis parturient montes.",
"Lectus arcu bibendum at varius vel.",
"Dignissim cras tincidunt lobortis feugiat vivamus at augue eget arcu.
Bibendum at varius vel pharetra vel turpis.
Morbi tempus iaculis urna id volutpat lacus laoreet non.
Neque volutpat ac tincidunt vitae semper quis lectus."
        ]);
    }

    #[test]
    fn file_test_01() {
        let f = "# A doc comment

[fail-fast]

def foo-bar () { }

def-ty Woah code goes here

first expr

# Bzog docs
def bar-zog () { }

an xpr | zog

";

        let f = file(f, Location::Shell).unwrap();

        dbg!(&f);

        assert_eq!(f.doc.as_deref(), Some("A doc comment"));
        assert_eq!(f.directives, vec![Directive::FailFast]);
        assert_eq!(
            f.types,
            vec![(
                "Woah".to_string(),
                Item {
                    doc: None,
                    code: "def-ty Woah code goes here".to_string()
                }
            )]
        );
        assert_eq!(
            f.impls,
            vec![
                (
                    "foo-bar".to_string(),
                    Item {
                        doc: None,
                        code: "def foo-bar () { }".to_string()
                    }
                ),
                (
                    "bar-zog".to_string(),
                    Item {
                        doc: Some("Bzog docs".to_string()),
                        code: "def bar-zog () { }".to_string()
                    }
                )
            ]
        );
        assert_eq!(
            f.exprs,
            vec![
                Item {
                    doc: None,
                    code: "first expr".to_string(),
                },
                Item {
                    doc: None,
                    code: "an xpr | zog".to_string()
                }
            ]
        );
    }

    #[test]
    fn file_test_02() {
        let f = "

[fail-fast]
[no-parallelise]
";

        let f = file(f, Location::Shell).unwrap();

        dbg!(&f);

        assert_eq!(f.doc, None);
        assert_eq!(
            f.directives,
            vec![Directive::FailFast, Directive::NoParallelise]
        );
        assert!(f.types.is_empty());
        assert!(f.impls.is_empty());
        assert!(f.exprs.is_empty());
    }

    #[test]
    fn import_test() {
        fn t(s: &str, exp: Option<Import>) {
            let l = Line::from(s);
            let x = import(&l)(&l.line);
            dbg!(&x);
            match exp {
                Some(exp) => assert_eq!(x, Ok(("", exp))),
                None => assert!(x.is_err()),
            }
        }

        t(
            "yo",
            Some(Import {
                path: vec![],
                glob: tt("yo"),
            }),
        );

        t(
            "yo/path",
            Some(Import {
                path: vec![tt("yo")],
                glob: tt("path"),
            }),
        );

        t(
            "yo/path/*",
            Some(Import {
                path: vec![tt("yo"), tt("path")],
                glob: tt("*"),
            }),
        );

        t(
            "yo/path/{a,b}",
            Some(Import {
                path: vec![tt("yo"), tt("path")],
                glob: tt("{a,b}"),
            }),
        );

        t(
            "yo/path/[a,b]",
            Some(Import {
                path: vec![tt("yo"), tt("path")],
                glob: tt("[a,b]"),
            }),
        );

        t("yo/*/path", None);
    }
}
