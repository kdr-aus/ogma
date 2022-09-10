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
}

/// An item contains code and an optional documentation string.
#[derive(PartialEq, Eq, Debug)]
pub struct Item {
    /// Documentation string.
    pub doc: Option<String>,
    /// Code, including the keywords for types and impls.
    pub code: String,
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
    let (doc, mut text) = doc_comment(line.line.trim());
    let doc = (!doc.is_empty()).then_some(doc);

    let mut directives = Vec::new();
    let text = loop {
        let (t, ds) = opt(terminated(directive_line(), cut(newline)))(text)
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

fn directive_line() -> impl FnMut(&str) -> IResult<&str, Vec<Directive>, ParsingError> {
    move |i| {
        let i = i.trim_start();
        delimited(
            char('['),
            separated_list1(space1, directive()),
            cut(preceded(space0, char(']'))),
        )(i)
    }
}

fn directive() -> impl FnMut(&str) -> IResult<&str, Directive, ParsingError> {
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

        Err(ParsingError::err(
            i,
            "unrecognised directive",
            Expecting::NONE,
        ))
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

    #[test]
    fn directive_line_test_01() {
        let d = |i| directive_line()(i);

        assert_eq!(
            d("[no-parallelise]"),
            Ok(("", vec![Directive::NoParallelise]))
        );
        assert_eq!(d("[fail-fast]"), Ok(("", vec![Directive::FailFast])));
        assert_eq!(
            d("[no-parallelise fail-fast]"),
            Ok(("", vec![Directive::NoParallelise, Directive::FailFast]))
        );
        assert!(d("[no-parallelise, fail-fast]").is_err());
        assert!(d("[]").is_err());
        assert!(d("[no-parallelise, fail-fast").is_err());
        assert!(d("[no-parallelise, fail-fast").is_err());
        assert_eq!(
            d("[ no-parallelise fail-fast  ]"),
            Ok(("", vec![Directive::NoParallelise, Directive::FailFast]))
        );
        assert!(d("[no-parallelise, fail-fast
]")
        .is_err());
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
}
