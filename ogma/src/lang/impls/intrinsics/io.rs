use super::*;
use rt::fscache::FSCACHE;
use std::io::{self, Write};

pub fn add_intrinsics(impls: &mut Implementations) {
    add! { impls,
        ("ls", Table, ls_table, Io)
        (ls, Io)

        (open, Io)
        (save, Io)
    };
}

// ------ Helpers --------------------------------------------------------------
/// Joins path onto the current cx working directory.
/// If the path goes beyond the store root then an error is returned to disallow users to walk
/// around outside the workspace folders.
fn scrub_filepath(path: &str, cx: &Context) -> io::Result<std::path::PathBuf> {
    let root = cx.root;
    let wd = cx.root.join(cx.wd);

    let wd = wd
        .join(path)
        .canonicalize()
        .map_err(|e| io::Error::new(e.kind(), format!("{}: {}", e, path)))?;

    let root = root
        .canonicalize()
        .unwrap_or_else(|_| std::path::PathBuf::from("."));

    wd.strip_prefix(&root)
        .map(|x| x.to_path_buf())
        .map_err(|_| io::Error::new(io::ErrorKind::Other, "cannot move above root directory"))
}

// ------ List -----------------------------------------------------------------
fn ls_table_help() -> HelpMessage {
    HelpMessage {
        desc: "list out the headers of the table".into(),
        examples: vec![HelpExample {
            desc: "list headers in table",
            code: "open table.csv | ls",
        }],
        ..HelpMessage::new("ls")
    }
}

fn ls_table_intrinsic(mut blk: Block) -> Result<Step> {
    blk.assert_input(&Type::Tab)?;
    blk.assert_output(Type::Tab); // always outputs a table

    let blk_tag = blk.blk_tag().clone();
    blk.eval_o(move |input, cx| {
        Table::try_from(input)
            .and_then(|t| {
                t.row(0)
                    .ok_or_else(|| Error::empty_table("", &blk_tag))
                    .map(|r| once(o("header")).chain(r.cloned()).map(|x| vec![x]))
                    .map(|x| x.collect::<Vec<_>>())
            })
            .map(::table::Table::from)
            .map(Table::from)
            .and_then(|x| cx.done_o(x))
    })
}

fn ls_help() -> HelpMessage {
    HelpMessage {
        desc: "list out the filesystem contents in the current working dir".into(),
        params: vec![HelpParameter::Optional("path".into())],
        examples: vec![
            HelpExample {
                desc: "list the current working directory items",
                code: "ls",
            },
            HelpExample {
                desc: "list directory items in `path`",
                code: "ls path/to",
            },
        ],
        ..HelpMessage::new("ls")
    }
}

fn ls_intrinsic(mut blk: Block) -> Result<Step> {
    blk.assert_output(Type::Tab); // always outputs a table

    let blk_tag = blk.blk_tag().clone();
    let path = if blk.args_len() > 0 {
        Some(
            blk.next_arg()?
                .supplied(Type::Nil)?
                .returns(Type::Str)?
                .concrete()?,
        )
    } else {
        None
    };

    blk.eval_o(move |_, cx| {
        if let Some(path) = &path {
            let path: Str = path.resolve(|| Value::Nil, &cx)?.try_into()?;
            make_dir_table(cx.wd.join(path.as_str()), &blk_tag)
        } else {
            make_dir_table(cx.wd, &blk_tag)
        }
        .and_then(|x| cx.done_o(x))
    })
}

fn make_dir_table<P: AsRef<std::path::Path>>(dir: P, blk_tag: &Tag) -> Result<Table> {
    use std::iter::*;
    use Entry::*;

    let o = |s: &str| Obj(Str::new(s));

    let mut table = ::table::DataTable::from(vec![vec![
        o("name"),
        o("type"),
        o("size"),
        o("ext"),
        o("modified"),
    ]]);
    table.header = true;

    for entry in dir
        .as_ref()
        .read_dir()
        .map_err(|e| Error::io(blk_tag, e))?
        .filter_map(|x| x.ok())
    {
        let row = once(o(entry.file_name().to_str().unwrap_or("")));
        if let Ok(meta) = entry.metadata() {
            let row = row
                .chain(once(if meta.is_dir() {
                    o("dir")
                } else if meta.is_file() {
                    o("file")
                } else {
                    Nil
                }))
                .chain(once(Num(meta.len().into())))
                .chain(once(
                    entry
                        .path()
                        .extension()
                        .and_then(|x| x.to_str())
                        .map(o)
                        .unwrap_or(Nil),
                ))
                .chain(once(
                    meta.modified().map(fmt_systime).map(Obj).unwrap_or(Nil),
                ));

            table.add_row(row);
        } else {
            table.add_row(row);
        }
    }

    table.sort(0, |x, y| x.partial_cmp(y).unwrap());

    Ok(table.map_obj(Value::Str).into()) // convert to Table<Value>
}

fn fmt_systime(systime: std::time::SystemTime) -> Str {
    let fmt = &time::macros::format_description!("[year].[month].[day] [hour][minute]");
    let dt = time::OffsetDateTime::from(systime);
    dt.format(fmt).unwrap_or_default().into()
}

// ------ Open -----------------------------------------------------------------
fn open_help() -> HelpMessage {
    HelpMessage {
        desc: "open something
Table (default): parse file as a table
String: reads file as string"
            .into(),
        params: vec![HelpParameter::Required("file".into())],
        flags: vec![(
            "<type>",
            "open file as type. defaults to Table if not specified",
        )],
        examples: vec![
            HelpExample {
                desc: "open a csv as a table",
                code: "open file.csv",
            },
            HelpExample {
                desc: "open a file along a path",
                code: "open 'path/to a/file.csv'",
            },
            HelpExample {
                desc: "open a file as a string",
                code: "open --Str foo.txt",
            },
        ],
        ..HelpMessage::new("open")
    }
}

fn open_intrinsic(mut blk: Block) -> Result<Step> {
    let blktag = blk.blk_tag().clone();
    let arg = blk
        .next_arg()?
        .supplied(None)?
        .returns(Ty::Str)?
        .concrete()?;
    // TODO make this output inferred / default to Table?
    // AND make this to guessing of types based on file extension
    let as_ty = type_flag(&mut blk)?.unwrap_or(Ty::Tab);

    match as_ty {
        Ty::Tab => blk.eval_o(move |val, cx| {
            // TODO make this better at reading in tables:
            // 1. Recognise extension to choosing deserializing method?
            // 2. Use a flag to choose deserializing method?
            // 3. Support more than just comma for dsv types

            let p: Str = arg.resolve(|| val, &cx)?.try_into()?;
            let path = scrub_filepath(&p, &cx).map_err(|e| Error::io(&blktag, e))?;
            let table = match FSCACHE.get::<Table>(&path) {
                Some(table) => table,
                None => {
                    let s: Str = read_file(&path).map_err(|e| Error::io(&blktag, e))?.into();

                    let table = Table::from(
                        ::table::parse_dsv(',', &s).map_obj(|s| Value::Str(Str::new(s))),
                    );
                    FSCACHE.insert(&path, table.clone());
                    table
                }
            };

            cx.done_o(table)
        }),
        Ty::Str => blk.eval_o(move |val, cx| {
            let p: Str = arg.resolve(|| val, &cx)?.try_into()?;
            let path = scrub_filepath(&p, &cx).map_err(|e| Error::io(&blktag, e))?;
            let s = match FSCACHE.get::<Str>(&path) {
                Some(s) => s,
                None => {
                    let s: Str = read_file(&path).map_err(|e| Error::io(&blktag, e))?.into();

                    FSCACHE.insert(&path, s.clone());
                    s
                }
            };
            cx.done_o(s)
        }),
        x => Err(Error {
            help_msg: None,
            ..Error::wrong_op_input_type(&x, blk.op_tag())
        }),
    }
}

/// Read a file to a String, but not necessarily from UTF-8
fn read_file(path: impl AsRef<std::path::Path>) -> io::Result<String> {
    use ::encoding::{all::UTF_8, decode, DecoderTrap};

    decode(&std::fs::read(path)?, DecoderTrap::Strict, UTF_8)
        .0
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
}

// ------ Save -----------------------------------------------------------------
fn save_help() -> HelpMessage {
    HelpMessage {
        desc: "save the input to a file
table input is saved as comma separated values"
            .into(),
        params: vec![HelpParameter::Required("file".into())],
        examples: vec![
            HelpExample {
                desc: "save table as a csv",
                code: "open file1.csv | save file2.csv",
            },
            HelpExample {
                desc: "save text as a string",
                code: "\\ 'Hello, world!' | save hello-world.txt",
            },
        ],
        ..HelpMessage::new("save")
    }
}

fn save_intrinsic(mut blk: Block) -> Result<Step> {
    let ty = blk.in_ty().clone();
    blk.assert_output(ty.clone()); // output is the same as input
    if ty == Ty::TabRow {
        return Err(Error::wrong_op_input_type(&ty, blk.op_tag()));
    }

    let filepath = blk
        .next_arg()?
        .supplied(None)?
        .returns(Ty::Str)?
        .concrete()?;
    let blktag = blk.blk_tag().clone();
    blk.eval(ty, move |val, cx| {
        let p: Str = filepath.resolve(|| val.clone(), &cx)?.try_into()?;
        let p = cx.root.join(cx.wd).join(p.as_str());
        // check path doesn't go beyond root. can't use scrub_filepath as this uses
        // canonicalization for checking
        {
            use std::path::Component::*;
            let x = p.components().fold(0i32, |x, c| {
                x + match c {
                    RootDir => std::i32::MIN,
                    CurDir => 0,
                    ParentDir => -1,
                    _ => 1,
                }
            }); // there is always one for the file name
            if x <= 0 {
                Err(io::Error::new(
                    io::ErrorKind::Other,
                    "cannot move above root directory",
                ))
            } else {
                Ok(())
            }
        }
        .and_then(|_| mkdirs(&p).and_then(|_| std::fs::File::create(p)))
        .map(std::io::BufWriter::new)
        .and_then(|mut file| write_file(&mut file, val.clone()))
        .map_err(|e| Error::io(&blktag, e))?;
        cx.done(val)
    })
}

fn mkdirs<P: AsRef<std::path::Path>>(p: P) -> io::Result<()> {
    let p = p.as_ref();
    if let Some(p) = p.parent() {
        if !p.exists() {
            std::fs::create_dir_all(p)?;
        }
    }
    Ok(())
}

fn write_file<W: Write>(file: &mut W, value: Value) -> io::Result<()> {
    use ::numfmt::*;
    fn fmt_cell<WW: Write>(
        wtr: &mut WW,
        entry: &Entry<Value>,
        fmtr: &mut Formatter,
    ) -> io::Result<()> {
        match entry {
            Entry::Obj(Value::Nil) | Entry::Nil => Ok(()), // don't write anything
            e => {
                let s = print::fmt_cell(e, fmtr);
                // if s contains commas or new lines need to escape it.
                if s.contains(&[',', '"', '\r', '\n'] as &[_]) {
                    write!(wtr, "\"{}\"", s.escape_debug())
                } else {
                    write!(wtr, "{}", s)
                }
            }
        }
    }

    let fmtr = &mut Formatter::new();
    match value {
        Value::Tab(table) => {
            let mut add_newline = false;
            for row in table.rows() {
                if add_newline {
                    writeln!(file)?;
                }
                add_newline |= true;
                let mut add_comma = false;
                for entry in row {
                    if add_comma {
                        write!(file, ",")?;
                    }
                    add_comma |= true;
                    fmt_cell(file, entry, fmtr)?;
                }
            }
        }
        x => {
            let x = print::fmt_cell(&Entry::from(x), fmtr);
            write!(file, "{}", x)?;
        }
    }

    file.flush()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn write_file_testing() {
        let f = |v| {
            let mut wtr = Vec::new();
            write_file(&mut wtr, v).unwrap();
            String::from_utf8(wtr).unwrap()
        };
        let s = |s| Entry::Obj(Value::Str(Str::new(s)));
        let n = |n: f64| Entry::Num(n.into());

        let t = |v| Value::Tab(Table::from(::table::Table::from(v)));

        assert_eq!(&f(Value::Bool(true)), "true");
        assert_eq!(&f(Value::Num((3.14).into())), "3.14");
        assert_eq!(&f(Value::Str("Hello, world!".into())), "Hello, world!");
        assert_eq!(
            &f(t(vec![
                vec![n(1.5e6), n(2.5)],
                vec![s("foo"), Entry::Nil, s("foo\nbar")],
                vec![n(3.6e9), s("foo,bar"), s("foo \"zog\" bar")]
            ])),
            r#"1500000.0,2.5,
foo,,"foo\nbar"
3600000000.0,"foo,bar","foo \"zog\" bar""#
        );
    }
}
