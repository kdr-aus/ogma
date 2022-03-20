//! This handles definitions (fns, structs, enums)
use crate::prelude::*;
use ::libs::divvy::Str;
use ast::*;
use err::Trace;
use lang::help::*;

/// The working set of `ogma` definitions.
///
/// [`Definitions`] contains the implementations (commands) and the types in the current `ogma`
/// session.
#[derive(Clone)]
pub struct Definitions {
    impls: lang::impls::Implementations,
    types: types::Types,
}

impl Default for Definitions {
    fn default() -> Self {
        Self::new()
    }
}

impl Definitions {
    /// Create the new, base set of definitions.
    pub fn new() -> Self {
        // take the default impls first, these do not have the derive impls
        let mut impls = Default::default();
        // build the std types off this
        let types = types::Types::init(&mut impls);

        let mut definitions = Self { impls, types };

        let defs = &mut definitions;

        use lang::impls::OperationCategory;

        // progressively add in derived impls (such as >,<,!= etc)
        add_derived_impl(
            defs,
            "def = (rhs) { eq $rhs }",
            OperationCategory::Cmp,
            "test if input is not equal to rhs",
            vec![HelpExample {
                desc: "test if 1 is equal to 0",
                code: "in 1 | = 0",
            }],
        );
        add_derived_impl(
            defs,
            "def != (rhs) { eq $rhs | not }",
            OperationCategory::Cmp,
            "test if input is not equal to rhs",
            vec![HelpExample {
                desc: "test if 1 is equal to 0",
                code: "in 1 | != 0",
            }],
        );
        add_derived_impl(
            defs,
            "def > (rhs) { cmp $rhs | = Ord::Gt }",
            OperationCategory::Cmp,
            "test if input is greater than rhs",
            vec![
                HelpExample {
                    desc: "test if 1 is greater than 0",
                    code: "\\ 1 | > 0",
                },
                HelpExample {
                    desc: "use to filter ls",
                    code: "ls | filter > size 1e6",
                },
            ],
        );
        add_derived_impl(
            defs,
            "def >= (rhs) { cmp $rhs | or { = Ord::Gt } { = Ord::Eq } }",
            OperationCategory::Cmp,
            "test if input is greater than or equal to rhs",
            vec![
                HelpExample {
                    desc: "test if 1 againt 0",
                    code: "\\ 1 | >= 0",
                },
                HelpExample {
                    desc: "use to filter ls",
                    code: "ls | filter >= size 1e6",
                },
            ],
        );
        add_derived_impl(
            defs,
            "def < (rhs) { cmp $rhs | = Ord::Lt }",
            OperationCategory::Cmp,
            "test if input is less than rhs",
            vec![
                HelpExample {
                    desc: "test if 1 is less than 0",
                    code: "\\ 1 | < 0",
                },
                HelpExample {
                    desc: "use to filter ls",
                    code: "ls | filter < size 1e6",
                },
            ],
        );
        add_derived_impl(
            defs,
            "def <= (rhs) { cmp $rhs | or { = Ord::Lt } { = Ord::Eq } }",
            OperationCategory::Cmp,
            "test if input is less than or equal to rhs",
            vec![
                HelpExample {
                    desc: "test if 1 againt 0",
                    code: "\\ 1 | <= 0",
                },
                HelpExample {
                    desc: "use to filter ls",
                    code: "ls | filter <= size 1e6",
                },
            ],
        );
        add_derived_impl(
            defs,
            "def last Table (expr:Expr) { nth {len | - 1} $expr }",
            OperationCategory::Pipeline,
            "apply the expression to the last row in a table",
            vec![HelpExample {
                desc: "fetch value in column in table",
                code: "last {get 'foo' --Str}",
            }],
        );
        add_derived_impl(
            defs,
            "def last Str () { nth {len | - 1} }",
            OperationCategory::Pipeline,
            "get the last character of a string",
            vec![HelpExample {
                desc: "get the last character",
                code: "\\ 'Hello' | last",
            }],
        );
        add_derived_impl(
            defs,
            "def abs Num () { if {< 0} {* -1} #i }",
            OperationCategory::Arithmetic,
            "take the absolute of a number",
            vec![],
        );
        add_derived_impl(
            defs,
            "def mod Num (denom) { - {/ $denom | floor | * $denom} }",
            OperationCategory::Arithmetic,
            "return the modulus of a number",
            vec![HelpExample {
                desc: "return remainder of 35 divided by 3",
                code: "\\ 35 | mod 3",
            }],
        );
        add_derived_impl(
            defs,
            "def empty () { len | = 0 }",
            OperationCategory::Pipeline,
            "returns if a table or string is empty",
            vec![HelpExample {
                desc: "returns that string is empty",
                code: "in '' | empty",
            }],
        );
        add_derived_impl(
            defs,
            "def skip-hdrs Table (num:Num) { ren-with --Str $num {\\#i} | skip $num }",
            OperationCategory::Morphism,
            "skip the number of headers, setting the table headers to the top most row
the row is assumed to be populated with strings, if not an error occurs",
            vec![],
        );

        definitions
    }

    /// Add definitions by reading a file.
    pub fn add_from_file<P: AsRef<std::path::Path>>(&mut self, file: P) -> Result<usize> {
        let file = file.as_ref();
        let s = std::fs::read_to_string(file).map_err(|e| Error::io(&ast::Tag::default(), e))?;
        self.add_from_str(&s, file)
    }

    /// Add definitions from a string.
    pub fn add_from_str(&mut self, s: &str, file: &std::path::Path) -> Result<usize> {
        let items = rt::bat::parse_str(s);
        let file = Arc::from(file);
        // parse and add each def
        let mut count = 0;
        for mut item in items.items {
            let help = item.comment.take();
            process_definition(
                item.code(),
                Location::File(Arc::clone(&file), item.line as usize),
                help,
                self,
            )?;
            count += 1;
        }

        Ok(count)
    }

    /// Clears user-defined commands. If `only_files` is `true`, shell defined definitions are left
    /// in.
    pub fn clear(&mut self, only_files: bool) {
        self.impls.clear(only_files);
        self.types.clear(only_files);
    }

    /// Provide access to the defined implementations.
    pub fn impls(&self) -> &Implementations {
        &self.impls
    }

    /// Provide access to the defined types.
    pub fn types(&self) -> &types::Types {
        &self.types
    }
}

fn add_derived_impl(
    defs: &mut Definitions,
    s: &str,
    opcat: lang::impls::OperationCategory,
    desc: &str,
    eg: Vec<HelpExample>,
) {
    let im = lang::syntax::parse::definition_impl(s, Location::Ogma, defs).unwrap();
    let in_ty = if let Some(in_ty) = &im.in_ty {
        Some(defs.types.get_using_tag(in_ty).unwrap().clone())
    } else {
        None
    };
    let mut help = lang::impls::usr_impl_help(&im);
    let d = help.desc.to_mut();
    d.push('\n');
    d.push_str(desc);
    help.examples = eg;
    defs.impls.insert_impl(in_ty, im, opcat, help).unwrap();
}

/// Recognise a string which defines an implementation or type.
///
/// ```rust
/// # use ogma::lang::recognise_definition;
/// assert!(recognise_definition("def foo-bar { }"));
/// assert!(recognise_definition("def-ty Point { x:Num y:Num }"));
/// assert!(!recognise_definition("foo-bar zog"));
/// ```
pub fn recognise_definition(s: &str) -> bool {
    s.starts_with("def ") || s.starts_with("def-ty ")
}

type DefResult<'a> = Result<(Value, Option<&'a str>)>;

/// Process an expression whichs defines a _definition_.
///
/// If successful the definition will be added to `defs`.
///
/// # Return Value
/// Sometimes a definition will process and return a [`Value`], but will have trailing `ogma` code
/// that potentially might compile to use the the returned [`Value`]. This is why the successful
/// return value is `Ok((Value, Option<&str>))`. The optional returned slice indicates that this
/// slice should be sent through the `ogma` processor again, with the returned [`Value`] as the
/// input. **It does not indicate whether it will succeed or not**.
pub fn process_definition<'a>(
    def: &'a str,
    loc: Location,
    help: Option<String>,
    defs: &mut Definitions,
) -> DefResult<'a> {
    if def.starts_with("def ") {
        process_impl(def, loc, help, defs)
    } else if def.starts_with("def-ty ") {
        process_ty(def, loc, help, defs)
    } else {
        Err(Error {
            cat: err::Category::Parsing,
            desc: "a definition must start with `def` or `def-ty`".into(),
            traces: vec![Trace {
                loc,
                source: def.to_string(),
                len: def.len(),
                ..Default::default()
            }],
            help_msg: Some("try using `def --help` or `def-ty --help` for more information".into()),
            ..Error::default()
        })
    }
}

fn process_impl<'a>(
    s: &'a str,
    loc: Location,
    help: Option<String>,
    defs: &mut Definitions,
) -> DefResult<'a> {
    if s.contains("--help") {
        let help = HelpMessage {
            desc: "define a command that encapsulates an expression
def has specialised syntax which takes variable params: ( )"
                .into(),
            params: vec![
                HelpParameter::Required("name".into()),
                HelpParameter::Optional("Ty".into()),
                HelpParameter::Custom(
                    "([param1[:Ty|Expr]] [param2[:Ty|Expr]] ...) { expr }".into(),
                ),
            ],
            flags: vec![
                ("list", "list the definitions as a table"),
                (
                    "load",
                    "load persistent definitions from files in daedalus folder",
                ),
                ("clear", "clear all user defined definitions"),
            ],
            examples: vec![
                HelpExample {
                    desc: "define a command that returns the number 5",
                    code: "def num5 () { \\ 5 }",
                },
                HelpExample {
                    desc: "list directory items that match a type",
                    code: "def list (ty) { ls | filter = type $ty }",
                },
                HelpExample {
                    desc: "use types to better define use",
                    code: "def sum Table (seed:Num value:Expr) { fold $seed + $acc $value }",
                },
            ],
            ..HelpMessage::new("def")
        };
        Err(err::help_as_error(&help))
    } else if s.contains(" --list") {
        let post = s.split_once(" | ").map(|x| x.1);
        Ok((Value::Tab(construct_def_table(defs)), post))
    } else if s.contains(" --clear") {
        defs.clear(false);
        Ok((Value::Nil, None))
    } else {
        let def = lang::syntax::parse::definition_impl(s, loc, defs).map_err(|e| e.0)?;

        assert_all_ops_defined(&def, defs.impls())?;

        let in_ty = if let Some(in_ty) = &def.in_ty {
            Some(defs.types.get_using_tag(in_ty)?.clone())
        } else {
            None
        };

        let mut helpmsg = lang::impls::usr_impl_help(&def);
        if let Some(help) = help {
            helpmsg.desc = format!("{}\n\n{}", helpmsg.desc, help).into();
        }

        defs.impls.insert_impl(
            in_ty,
            def,
            lang::impls::OperationCategory::UserDefined,
            helpmsg,
        )?;
        Ok((Value::Nil, None))
    }
}

fn process_ty<'a>(
    s: &'a str,
    loc: Location,
    help: Option<String>,
    defs: &mut Definitions,
) -> DefResult<'a> {
    if s.contains("--help") {
        todo!("need to create a def-ty help message");
    //         let help = HelpMessage {
    //             desc: "define a command that encapsulates an expression
    // def has specialised syntax which takes variable params: ( )"
    //                 .into(),
    //             params: vec![
    //                 HelpParameter::Required("name".into()),
    //                 HelpParameter::Custom("([param1] [param2] [..args]) { expr }".into()),
    //             ],
    //             flags: vec![
    //                 ("list", "list the definitions as a table"),
    //                 (
    //                     "load",
    //                     "load persistent definitions from files in daedalus folder",
    //                 ),
    //                 ("clear", "clear all user defined definitions"),
    //             ],
    //             examples: vec![
    //                 HelpExample {
    //                     desc: "define a command that returns the number 5",
    //                     code: "def num5 () { in 5 }",
    //                 },
    //                 HelpExample {
    //                     desc: "list directory items that match a type",
    //                     code: "def list (ty) { ls | filter = type $ty }",
    //                 },
    //                 HelpExample {
    //                     desc: "pass through remaining arguments",
    //                     code: "def a-name (first ..remaining) { foo $first $remaining }",
    //                 },
    //             ],
    //         };
    //         Err(help_as_error("def", &help))
    } else if s.contains(" --list") {
        todo!("need to create a listing of types")
    //         Ok(Value::Tab(construct_def_table(defs)))
    } else if s.contains(" --clear") {
        todo!("need to handle clearing of types")
    //         defs.clear(false);
    //         Ok(Value::Nil)
    } else {
        defs.types
            .insert(s, loc, help, &mut defs.impls)
            .map(|_| (Value::Nil, None))
    }
}

fn assert_all_ops_defined(def: &ast::DefinitionImpl, defs: &Implementations) -> Result<()> {
    let name = &def.name;

    let mut check = vec![def.expr.clone()];
    while let Some(expr) = check.pop() {
        for block in &expr.blocks {
            let op = block.op();

            if !defs.contains_op(op.str()) {
                return Err(Error::op_not_found(&op, &*op == name));
            }
            check.extend(block.terms().iter().filter_map(|term| match term {
                ast::Term::Arg(ast::Argument::Expr(expr)) => Some(expr.clone()),
                _ => None,
            }));
        }
    }
    Ok(())
}

/// Construct a table comprising of the various definitions in `defs`.
pub fn construct_def_table(defs: &Definitions) -> Table {
    use ::table::Entry::*;
    fn location(im: &Implementation) -> Str {
        match im.location() {
            Location::File(f, _) => f.display().to_string().into(),
            x => x.to_string().into(),
        }
    }

    fn line(im: &Implementation) -> Entry<Str> {
        match &im.location() {
            Location::File(_, l) => Num((*l).into()),
            _ => Nil,
        }
    }

    fn code(im: &Implementation) -> Entry<Str> {
        // we remove the `def ` at the start of a src line. This is an implementation detail which
        // could change if `def` keyword ever changes.
        match im {
            Implementation::Intrinsic { .. } => Nil,
            Implementation::Definition(d) => Obj(Str::new(&d.src[4..])),
        }
    }

    let mut table = ::table::DataTable::new();
    table.add_row(
        ["name", "category", "input", "location", "line", "code"]
            .iter()
            .map(|x| Obj(Str::from(*x))),
    );

    let mut rows = defs
        .impls
        .iter()
        .map(|(name, ty, im)| {
            let cat = Obj(defs.impls.get_cat(name).unwrap().to_string().into());
            let name = Obj(name.clone());
            let inty = ty.map(|t| Str::from(t.to_string())).map(Obj).unwrap_or(Nil);
            let loc = Obj(location(im));
            let line = line(im);
            let code = code(im);
            vec![name, cat, inty, loc, line, code]
        })
        .collect::<Vec<_>>();

    // we know we can unwrap because all names are strings which implement total ordering
    rows.sort_by(|x, y| {
        use std::cmp::Ordering::*;
        match (&x[2], &y[2]) {
            (Obj(x), Obj(y)) => x.cmp(y),
            (Nil, _) => Less,
            (_, Nil) => Greater,
            _ => Equal,
        }
    }); // sort by input column
    rows.sort_by(|x, y| x[0].partial_cmp(&y[0]).unwrap()); // sort by name column

    table.add_rows(rows.into_iter().map(|x| x.into_iter()));

    table.map_obj(Value::Str).into()
}
