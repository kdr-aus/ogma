//! Table expression system.
#![warn(missing_docs)]

use ::numfmt::Formatter;
use ::table::Entry;
use ::libs::{
    colored::*,
    divvy::Str
};
use std::{
    fmt,
    io::{self, Write},
    iter::*,
    path::Path,
    sync::Arc,
};

pub mod ast;
pub mod bat;
mod defs;
mod err;
mod hir;
mod impls;
mod parsing;
#[cfg(test)]
mod tests;
mod types;
mod var;

type HashMap<K, V> = fxhash::FxHashMap<K, V>;
type HashSet<T> = fxhash::FxHashSet<T>;
type Result<T> = std::result::Result<T, Error>;
type Mutex<T> = ::parking_lot::Mutex<T>;

pub use self::types::Value;
use self::types::{AsType, Table};
pub use ast::Location;
pub use defs::Definitions;
pub use parsing::{Expecting, ParseFail};

// ###### HELP #################################################################
/// Help messages work off the back off error messages such that:
/// ```shell
/// Help: `command`
/// --> help:0
///  | description
///  |
///  | Usage:
///  |  => command params
///  |
///  | Examples:
///  |  example-desc
///  |  => command example-code
/// ```
#[derive(Clone)]
pub struct HelpMessage {
    cmd: Str,
    desc: Str,
    params: Vec<HelpParameter>,
    no_space: bool,
    /// (flag-name, description)
    flags: Vec<(&'static str, &'static str)>,
    examples: Vec<HelpExample>,
}

impl HelpMessage {
    fn new<C: Into<Str>>(cmd: C) -> Self {
        Self {
            cmd: cmd.into(),
            desc: Str::default(),
            params: Vec::new(),
            no_space: false,
            flags: Vec::new(),
            examples: Vec::new(),
        }
    }
}

impl fmt::Display for HelpMessage {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", help_as_error(self))
    }
}

#[derive(Clone)]
enum HelpParameter {
    Required(Str),
    Optional(Str),
    Custom(Str),
    /// Used to break to a new line for the help usage message.
    Break,
}

impl HelpParameter {
    fn write(&self, wtr: &mut dyn fmt::Write) {
        match self {
            HelpParameter::Required(p) | HelpParameter::Custom(p) => write!(wtr, "{}", p),
            HelpParameter::Optional(p) => write!(wtr, "[{}]", p),
            HelpParameter::Break => panic!("`write` should not be called on HelpParameter::Break"),
        }
        .ok();
    }
}

#[derive(Clone)]
struct HelpExample {
    desc: &'static str,
    code: &'static str,
}

// ###### ERROR ################################################################
/// Processing error.
///
/// Errors are printed like so:
/// ```shell
/// Category: description
/// --> location:column-num
///  | source line { }
///  |        ^^^^ short description
/// --> help: help message
/// ```
#[derive(Debug, PartialEq)]
pub struct Error {
    cat: err::Category,
    desc: String,
    traces: Vec<ErrorTrace>,
    help_msg: Option<String>,
}

#[derive(Debug, PartialEq)]
struct ErrorTrace {
    loc: Location,
    source: String,
    desc: Option<String>,
    start: usize,
    len: usize,
}

fn help_as_error(msg: &HelpMessage) -> Error {
    use fmt::Write;

    let cmd = msg.cmd.as_str();
    let mut source = format!("{}\n\nUsage:\n => {}", msg.desc, cmd);

    for param in &msg.params {
        let brk = matches!(param, HelpParameter::Break);
        if brk {
            write!(source, "\n => {}", cmd).ok();
        }
        if !msg.no_space {
            source.push(' ');
        }
        if !brk {
            param.write(&mut source);
        }
    }

    if !msg.flags.is_empty() {
        source.push_str("\n\nFlags:");
        for (name, desc) in &msg.flags {
            source.push_str("\n --");
            source.push_str(name);
            source.push_str(": ");
            source.push_str(desc);
        }
    }

    if !msg.examples.is_empty() {
        source.push_str("\n\nExamples:");
        for example in &msg.examples {
            write!(source, "\n {}\n => {}\n", example.desc, example.code).ok();
        }
    }

    Error {
        cat: crate::err::Category::Help,
        desc: format!("`{}`", cmd),
        help_msg: None,
        traces: vec![ErrorTrace {
            source,
            ..Default::default()
        }],
    }
}

// ###### PARSE ################################################################
/// Successful parse result.
pub enum ParseSuccess {
    /// Parsed as a `def`inition.
    Impl(ast::DefinitionImpl),
    /// Parsed as a type definition (`def-ty`).
    Ty(ast::DefinitionType),
    /// Parsed as an expression.
    Expr(ast::Expression),
}

/// Parse the `input` as a valid `ogma` expression or definition.
///
/// Uses `Location::Shell`.
pub fn parse(input: &str, defs: &Definitions) -> std::result::Result<ParseSuccess, ParseFail> {
    let loc = Location::Shell;
    if input.starts_with("def ") {
        parsing::definition_impl(input, loc, defs).map(ParseSuccess::Impl)
    } else if input.starts_with("def-ty ") {
        parsing::definition_type(input, loc).map(ParseSuccess::Ty)
    } else {
        parsing::expression(input, loc, defs).map(ParseSuccess::Expr)
    }
}

// ###### PROCESS ##############################################################
/// Parse and evaluate an `expr`, returning the value if successful.
///
/// `root`: The root directory that the ogma instance is evaluating in.
/// `wd`: The working directory that the expression is evaluating in.
///
/// These two paths are important since commands such as `open` and `ls` are relative.
/// There are also security concerns with accessing items _above_ the `root` path, so this is
/// generally disallowed.
pub fn process_expression<I, S>(
    seed: I,
    expr: S,
    loc: Location,
    defs: &Definitions,
    root: &Path,
    wd: &Path,
) -> Result<Value>
where
    I: AsType + Into<Value> + 'static,
    S: Into<Arc<str>>,
{
    let expr = parsing::expression(expr, loc, defs).map_err(|e| e.0)?;
    hir::handle_help(&expr, defs)?;
    let vars = var::Locals::default();
    let evaluator = hir::construct_evaluator(I::as_type(), expr, defs, vars.clone())?;
    let cx = hir::Context {
        root,
        wd,
        env: var::Environment::new(vars),
    };
    let output = evaluator.eval(seed.into(), cx)?.0;

    Ok(output)
}

pub use defs::{process_definition, recognise_definition};

// ###### PRINTING #############################################################

const ROWS_LIM: usize = 30;
const COLS_LIM: usize = 7;

/// Print the [`Table`](::table::DataTable) as a text formatted table to the given [`Write`]r.
/// Colours the output. This is intended for terminal printing.
pub fn print_table(table: &Table, wtr: &mut dyn Write) -> io::Result<()> {
    use comfy_table::TableComponent::*;

    if table.is_empty() {
        return writeln!(wtr, "{}", "table is empty".bright_yellow());
    }

    let mut out = comfy_table::Table::new();

    let mut header_fmtr = Formatter::new();
    let mut cell_fmtr = Formatter::default();

    let mut rows = table.rows();

    let limit_col = table.cols_len() > COLS_LIM;
    let limit_row = table.rows_len() > ROWS_LIM;

    if table.header {
        if let Some(header) = rows.next() {
            let row = fmt_row(header, limit_col, table.cols_len(), &mut header_fmtr, true);
            out.set_header(row);
        }
    }

    let (take, skip) = if limit_row {
        (5, table.rows_len() - 11)
    } else {
        (table.rows_len(), 0)
    };

    let rows = rows.by_ref();

    for row in rows.take(take) {
        let row = fmt_row(row, limit_col, table.cols_len(), &mut cell_fmtr, false);
        out.add_row(row);
    }

    if limit_row {
        out.add_row(
            once(Str::from(format!(
                "{} rows elided",
                table.rows_len() - 10 - if table.header { 1 } else { 0 }
            )))
            .chain(repeat_with(|| Str::from("...")).take(if limit_col {
                6
            } else {
                table.cols_len() - 1
            })),
        );
        for row in rows.skip(skip) {
            let row = fmt_row(row, limit_col, table.cols_len(), &mut cell_fmtr, false);
            out.add_row(row);
        }
    }

    // style
    out.load_preset(comfy_table::presets::UTF8_FULL);
    out.remove_style(HorizontalLines);
    out.remove_style(MiddleIntersections);
    out.remove_style(LeftBorderIntersections);
    out.remove_style(RightBorderIntersections);

    writeln!(wtr, "{}", out)
}

/// Prints the processing error. Uses colour and assumes printing is to the terminal.
/// Use [`Error::print`] if this is not the case.
pub fn print_error(err: &Error, wtr: &mut dyn Write) -> io::Result<()> {
    err.print(true, wtr)
}

fn fmt_row<'a, I>(
    mut row: I,
    limit_col: bool,
    cols_len: usize,
    fmtr: &mut Formatter,
    header: bool,
) -> Vec<Str>
where
    I: Iterator<Item = &'a Entry<Value>>,
{
    let mut cols = Vec::with_capacity(COLS_LIM);

    let (take, skip) = if limit_col {
        (3, cols_len - 6)
    } else {
        (cols_len, 0)
    };

    let cells = row.by_ref();

    cols.extend(cells.take(take).map(|e| fmt_cell(e, fmtr)));

    if limit_col {
        cols.push(if header {
            format!("{} cols elided", cols_len - 6).into()
        } else {
            "...".into()
        });
        cols.extend(cells.skip(skip).map(|e| fmt_cell(e, fmtr)));
    }

    cols
}

fn fmt_cell(entry: &Entry<Value>, numfmtr: &mut Formatter) -> Str {
    use Entry::*;
    use Value as V;
    match entry {
        Nil | Obj(V::Nil) => Str::from("-"),
        Num(n) | Obj(V::Num(n)) => Str::new(numfmtr.fmt(n.as_f64())),
        Obj(V::Bool(b)) => b.to_string().into(),
        Obj(V::Str(s)) => s.clone(),
        Obj(V::Tab(t)) => format!("<table [{},{}]>", t.rows_len(), t.cols_len()).into(),
        Obj(V::TabRow(_)) => Str::from("<table row>"), // this should not be reachable.
        Obj(V::Ogma(x)) => print_ogma_data(x.clone()).into(),
    }
}

/// Serialises `OgmaData` into [`::kserd::Kserd`] and the formats it into a string.
pub fn print_ogma_data(data: types::OgmaData) -> String {
    use kserd::ToKserd;
    data.into_kserd().unwrap().as_str()
}
