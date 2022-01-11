use libs::colored::*;
use ::numfmt::Formatter;
use crate::prelude::*;
use std::{iter::*, io::{self, Write}};

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

pub fn fmt_cell(entry: &Entry<Value>, numfmtr: &mut Formatter) -> Str {
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

