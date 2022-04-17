use super::*;
use std::{cell::RefCell, cmp, collections::BTreeMap, mem, rc::Rc};

pub fn add_intrinsics(impls: &mut Implementations) {
    add! { impls,
    (append, Morphism)
    ("append-row", append_row, Morphism)
    (dedup, Morphism)
    (filter, Morphism)
    (fold, Morphism)
    ("fold-while", fold_while, Morphism)
    (grp, Morphism)
    ("grp-by", grpby, Morphism)
    (map, Morphism)
    (pick, Morphism)
    (ren, Morphism)
    ("ren-with", ren_with, Morphism)
    (rev, Morphism)
    (skip, Morphism)
    (sort, Morphism)
    ("sort-by", sortby, Morphism)
    (take, Morphism)
    };
}

// ------ Append ---------------------------------------------------------------
fn append_help() -> HelpMessage {
    HelpMessage{
        desc: "add new columns onto a table using one or more expressions
each expression adds a new column, populated by row with the result of the expression
tags can be optionally specified to name the columns".into(),
        params: vec![HelpParameter::Required("args..".into())],
        flags: vec![("<col-names>", "name each column in order of expression")],
        examples: vec![
            HelpExample {
                desc: "flag if a filesystem item is a file",
                code: "ls | append { get type --Str | eq file } --is-file",
            },
            HelpExample {
                desc: "add more than one column",
                code: "ls | append { get size | if { > 1e9 } 'big file' '' } { get ext --Str | eq csv }",
            },
        ],
        ..HelpMessage::new("append")
    }
}

fn append_intrinsic(mut blk: Block) -> Result<Step> {
    if blk.in_ty() != &Ty::Tab {
        return Err(Error::wrong_op_input_type(blk.in_ty(), blk.op_tag()));
    }

    let len = blk.args_len();
    if len == 0 {
        return Err(Error::insufficient_args(blk.blk_tag(), 0, None));
    }

    let mut cols = Vec::with_capacity(len);
    let mut auto = 1;
    for _ in 0..len {
        let arg = blk.next_arg()?.supplied(Ty::TabRow)?.concrete()?;
        let col = blk
            .get_flag(None)
            .map(|x| Str::new(x.str()))
            .unwrap_or_else(|| (format!("_append{}", auto).into(), auto += 1).0);
        cols.push((arg, col));
    }

    blk.eval_o(move |table, cx| {
        append_table(table.try_into()?, &cx, &cols).and_then(|x| cx.done_o(x))
    })
}

fn append_table(mut table: Table, cx: &Context, with: &[(eng::Argument, Str)]) -> Result<Table> {
    let rows = table.rows_len();
    // seed column buffers
    let mut to_append = with
        .iter()
        .map(|(_, n)| {
            let mut v = Vec::new();
            v.resize_with(rows, Default::default);
            if let Some(x) = v.get_mut(0) {
                *x = Entry::Obj(Value::Str(n.clone()));
            }
            v
        })
        .collect::<Vec<_>>();

    // calculate appending values
    // parallelised over the expressions _and_ the rows
    let err = crate::Mutex::new(None);
    to_append
        .par_iter_mut()
        .enumerate()
        .for_each(|(withidx, av)| {
            let predicate = with[withidx].0.resolver_sync(cx);
            if let Err(e) = par_over_tablerows(av, &table, cx, |a, _, trow| {
                *a = predicate(trow.into())?.into();
                Ok(())
            }) {
                *err.lock() = Some(e);
            }
        });

    // return any error found
    if let Some(e) = err.into_inner() {
        return Err(e);
    }

    // append to the column, if ref shared, clone with known expansion of cols
    let to_append = to_append.into_iter().map(|x| x.into_iter());
    if let Some(t) = table.get_mut() {
        t.add_cols(to_append);
    } else {
        let mut t = table.clone_with_col_capacity(table.cols_len() + with.len());
        t.add_cols(to_append);
        table = t.into();
    }

    Ok(table)
}

// ------ Append-Row -----------------------------------------------------------
fn append_row_help() -> HelpMessage {
    variadic_help(
        "append-row",
        "append a row to the table
the row is populated with the expression results",
        vec![HelpExample {
            desc: "append the row 1 2 3 to the table",
            code: "append-row 1 2 3",
        }],
    )
}

fn append_row_intrinsic(mut blk: Block) -> Result<Step> {
    if blk.in_ty() != &Ty::Tab {
        return Err(Error::wrong_op_input_type(blk.in_ty(), blk.op_tag()));
    }
    blk.assert_output(Ty::Tab); // table -> table

    let len = blk.args_len();
    let mut cols = Vec::with_capacity(len);
    while blk.args_len() > 0 {
        cols.push(blk.next_arg()?.supplied(None)?.concrete()?);
    }

    blk.eval_o(move |table, cx| {
        let mut x = Vec::with_capacity(cols.len());
        for c in &cols {
            x.push(c.resolve(|| table.clone(), &cx)?);
        }

        let mut table: Table = table.try_into()?;
        let t = table.make_mut();
        t.add_row(x.into_iter());
        let mut i = 1;
        if let Some(hdr) = t.row_mut(0) {
            for e in hdr {
                if e.is_nil() {
                    *e = Value::Str(format!("_append{}", i).into()).into();
                    i += 1;
                }
            }
        }
        cx.done_o(table)
    })
}

// ------ Dedup ----------------------------------------------------------------
fn dedup_help() -> HelpMessage {
    HelpMessage {
        desc: "deduplicate items
for Tables consectutive repeated rows are removed if the cells in
specified columns match. if no columns are specified the whole row must match.
if the table is sorted, this removes all duplicates.
for Strs duplicate characters are removed."
            .into(),
        params: vec![HelpParameter::Required("col-name..".into())],
        examples: vec![
            HelpExample {
                desc: "remove all duplicate entries in the 'Product' heading",
                code: "sort Product | dedup Product",
            },
            HelpExample {
                desc: "remove duplicates that match the entire row",
                code: "ls foo | + ls bar | sort name | dedup",
            },
        ],
        ..HelpMessage::new("dedup")
    }
}

fn dedup_intrinsic(blk: Block) -> Result<Step> {
    match blk.in_ty() {
        Ty::Str => dedup_str(blk),
        Ty::Tab => dedup_table(blk),
        x => Err(Error::wrong_op_input_type(x, blk.op_tag())),
    }
}

/// Assumes already check that input is Table.
fn dedup_table(mut blk: Block) -> Result<Step> {
    blk.assert_output(Ty::Tab); // table -> table
    let colnames = match blk.args_len() {
        0 => None,
        _ => Some(ColNameArgs::build(&mut blk)?),
    };
    blk.eval_o(move |table, cx| {
        let table: Table = table.try_into()?;
        let cols: Vec<usize> = match &colnames {
            Some(c) => c
                .resolve_indices(&table, &cx)?
                .into_iter()
                .map(|x| x.0)
                .collect(),
            None => (0..table.cols_len()).collect(),
        };
        // we need to own the vector for .dedup function
        let mut t = (&*table).clone().into_raw();
        t.dedup_by(|a, b| cols.iter().all(|&c| a[c] == b[c]));

        cx.done_o(Table::from(InnerTable::from(t)))
    })
}

/// Assumes already check that input is Str.
fn dedup_str(blk: Block) -> Result<Step> {
    blk.eval_o(move |string, cx| {
        let string: Str = string.try_into()?;

        let mut x = None;
        let s: Str = string
            .chars()
            .filter(|&c| match x {
                Some(x) if c == x => false,
                _ => {
                    x = Some(c);
                    true
                }
            })
            .collect::<String>()
            .into();

        cx.done_o(s)
    })
}

// ------ Filter ---------------------------------------------------------------
fn filter_help() -> HelpMessage {
    HelpMessage {
        desc: "filter incoming data using a predicate
filter can be used with a column header and a type flag
filtering columns is achievable with the --cols flag
filtering on a string supplies one character at a time"
            .into(),
        params: vec![
            HelpParameter::Optional("col-name".into()),
            HelpParameter::Required("<predicate>".into()),
        ],
        flags: vec![
            (
                "<type>",
                "only filter entries of type. defaults to Num if not specified",
            ),
            (
                "cols",
                "filter columns with predicate. predicate is String -> Bool",
            ),
        ],
        examples: vec![
            HelpExample {
                desc: "filter ls items greater than 5kB",
                code: "ls | filter size > 5e3",
            },
            HelpExample {
                desc: "filter ls by extension",
                code: "ls | filter ext --Str = md",
            },
            HelpExample {
                desc: "filter a table by two columns",
                code: "\\ table.csv | filter { and { get col-a | > 100 } { get col-b | < 10 } }",
            },
            HelpExample {
                desc: "filter table columns",
                code: "\\ table.csv | filter --cols or { = 'foo' } { = bar }",
            },
            HelpExample {
                desc: "filtering a string",
                code: "\\ 'Hello, world!' | filter != ' '",
            },
        ],
        ..HelpMessage::new("filter")
    }
}

fn filter_intrinsic(mut blk: Block) -> Result<Step> {
    match blk.in_ty() {
        Ty::Str => filter_string(blk),
        Ty::Tab => {
            blk.assert_output(Ty::Tab); // filtering Table -> Table

            let cols = blk.get_flag("cols").is_some();
            if cols {
                filter_table_columns(blk)
            } else {
                FilterTable::filter(blk)
            }
        }
        x => Err(Error::wrong_op_input_type(x, blk.op_tag())),
    }
}

struct FilterTable {
    expr_predicate: eng::Argument,
    col: Option<eng::Argument>,
    exp_ty: Type,
}

impl FilterTable {
    fn filter(mut blk: Block) -> Result<Step> {
        if blk.args_len() == 1 {
            let ft = Box::new(Self {
                expr_predicate: blk
                    .next_arg()?
                    .supplied(Ty::TabRow)?
                    .returns(Ty::Bool)?
                    .concrete()?,
                col: None,
                exp_ty: Ty::Nil,
            });

            blk.eval_o(move |table, cx| {
                let table: Table = table.try_into()?;
                let keep = ft.gen_keep_arr_with_table_row_input(&table, &cx)?;
                cx.done_o(FilterTable::retain_keep_rows(table, &keep))
            })
        } else {
            let col = blk
                .next_arg()?
                .supplied(Ty::Nil)?
                .returns(Ty::Str)?
                .concrete()?;

            let ty_flag = type_flag(&mut blk)?;

            let expr_predicate = blk.next_arg()?;
            let expr_predicate = match ty_flag {
                Some(ty) => expr_predicate.supplied(ty)?,
                None => expr_predicate,
            }
            .returns(Ty::Bool)?
            .concrete()?;

            let exp_ty = expr_predicate.in_ty().clone();

            let ft = Box::new(Self {
                expr_predicate,
                col: Some(col),
                exp_ty,
            });

            blk.eval_o(move |table, cx| {
                let table: Table = table.try_into()?;
                let keep = ft.gen_keep_arr_with_known_col(&table, &cx)?;
                cx.done_o(FilterTable::retain_keep_rows(table, &keep))
            })
        }
    }

    // filtering works by applying the predicate to each row and marking rows for
    // keeping if it passes the predicate.
    // Rows cannot be removed in the loop as the indexing will break,
    // and the predicate might use the indexing.
    // The specialised syntax which has the col-name out the front can leverage parallelisation
    // since the col-idx can be cached.
    // The normal filter can still utilise parallelisation by using for_each_init
    fn gen_keep_arr_with_table_row_input(&self, table: &Table, cx: &Context) -> Result<Vec<bool>> {
        let mut keep = vec![true; table.rows_len()];
        let predicate = self.expr_predicate.resolver_sync(cx);
        par_over_tablerows(&mut keep, table, cx, |k, _, trow| {
            predicate(trow.into())
                .and_then(TryInto::try_into)
                .map(|x| *k = x)
        })?;

        Ok(keep)
    }

    fn gen_keep_arr_with_known_col(&self, table: &Table, cx: &Context) -> Result<Vec<bool>> {
        let Self {
            col, exp_ty: ty, ..
        } = self;

        let col = col.as_ref().expect("only take this branch if have some");
        let tag = &col.tag;
        let name = &col.resolve(|| Value::Nil, cx).and_then(Str::try_from)?;
        let mut keep = vec![true; table.rows_len()];
        let predicate = self.expr_predicate.resolver_sync(cx);

        par_over_tablerows(&mut keep, table, cx, |k, _, trow| {
            let i = trow.idx;
            let e = trow.entry(name, tag)?;
            match TableRow::cnv_value(e, ty, i, name, tag) {
                Ok(e) => predicate(e).and_then(TryInto::try_into).map(|x| *k = x),
                Err(_) => (*k = false, Ok(())).1,
            }
        })?;

        Ok(keep)
    }

    fn retain_keep_rows(mut table: Table, keep: &[bool]) -> Table {
        // there are three table building branches:
        //   1. keep is all true; just return the table (fast since it is arc)
        //   2. `table` is owned. we use retain to remove the rows
        //   3. `table` is shared. in this case we rebuild a table to avoid cloning the backing data
        if keep.par_iter().all(|x| *x) {
            table
        } else if let Some(t) = table.get_mut() {
            t.retain_rows(|idx, _| keep[idx]);
            table
        } else {
            let keep_c = keep.par_iter().filter(|&&x| x).count();
            table::Table::from((0..table.rows_len()).filter(|&x| keep[x]).fold(
                Vec::with_capacity(keep_c),
                |mut acc, x| {
                    acc.push(table.row(x).unwrap().cloned().collect::<Vec<_>>());
                    acc
                },
            ))
            .into()
        }
    }
}

fn filter_table_columns(mut blk: Block) -> Result<Step> {
    let predicate = blk
        .next_arg()?
        .supplied(Ty::Str)?
        .returns(Ty::Bool)?
        .concrete()?;
    blk.eval_o(move |input, cx| {
        let mut table = Table::try_from(input)?;
        // work backwards on cols to remove
        for idx in (0..table.cols_len()).rev() {
            let hdr = table
                .col(idx)
                .and_then(|mut x| x.next())
                .map(|v| match v {
                    Entry::Obj(Value::Str(h)) => h.clone(),
                    _ => Str::default(),
                })
                .unwrap_or_default();
            let rm = predicate
                .resolve(|| hdr.into(), &cx)
                .and_then(bool::try_from)?;
            if !rm {
                // delay cloning (if have to) to last moment
                // should only clone _once_ (if have to)
                table.make_mut().remove_col_par(idx);
            }
        }

        cx.done_o(table)
    })
}

fn filter_string(mut blk: Block) -> Result<Step> {
    blk.assert_output(Type::Str);

    let predicate = blk
        .next_arg()?
        .supplied(Ty::Str)?
        .returns(Ty::Bool)?
        .concrete()?;

    blk.eval_o(move |input, cx| {
        let mut string = Str::try_from(input)?;
        let s = string.to_mut();
        let r = predicate.resolver_sync(&cx);
        let mut e = None;
        s.retain(|c| {
            r(Value::Str(c.into()))
                .and_then(bool::try_from)
                .unwrap_or_else(|err| {
                    e = Some(err);
                    true
                })
        });

        drop(r);

        match e {
            Some(e) => Err(e),
            None => cx.done_o(string),
        }
    })
}

// ------ Fold -----------------------------------------------------------------
fn fold_help() -> HelpMessage {
    HelpMessage {
        desc: "fold (reduce) table into single value
fold takes a seed value and an accumulator expression
the variable $row is available to query the table row"
            .into(),
        params: vec![
            HelpParameter::Required("seed".into()),
            HelpParameter::Required("accumulator".into()),
        ],
        examples: vec![
            HelpExample {
                desc: "sum numbers (0,10)",
                code: "range 0 11 | fold 0 { + $row.i }",
            },
            HelpExample {
                desc: "count number of files in directory",
                code: "ls | filter { get type --Str | = file } | fold 0 + 1",
            },
        ],
        ..HelpMessage::new("fold")
    }
}

fn fold_intrinsic(mut blk: Block) -> Result<Step> {
    match blk.in_ty() {
        Ty::Tab => {
            let seed = blk.next_arg()?.supplied(Type::Nil)?.concrete()?;
            let out_ty = seed.out_ty().clone();
            blk.assert_output(out_ty.clone());

            let row_var = blk.inject_manual_var_next_arg("row", Ty::TabRow)?;
            let acc_expr = blk
                .next_arg()?
                .supplied(out_ty.clone())? // accumulator supplies seed type
                .returns(out_ty.clone())? // and must return seed type!
                .concrete()?;

            blk.eval(out_ty, move |table, mut cx| {
                let table: Table = table.try_into()?;
                let colmap = types::TableRowColMap::default();
                let mut x = seed.resolve(|| Value::Nil, &cx)?;
                for idx in 1..table.rows_len() {
                    let trow = TableRow::new(table.clone(), colmap.clone(), idx);
                    row_var.set_data(&mut cx.env, trow.into());
                    x = acc_expr.resolve(|| x, &cx)?;
                }

                cx.done(x)
            })
        }
        x => Err(Error::wrong_op_input_type(x, blk.op_tag())),
    }
}

// ------ Fold-While -----------------------------------------------------------
fn fold_while_help() -> HelpMessage {
    HelpMessage {
        desc: "fold (reduce) table into single value while a predicate remains true
fold-while is similar to fold with an added predicate check on each iteration
the input into the predicate is the current accumulator value
fold-while will stop iterating once the predicate returns false"
            .into(),
        params: vec![
            HelpParameter::Required("seed".into()),
            HelpParameter::Required("predicate".into()),
            HelpParameter::Required("accumulator".into()),
        ],
        examples: vec![HelpExample {
            desc: "sum natural numbers until sum is greater than one million",
            code: "range 1 1e6 | fold-while 0 {<= 1e6} { + $row.i }",
        }],
        ..HelpMessage::new("fold-while")
    }
}

fn fold_while_intrinsic(mut blk: Block) -> Result<Step> {
    match blk.in_ty() {
        Ty::Tab => {
            let seed = blk.next_arg()?.supplied(Type::Nil)?.concrete()?;
            let out_ty = seed.out_ty().clone();
            blk.assert_output(out_ty.clone());

            // predicate and predicate row variable
            let row_var_predicate = blk.inject_manual_var_next_arg("row", Ty::TabRow)?;
            let acc_predicate = blk
                .next_arg()?
                .supplied(out_ty.clone())?
                .returns(Ty::Bool)?
                .concrete()?;
            // expr and expr row variable
            let row_var_expr = blk.inject_manual_var_next_arg("row", Ty::TabRow)?;
            let acc_expr = blk
                .next_arg()?
                .supplied(out_ty.clone())?
                .returns(out_ty.clone())?
                .concrete()?;

            blk.eval(out_ty, move |table, mut cx| {
                let table: Table = table.try_into()?;
                let colmap = types::TableRowColMap::default();
                let mut x = seed.resolve(|| Value::Nil, &cx)?;
                for idx in 1..table.rows_len() {
                    let trow = TableRow::new(table.clone(), colmap.clone(), idx);
                    row_var_predicate.set_data(&mut cx.env, trow.into());

                    let met = acc_predicate
                        .resolve(|| x.clone(), &cx)
                        .and_then(bool::try_from)?;
                    if !met {
                        break;
                    }

                    let trow = TableRow::new(table.clone(), colmap.clone(), idx);
                    row_var_expr.set_data(&mut cx.env, trow.into());
                    x = acc_expr.resolve(|| x, &cx)?;
                }

                cx.done(x)
            })
        }
        x => Err(Error::wrong_op_input_type(x, blk.op_tag())),
    }
}

// ------ Grouping -------------------------------------------------------------
fn grp_help() -> HelpMessage {
    HelpMessage {
        desc: "group a table by column headers
each value under the header is stringified and
concatenated together separated by a hyphen
to group on a derived value see `grp-by`"
            .into(),
        params: vec![HelpParameter::Required("col-name..".into())],
        examples: vec![
            HelpExample {
                desc: "group by file extension",
                code: "ls | grp ext",
            },
            HelpExample {
                desc: "group by file extension and modified",
                code: "ls | grp ext modified",
            },
        ],
        ..HelpMessage::new("grp")
    }
}

fn grp_intrinsic(mut blk: Block) -> Result<Step> {
    if blk.in_ty() != &Ty::Tab {
        return Err(Error::wrong_op_input_type(blk.in_ty(), blk.op_tag()));
    }
    blk.assert_output(Ty::Tab);

    let colnames = ColNameArgs::build(&mut blk)?;
    let blktag = blk.blk_tag().clone();
    blk.eval_o(move |table, cx| {
        let table: Table = table.try_into()?;
        if table.is_empty() {
            return Err(Error::eval(&blktag, "table is empty", None, None));
        }

        let cols = colnames.resolve_indices(&table, &cx)?;

        let mut map = BTreeMap::default();
        let row = |i| table.row(i).expect("should exist");
        let fmtr = &mut numfmt::Formatter::new();

        for rowidx in 1..table.rows_len() {
            let key = cols
                .iter()
                .map(|(c, _)| row(rowidx).nth(*c).expect("index inside table"))
                .fold(String::new(), |mut k, e| {
                    if !k.is_empty() {
                        k.push('-');
                    }
                    k.push_str(&print::fmt_cell(e, fmtr));
                    k
                });
            let t = map.entry(key).or_insert_with(|| {
                let mut t = InnerTable::new();
                t.add_row(row(0).cloned()); // hdr should exist
                t
            });
            t.add_row(row(rowidx).cloned());
        }

        cx.done_o(build_table_from_map(map, |s| Value::Str(s.into())))
    })
}

fn build_table_from_map<K, F>(map: BTreeMap<K, InnerTable>, mut key_f: F) -> Table
where
    F: FnMut(K) -> Value,
{
    let mut table = InnerTable::default();
    table.add_row(once("key").chain(once("value")).map(o));
    table.add_rows(
        map.into_iter()
            .map(|(k, v)| once(key_f(k)).chain(once(Value::Tab(Table::from(v))))),
    );
    table.into()
}

// grp-by
// whilst grp uses a string conversion as key, grp-by converts each row into a value using an
// expression, then groups the resulting values (and by proxy; the table)
// grouping the values uses `cmp` definitions
// the actual implementation is a bit more complex; we must create a pseudo-env to eval `cmp`
fn grpby_help() -> HelpMessage {
    HelpMessage {
        desc: "group table using an expression
the result of the expression must define a `cmp` implementation
this can be used to group user-defined types"
            .into(),
        params: vec![HelpParameter::Required("<expr>".into())],
        examples: vec![
            HelpExample {
                desc: "group ls by file extension",
                code: "ls | grp-by { get --Str ext }",
            },
            HelpExample {
                desc: "group using a user-defined type",
                code: "ls | grp-by { Point { get size } }",
            },
        ],
        ..HelpMessage::new("grp-by")
    }
}

fn grpby_intrinsic(mut blk: Block) -> Result<Step> {
    if blk.in_ty() != &Ty::Tab {
        return Err(Error::wrong_op_input_type(blk.in_ty(), blk.op_tag()));
    }
    blk.assert_output(Ty::Tab);

    // the expression which will be grouped on
    let key = blk.next_arg()?.supplied(Ty::TabRow)?.concrete()?;

    let cmpr = BinaryOp::cmp_cmd(key.out_ty(), "grp-by", &blk, &key)?;

    blk.eval_o::<_, Table>(move |table, cx| {
        let table = Table::try_from(table)?;
        let grping_values: SortIdx = resolve_trow_expr_par(&table, &key, &cx)?
            .into_iter()
            .enumerate()
            .collect();
        let t = grp_table(grping_values, &table, cmpr.pin_env(), &cx);
        cx.done_o(t)
    })
}

struct GrpByKey<'a, T> {
    value: Value,
    binop: Rc<RefCell<BinaryOpRef<'a, T>>>,
    cx: &'a Context<'a>,
}

impl<'a, T> PartialEq for GrpByKey<'a, T>
where
    T: Fn(Value) -> cmp::Ordering,
{
    fn eq(&self, rhs: &Self) -> bool {
        self.cmp(rhs).eq(&cmp::Ordering::Equal)
    }
}
impl<'a, T> Eq for GrpByKey<'a, T> where T: Fn(Value) -> cmp::Ordering {}
impl<'a, T> PartialOrd for GrpByKey<'a, T>
where
    T: Fn(Value) -> cmp::Ordering,
{
    fn partial_cmp(&self, rhs: &Self) -> Option<cmp::Ordering> {
        self.binop
            .borrow_mut()
            .eval(self.value.clone(), rhs.value.clone(), self.cx)
            .ok()
    }
}
impl<'a, T> Ord for GrpByKey<'a, T>
where
    T: Fn(Value) -> cmp::Ordering,
{
    fn cmp(&self, rhs: &Self) -> cmp::Ordering {
        self.partial_cmp(rhs).unwrap_or(cmp::Ordering::Equal)
    }
}

fn grp_table<T>(values: SortIdx, table: &Table, binop: BinaryOpRef<T>, cx: &Context) -> Table
where
    T: Fn(Value) -> cmp::Ordering,
{
    let newtable = || {
        let mut t = ::table::Table::default();
        t.add_row(table.row(0).expect("has hdr").cloned());
        t
    };
    let mut map = BTreeMap::new();

    let binop = Rc::new(RefCell::new(binop));
    for (idx, value) in values.into_iter().skip(1) {
        // skip header row
        let key = GrpByKey {
            value,
            cx,
            binop: Rc::clone(&binop),
        };
        let t = map.entry(key).or_insert_with(newtable);
        t.add_row(table.row(idx).expect("row inside table").cloned());
    }

    build_table_from_map(map, |k| k.value)
}

// ------ Map ------------------------------------------------------------------
fn map_help() -> HelpMessage {
    HelpMessage {
        desc: "replace entry in column with result of an expression
`map` provides the variable `$row` which is the TableRow
the input into the expression is the value of the entry"
            .into(),
        params: vec![
            HelpParameter::Required("col-name".into()),
            HelpParameter::Required("value".into()),
        ],
        flags: vec![
            ("<type>", "the type that entry has"),
            ("force", "ignore entry types"),
        ],
        examples: vec![
            HelpExample {
                desc: "scale 'size' by dividing by one million",
                code: "ls | map size / 1e6",
            },
            HelpExample {
                desc: "use a different column and result type",
                code: "ls | map type --Str { \\$row.size | + 100 }",
            },
        ],
        ..HelpMessage::new("map")
    }
}

fn map_intrinsic(blk: Block) -> Result<Step> {
    match blk.in_ty() {
        Ty::Tab => MapTable::map(blk),
        x => Err(Error::wrong_op_input_type(x, blk.op_tag())),
    }
}

struct MapTable {
    /// Expecting TableRow.
    transformation: eng::Argument,
    colarg: eng::Argument,
    force: bool,
    row_var: eng::Variable,
}

impl MapTable {
    fn map(mut blk: Block) -> Result<Step> {
        blk.assert_output(Ty::Tab);

        let colarg = blk
            .next_arg()?
            .supplied(Ty::Nil)?
            .returns(Ty::Str)?
            .concrete()?;
        let force_flag = blk.get_flag("force").is_some();
        let ty_flag = (!force_flag)
            .then(|| type_flag(&mut blk))
            .transpose()?
            .flatten();

        let row_var = blk.inject_manual_var_next_arg("row", Ty::TabRow)?;

        let transformation = blk.next_arg()?;
        let transformation = match (force_flag, ty_flag) {
            (true, _) => transformation.supplied(Ty::Nil)?,
            (false, Some(tyflag)) => transformation.supplied(tyflag)?,
            _ => transformation,
        }
        .concrete()?;

        let mp = Box::new(Self {
            transformation,
            colarg,
            force: force_flag,
            row_var,
        });

        blk.eval_o::<_, Table>(move |table, cx| {
            mp.doit(table.try_into()?, &cx).and_then(|x| cx.done_o(x))
        })
    }

    fn doit(&self, mut table: Table, cx: &Context) -> Result<Table> {
        let colname: Str = self.colarg.resolve(|| Value::Nil, cx)?.try_into()?;
        let ctag = &self.colarg.tag;
        let colidx = TableRow::col_idx(&table, &colname, ctag)?;

        let mut replace_with: Vec<Value> =
            repeat_with(|| Value::Nil).take(table.rows_len()).collect();
        let tf = &self.transformation;
        let var = &self.row_var;
        let force = self.force;
        let in_ty = tf.in_ty();

        par_over_tablerows(&mut replace_with, &table, cx, |v, cx, trow| {
            let trowidx = trow.idx;
            var.set_data(&mut cx.env, trow.into());
            let outv = match force {
                true => tf.resolve(|| Value::Nil, cx),
                false => {
                    let e = TableRow::entry_at(&table, trowidx, colidx);
                    let e = TableRow::cnv_value(e, in_ty, trowidx, &colname, ctag)?;
                    tf.resolve(|| e, cx)
                }
            };
            *v = outv?;
            Ok(())
        })?;

        table
            .make_mut()
            .col_mut(colidx)
            .expect("col should exist")
            .zip(replace_with.into_iter())
            .skip(1) // for header
            .for_each(|(e1, e2)| *e1 = e2.into());

        Ok(table)
    }
}

// ------ Pick -----------------------------------------------------------------
fn pick_help() -> HelpMessage {
    HelpMessage {
        desc: "pick out columns to keep in a table, in order".into(),
        params: vec![HelpParameter::Required("col-name..".into())],
        flags: vec![
            (
                "add",
                "add a blank column if it does not exist in the table",
            ),
            ("trail", "append any remaining columns in order"),
        ],
        examples: vec![HelpExample {
            desc: "choose the size, name, and type columns",
            code: "ls | pick name size type",
        }],
        ..HelpMessage::new("pick")
    }
}

fn pick_intrinsic(mut blk: Block) -> Result<Step> {
    blk.assert_output(Type::Tab); // always return a table

    match blk.in_ty() {
        Ty::Tab => pick_table_columns(blk),
        x => Err(Error::wrong_op_input_type(x, blk.op_tag())),
    }
}

fn pick_table_columns(mut blk: Block) -> Result<Step> {
    let addflag = blk.get_flag("add").is_some();
    let trailflag = blk.get_flag("trail").is_some();
    //
    let colnames = ColNameArgs::build(&mut blk)?;
    blk.eval_o::<_, Table>(move |input, cx| {
        let table = Table::try_from(input)?;
        let mut colidxs = if addflag {
            colnames.resolve_indices_forgiven(&table, &cx)?
        } else {
            colnames
                .resolve_indices(&table, &cx)?
                .into_iter()
                .map(|(a, b)| (Some(a), b))
                .collect()
        };

        if trailflag {
            // add columns that weren't touched to end, in order.
            let indices: HashSet<_> = colidxs.iter().filter_map(|x| x.0).collect();
            let toadd = (0..table.cols_len()).filter(|i| !indices.contains(i));
            colidxs.extend(toadd.map(|i| (Some(i), "".into())));
        }

        // rebuild table in parallel fashion
        let mut v = repeat_with(|| Vec::with_capacity(colidxs.len()))
            .take(table.rows_len())
            .collect::<Vec<_>>();
        v.par_iter_mut().enumerate().for_each(|(row, v)| {
            let row = colidxs.iter().map(|i| match i {
                (Some(i), _) => table.row(row).and_then(|mut x| x.nth(*i)).unwrap().clone(),
                (None, n) if row == 0 => Value::Str(n.clone()).into(), // header
                (None, _) => Entry::Nil,
            });
            v.extend(row);
        });

        cx.done_o(::table::Table::from(v).into())
    })
}

// ------ Ren ------------------------------------------------------------------
fn ren_help() -> HelpMessage {
    HelpMessage {
        desc: "rename column headers
each binding takes the form `<col-ref> <name>`
`<col-ref>` can be a string or a column index number"
            .into(),
        params: vec![
            HelpParameter::Optional("<col-ref-1> <name-1>".into()),
            HelpParameter::Optional("<col-ref-2> <name-2>".into()),
            HelpParameter::Required("...".into()),
        ],
        examples: vec![
            HelpExample {
                desc: "rename foo to bar and bar to foo",
                code: "ren foo bar bar foo",
            },
            HelpExample {
                desc: "rename idx 0 to foo",
                code: "ren 0 foo",
            },
        ],
        ..HelpMessage::new("ren")
    }
}

fn ren_intrinsic(mut blk: Block) -> Result<Step> {
    if blk.in_ty() != &Ty::Tab {
        return Err(Error::wrong_op_input_type(blk.in_ty(), blk.op_tag()));
    }
    blk.assert_output(Ty::Tab); // table -> table

    enum Ref {
        Name(eng::Argument),
        Idx(eng::Argument),
    }
    // hdrs and names take Nil input.
    let mut hdrs: Vec<Ref> = Vec::with_capacity(blk.args_len() / 2);
    let mut names = Vec::with_capacity(blk.args_len() / 2);

    while blk.args_len() > 1 {
        let hdr = blk.next_arg()?.supplied(Ty::Nil)?;
        let hdr = match hdr.return_ty() {
            Some(Ty::Num) => Ref::Idx(hdr.returns(Ty::Num)?.concrete()?),
            _ => Ref::Name(hdr.returns(Ty::Str)?.concrete()?),
        };

        hdrs.push(hdr);
        names.push(
            blk.next_arg()?
                .supplied(Ty::Nil)?
                .returns(Ty::Str)?
                .concrete()?,
        );
    }

    blk.eval_o(move |table, cx| {
        let mut table: Table = table.try_into()?;
        let mut indices = Vec::with_capacity(hdrs.len());
        // resolve the headers first so we don't encounter weird issues by updating the column
        // headers _while_ resolving the header indices.
        for h in &hdrs {
            let i = match h {
                Ref::Idx(x) => x
                    .resolve(|| Value::Nil, &cx)
                    .and_then(|n| cnv_num_to_uint::<usize>(n, &x.tag)),
                Ref::Name(x) => x
                    .resolve(|| Value::Nil, &cx)
                    .and_then(Str::try_from)
                    .and_then(|n| TableRow::col_idx(&table, n.as_str(), &x.tag)),
            }?;
            indices.push(i);
        }

        let t = table.make_mut();

        for (idx, i) in indices.into_iter().enumerate() {
            match t.col_mut(i) {
                Some(mut x) => {
                    let name = names[idx].resolve(|| Value::Nil, &cx)?;
                    if let Some(x) = x.next() {
                        *x = name.into();
                    }
                    Ok(())
                }
                None => Err(Error::eval(
                    match &hdrs[idx] {
                        Ref::Name(x) | Ref::Idx(x) => &x.tag,
                    },
                    format!("{} is outside table column bounds", i),
                    None,
                    "use `ls` command to view a table's headers".to_string(),
                )),
            }?;
        }

        cx.done_o(table)
    })
}

// ------ Ren-With -------------------------------------------------------------
fn ren_with_help() -> HelpMessage {
    HelpMessage {
        desc: "rename column headers using a row as a seed
each entry is fed into the expression, which returns a string
the default entry type required is a string"
            .into(),
        params: vec![
            HelpParameter::Required("row-idx".into()),
            HelpParameter::Required("name-expr".into()),
        ],
        flags: vec![("<type>", "the type of the entry")],
        examples: vec![
            HelpExample {
                desc: "rename the header with what is in row 2",
                code: "ren-with 2 #i",
            },
            HelpExample {
                desc: "append the headers with something",
                code: "ren-with 0 + ' bar'",
            },
            HelpExample {
                desc: "use the first row as a header and forget the old one",
                code: "ren-with 1 #i | skip 1",
            },
        ],
        ..HelpMessage::new("ren-with")
    }
}

fn ren_with_intrinsic(mut blk: Block) -> Result<Step> {
    if blk.in_ty() != &Ty::Tab {
        return Err(Error::wrong_op_input_type(blk.in_ty(), blk.op_tag()));
    }
    blk.assert_output(Ty::Tab); // table -> table

    let row_idx = blk
        .next_arg()?
        .supplied(Type::Nil)?
        .returns(Type::Num)?
        .concrete()?;
    let inty = type_flag(&mut blk)?;
    let expr = blk.next_arg()?;
    let expr = match inty {
        Some(t) => expr.supplied(t)?,
        None => expr,
    }
    .returns(Type::Str)?
    .concrete()?;

    let inty = expr.in_ty().clone();

    let blktag = blk.blk_tag().clone();

    blk.eval_o(move |table, cx| {
        let rowidx = row_idx
            .resolve(|| Value::Nil, &cx)
            .and_then(|v| cnv_num_to_uint(v, &row_idx.tag))?;
        let mut table: Table = table.try_into()?;
        if table.is_empty() {
            return Err(Error::empty_table(None, &blktag));
        }
        if rowidx >= table.rows_len() {
            return Err(Error::row_out_of_bounds(rowidx, &row_idx.tag));
        }

        let mut hdrs = Vec::with_capacity(table.cols_len());
        for (colidx, entry) in table
            .row(rowidx)
            .expect("row checked for existence")
            .enumerate()
        {
            let entry = TableRow::cnv_value(entry, &inty, rowidx, colidx, &row_idx.tag)?;
            let name: Str = expr.resolve(|| entry, &cx)?.try_into()?;
            hdrs.push(name);
        }

        let t = table.make_mut();
        if let Some(row) = t.row_mut(0) {
            row.zip(hdrs)
                .for_each(|(e, h)| *e = Entry::from(Value::from(h)));
        }

        cx.done_o(table)
    })
}

// ------ Reverse --------------------------------------------------------------
fn rev_help() -> HelpMessage {
    HelpMessage {
        desc: "reverse the order of the input
for String inputs; character ordering is reversed
for Table inputs; row or col ordering is reversed"
            .into(),
        flags: vec![("cols", "reverse table column ordering")],
        examples: vec![
            HelpExample {
                desc: "reverse table row ordering",
                code: "ls | rev",
            },
            HelpExample {
                desc: "reverse string character ordering",
                code: "\\ '!dlrow ,olleH' | rev",
            },
        ],
        ..HelpMessage::new("rev")
    }
}

fn rev_intrinsic(mut blk: Block) -> Result<Step> {
    match blk.in_ty() {
        Ty::Str => blk.eval_o(|input, cx| {
            Str::try_from(input)
                .map(|s| s.chars().rev().collect::<String>())
                .map(Str::from)
                .and_then(|x| cx.done_o(x))
        }),
        Ty::Tab => {
            let cols = blk.get_flag("cols").is_some();
            blk.eval_o(move |input, cx| {
                let mut table: Table = input.try_into()?;
                if cols {
                    table.make_mut().reverse_cols_par();
                } else {
                    table.make_mut().reverse_rows();
                }
                cx.done_o(table)
            })
        }
        x => Err(Error::wrong_op_input_type(x, blk.op_tag())),
    }
}

// ------ Skip -----------------------------------------------------------------
fn skip_help() -> HelpMessage {
    HelpMessage {
        desc: "skip the first n elements of a data structure".into(),
        params: vec![HelpParameter::Required("count".into())],
        examples: vec![
            HelpExample {
                desc: "skip the first 10 rows of a table",
                code: "skip 10",
            },
            HelpExample {
                desc: "skip the first 5 characters of a string",
                code: "\\ 'Hello, world!' | skip 5",
            },
            HelpExample {
                desc: "skip and take can be used to slice into a string",
                code: "\\ 'Hello, world!' | skip 7 | take 5",
            },
        ],
        ..HelpMessage::new("skip")
    }
}

fn skip_intrinsic(mut blk: Block) -> Result<Step> {
    match blk.in_ty() {
        Ty::Tab => {
            blk.assert_output(Ty::Tab); // table -> table
            let count = blk
                .next_arg()?
                .supplied(None)?
                .returns(Ty::Num)?
                .concrete()?;
            blk.eval_o(move |table, cx| {
                let count = count
                    .resolve(|| table.clone(), &cx)
                    .and_then(|v| cnv_num_to_uint::<usize>(v, &count.tag))?;
                let mut table = Table::try_from(table)?;
                if let Some(t) = table.get_mut() {
                    t.retain_rows(|i, _| i == 0 || i > count);
                } else {
                    let rows = table
                        .rows()
                        .take(1)
                        .chain(table.rows().skip(count + 1))
                        .map(|x| x.cloned());
                    let mut t = ::table::Table::new();
                    t.add_rows(rows);
                    table = t.into();
                }
                cx.done_o(table)
            })
        }
        Ty::Str => {
            blk.assert_output(Ty::Str); // str -> str
            let count = blk
                .next_arg()?
                .supplied(None)?
                .returns(Ty::Num)?
                .concrete()?;
            blk.eval_o::<_, Str>(move |string, cx| {
                let count = count
                    .resolve(|| string.clone(), &cx)
                    .and_then(|v| cnv_num_to_uint::<usize>(v, &count.tag))?;
                Str::try_from(string)
                    .map(|s| s.chars().skip(count).collect::<Str>())
                    .and_then(|x| cx.done_o(x))
            })
        }
        x => Err(Error::wrong_op_input_type(x, blk.op_tag())),
    }
}

// ------ Sorting --------------------------------------------------------------
fn sort_help() -> HelpMessage {
    HelpMessage {
        desc: "sort a table by column headers
each header sorts the rows lowest to highest in a canonical fashion,
in order specified (1st column is sorted first)
this sorts different value types, but NOT user-defined types. see `sort-by`"
            .into(),
        params: vec![HelpParameter::Required("col-name..".into())],
        examples: vec![
            HelpExample {
                desc: "sort ls by file size",
                code: "ls | sort size",
            },
            HelpExample {
                desc: "sort ls by ext, THEN by size (notice the inverted order)",
                code: "ls | sort size ext",
            },
        ],
        ..HelpMessage::new("sort")
    }
}

fn sort_intrinsic(mut blk: Block) -> Result<Step> {
    if blk.in_ty() != &Ty::Tab {
        return Err(Error::wrong_op_input_type(blk.in_ty(), blk.op_tag()));
    }

    blk.assert_output(Ty::Tab);
    let colnames = ColNameArgs::build(&mut blk)?;
    blk.eval_o(move |table, cx| {
        let mut table: Table = table.try_into()?;
        let cols = colnames.resolve_indices(&table, &cx)?;

        let t = table.make_mut();
        for (col, _) in cols {
            t.sort(col, cmp_table_entries);
        }

        cx.done_o(table)
    })
}

/// Ogma data types are compared on name. OgmaData with the same types are considered 'equal'.
fn cmp_table_entries(a: &Entry<Value>, b: &Entry<Value>) -> std::cmp::Ordering {
    // overall order of variants: Bool, Num, Str, OgmaData, Nil, Table, TableRow
    let (ai, bi) = (entry_discriminant(a), entry_discriminant(b));
    if ai != bi {
        return ai.cmp(&bi);
    }

    use std::cmp::Ordering::*;
    use Entry as E;
    use Value as V;
    use E::Obj as O;

    // we know a and b types variants will match now
    match (a, b) {
        (E::Nil, _) | (O(V::Nil), _) => Equal,
        (E::Num(lhs), E::Num(rhs))
        | (O(V::Num(lhs)), E::Num(rhs))
        | (E::Num(lhs), O(V::Num(rhs)))
        | (O(V::Num(lhs)), O(V::Num(rhs))) => lhs.cmp(rhs),
        (O(V::Bool(lhs)), O(V::Bool(rhs))) => lhs.cmp(rhs),
        (O(V::Str(lhs)), O(V::Str(rhs))) => lhs.cmp(rhs),
        (O(V::Tab(_)), _) => Equal,
        (O(V::TabRow(_)), _) => Equal,
        (O(V::Ogma(lhs)), O(V::Ogma(rhs))) => lhs.ty().name().str().cmp(rhs.ty().name().str()),
        _ => unreachable!("should not reach here given all equal cases are done"),
    }
}

/// Assigns a number to each variant of Entry<Value> combo.
/// `Bool = 0, Num = 1, Str = 2, OgmaData = 3, Nil = 4, Table = 5, TableRow = 6`
fn entry_discriminant(e: &Entry<Value>) -> u8 {
    match e {
        Entry::Obj(Value::Bool(_)) => 0,
        Entry::Num(_) | Entry::Obj(Value::Num(_)) => 1,
        Entry::Obj(Value::Str(_)) => 2,
        Entry::Obj(Value::Ogma(_)) => 3,
        Entry::Nil | Entry::Obj(Value::Nil) => 4,
        Entry::Obj(Value::Tab(_)) => 5,
        Entry::Obj(Value::TabRow(_)) => 6,
    }
}

// sort-by
// whilst sort uses canonicalized entry comparison, sort-by converts each row into a value using an
// expression, then sorts the resulting values (and by proxy; the table)
// sorting the values uses `cmp` definitions
// the actual implementation is a bit more complex; we must create a pseudo-env to eval `cmp`
fn sortby_help() -> HelpMessage {
    HelpMessage {
        desc: "sort table using an expression
the result of the expression must define a `cmp` implementation
this can be used to sort user-defined types"
            .into(),
        params: vec![HelpParameter::Required("<expr>".into())],
        examples: vec![
            HelpExample {
                desc: "sort ls by file size",
                code: "ls | sort-by { get size }",
            },
            HelpExample {
                desc: "sort using a user-defined type",
                code: "ls | sort-by { Point { get size } }",
            },
        ],
        ..HelpMessage::new("sort-by")
    }
}

fn sortby_intrinsic(mut blk: Block) -> Result<Step> {
    if blk.in_ty() != &Ty::Tab {
        return Err(Error::wrong_op_input_type(blk.in_ty(), blk.op_tag()));
    }
    blk.assert_output(Ty::Tab);

    // the expression which will be sorted on
    let key = blk.next_arg()?.supplied(Ty::TabRow)?.concrete()?;

    let cmpr = BinaryOp::cmp_cmd(key.out_ty(), "sort-by", &blk, &key)?;

    blk.eval_o::<_, Table>(move |table, cx| {
        let table = Table::try_from(table)?;
        let sorting_values: SortIdx = resolve_trow_expr_par(&table, &key, &cx)?
            .into_iter()
            .enumerate()
            .collect();
        let sorted_values = sort_values(sorting_values, &mut cmpr.pin_env(), &cx)?;
        cx.done_o(reorder_table(table, sorted_values))
    })
}

type SortIdx = Vec<(usize, Value)>;

/// Sort the table according to the order in `values`.
///
/// For each comparison `a` and `b` (which are `Value`s):
///   1. `b` is _set_ as `$rhs`
///   2. comparer is evaluated with `a` as input
///   3. Ord is known to return, and is converted into Ordering
///
/// Table is re-ordered according to sorted values.
fn sort_values<T>(mut values: SortIdx, binop: &mut BinaryOpRef<T>, cx: &Context) -> Result<SortIdx>
where
    T: Fn(Value) -> cmp::Ordering,
{
    let mut err = None;
    // sort values using a comparer
    values[1..].sort_by(|a, b| {
        // lhs is `a`, rhs is `b`
        match binop.eval(a.1.clone(), b.1.clone(), cx) {
            Ok(ord) => ord,
            Err(e) => {
                err = Some(e);
                cmp::Ordering::Equal
            }
        }
    });

    match err {
        Some(e) => Err(e),
        None => Ok(values),
    }
}

fn reorder_table(mut table: Table, order: SortIdx) -> Table {
    let mut x = Vec::with_capacity(table.rows_len());
    if let Some(table) = table.get_mut() {
        let mut table = mem::take(table).into_raw();
        for (idx, _) in order {
            x.push(mem::take(&mut table[idx]));
        }
    } else {
        for (idx, _) in order {
            x.push(table.row(idx).unwrap().cloned().collect());
        }
    }

    ::table::Table::from(x).into()
}

// ------ Take -----------------------------------------------------------------
fn take_help() -> HelpMessage {
    HelpMessage {
        desc: "take the first n elements of a data structure".into(),
        params: vec![HelpParameter::Required("count".into())],
        examples: vec![
            HelpExample {
                desc: "take the first 10 rows of a table",
                code: "take 10",
            },
            HelpExample {
                desc: "take the first 5 characters of a string",
                code: "\\ 'Hello, world!' | take 5",
            },
            HelpExample {
                desc: "skip and take can be used to slice into a string",
                code: "\\ 'Hello, world!' | skip 7 | take 5",
            },
        ],
        ..HelpMessage::new("take")
    }
}

fn take_intrinsic(mut blk: Block) -> Result<Step> {
    match blk.in_ty() {
        Ty::Tab => {
            blk.assert_output(Ty::Tab); // table -> table
            let count = blk
                .next_arg()?
                .supplied(None)?
                .returns(Ty::Num)?
                .concrete()?;
            blk.eval_o(move |table, cx| {
                let count = count
                    .resolve(|| table.clone(), &cx)
                    .and_then(|v| cnv_num_to_uint::<usize>(v, &count.tag))?;
                let mut table = Table::try_from(table)?;
                if let Some(t) = table.get_mut() {
                    t.retain_rows(|i, _| i == 0 || i <= count);
                } else {
                    let rows = table
                        .rows()
                        .take(1)
                        .chain(table.rows().skip(1).take(count))
                        .map(|x| x.cloned());
                    let mut t = ::table::Table::new();
                    t.add_rows(rows);
                    table = t.into();
                }
                cx.done_o(table)
            })
        }
        Ty::Str => {
            blk.assert_output(Ty::Str);
            let count = blk
                .next_arg()?
                .supplied(None)?
                .returns(Ty::Num)?
                .concrete()?;
            blk.eval_o::<_, Str>(move |string, cx| {
                let count = count
                    .resolve(|| string.clone(), &cx)
                    .and_then(|v| cnv_num_to_uint::<usize>(v, &count.tag))?;
                Str::try_from(string)
                    .map(|s| s.chars().take(count).collect::<Str>())
                    .and_then(|x| cx.done_o(x))
            })
        }
        x => Err(Error::wrong_op_input_type(x, blk.op_tag())),
    }
}
