use super::*;
use std::cmp;

pub fn add_intrinsics(impls: &mut Implementations) {
    add! { impls,
        ("+", Number, add_num, Arithmetic)
        ("+", Str, add_str, Arithmetic)
        ("+", Table, add_table, Arithmetic)

        ("*", Number, mul_num, Arithmetic)
        ("×", Number, mul_num, Arithmetic)

        ("-", Number, sub_num, Arithmetic)

        ("/", Number, div_num, Arithmetic)
        ("÷", Number, div_num, Arithmetic)

        (ceil, Arithmetic)
        (floor, Arithmetic)
        ("is-finite", isfinite, Arithmetic)
        (root, Arithmetic)
    };
}

fn variadic_intrinsic_num<F>(blk: Block, f: F) -> Result<Step>
where
    F: Fn(f64, f64) -> f64 + Send + Sync + 'static,
{
    variadic_intrinsic_in_constrained::<Number, _>(blk, move |prev, next| {
        let x = f(prev.as_f64(), next.as_f64()).into();
        (x, false)
    })
}

// ------ Add ------------------------------------------------------------------
fn add_num_help() -> HelpMessage {
    variadic_help(
        "+",
        "add numbers together",
        vec![
            HelpExample {
                desc: "add 2 to 1",
                code: "\\ 1 | + 2",
            },
            HelpExample {
                desc: "add multiple numbers together",
                code: "+ 1 2 3 4 5",
            },
        ],
    )
}

fn add_num_intrinsic(blk: Block) -> Result<Step> {
    variadic_intrinsic_num(blk, std::ops::Add::add)
}

fn add_str_help() -> HelpMessage {
    variadic_help(
        "+",
        "concatenate strings together",
        vec![
            HelpExample {
                desc: "join together strings",
                code: "\\ Hello | + ', world!'",
            },
            HelpExample {
                desc: "join strings with a new line",
                code: "\\ 'First Line' | + #b 'Second Line'",
            },
        ],
    )
}

fn add_str_intrinsic(blk: Block) -> Result<Step> {
    variadic_intrinsic_in_constrained::<Str, _>(blk, |mut prev, next| {
        prev.to_mut().push_str(&next);
        (prev, false)
    })
}

fn add_table_help() -> HelpMessage {
    let h = variadic_help(
        "+",
        "concatenate rows of table",
        vec![
            HelpExample {
                desc: "add two tables together, concatenating rows",
                code: "range 0 10 | + range 10 20",
            },
            HelpExample {
                desc: "index filesystem items, shrink table to min rows",
                code: "range 0 1000 | + --cols --intersect ls",
            },
        ],
    );

    HelpMessage {
        flags: vec![
            ("cols", "join tables (append columns)"),
            ("union", "expand table to capture all data (default)"),
            (
                "intersect",
                "use minimum size of table; min rows for --cols, min cols for concat rows",
            ),
        ],
        ..h
    }
}

fn add_table_intrinsic(mut blk: Block) -> Result<Step> {
    let mut f = |s| blk.get_flag(s).is_some();
    let byrow = !f("cols");
    let intersect = !f("union") && f("intersect");

    variadic_intrinsic_in_constrained(blk, move |prev, next| {
        (add_table2(prev, next, byrow, intersect), false)
    })
}

fn add_table2(prev: Table, next: Table, byrow: bool, intersect: bool) -> Table {
    if byrow {
        add_table_by_row(prev, next, intersect)
    } else {
        add_table_by_col(prev, next, intersect)
    }
}

fn add_table_by_row(mut prev: Table, next: Table, intersect: bool) -> Table {
    // prev has priority for column names
    let table = prev.make_mut();
    let (pc, nc) = (table.cols_len(), next.cols_len());

    if intersect {
        let take = cmp::min(pc, nc);
        table.add_rows(next.rows().skip(1).map(|x| x.take(take).cloned()));
        if nc < pc {
            // remove additional columns in prev
            for col in (nc..pc).rev() {
                table.remove_col_par(col);
            }
        }
    } else {
        // if table is empty there would be no headers, which would make the adding logic flawed.
        // however if table is empty it is easy to just return the `next` table!
        if table.is_empty() {
            return next;
        } else {
            table.add_rows(next.rows().skip(1).map(|x| x.cloned()));
            if nc > pc {
                // name the added cols
                for col in pc..nc {
                    if let Some(h) = table
                        .col_mut(col)
                        .expect("add_rows should extend cols")
                        .next()
                    {
                        *h = next.col(col).unwrap().next().cloned().unwrap_or_default();
                    }
                }
            }
        }
    }

    prev
}

fn add_table_by_col(mut prev: Table, next: Table, intersect: bool) -> Table {
    // prev has priority for column names
    let table = prev.make_mut();
    let (pr, nr) = (table.rows_len(), next.rows_len());

    if intersect {
        let take = cmp::min(pr, nr);
        table.add_cols(next.cols().map(|x| x.take(take).cloned()));
        if nr < pr {
            // remove additional rows in prev in REVERSE
            for row in (nr..pr).rev() {
                table.remove_row(row);
            }
        }
    } else {
        table.add_cols(next.cols().map(|x| x.cloned())); // additional rows are padded
    }

    prev
}

// ------ Ceil -----------------------------------------------------------------
fn ceil_help() -> HelpMessage {
    HelpMessage {
        desc: "return the smallest integer greater than or equal to a number".into(),
        ..HelpMessage::new("ceil")
    }
}

fn ceil_intrinsic(blk: Block) -> Result<Step> {
    if blk.in_ty() != &Ty::Num {
        return Err(Error::wrong_op_input_type(blk.in_ty(), blk.op_tag()));
    }
    blk.eval_o(move |n, cx| {
        Number::try_from(n)
            .map(|n| n.as_f64().ceil())
            .and_then(|n| cx.done_o(Number::from(n)))
    })
}

// ------ Div ------------------------------------------------------------------
fn div_num_help() -> HelpMessage {
    variadic_help(
        "/",
        "divide arguments against one another
dividing by 0 will result in infinity (∞)",
        vec![
            HelpExample {
                desc: "divide 4 by 2",
                code: "\\ 4 | / 2",
            },
            HelpExample {
                desc: "divide multiple numbers together",
                code: "\\ 1 | / 2 3 4 5",
            },
        ],
    )
}

fn div_num_intrinsic(blk: Block) -> Result<Step> {
    variadic_intrinsic_num(blk, std::ops::Div::div)
}

// ------ Floor ----------------------------------------------------------------
fn floor_help() -> HelpMessage {
    HelpMessage {
        desc: "return the largest integer less than or equal to a number".into(),
        ..HelpMessage::new("floor")
    }
}

fn floor_intrinsic(blk: Block) -> Result<Step> {
    if blk.in_ty() != &Ty::Num {
        return Err(Error::wrong_op_input_type(blk.in_ty(), blk.op_tag()));
    }
    blk.eval_o(move |n, cx| {
        Number::try_from(n)
            .map(|n| n.as_f64().floor())
            .and_then(|n| cx.done_o(Number::from(n)))
    })
}

// ------ Is Finite ------------------------------------------------------------
fn isfinite_help() -> HelpMessage {
    HelpMessage {
        desc: "returns whether a number is finite
a number is finite if it is not infinite AND not NaN"
            .into(),
        examples: vec![
            HelpExample {
                desc: "most numbers are finite",
                code: "\\ 5 | is-finite",
            },
            HelpExample {
                desc: "but dividing by zero isn't!",
                code: "÷ 1 0 | is-finite",
            },
        ],
        ..HelpMessage::new("is-finite")
    }
}

fn isfinite_intrinsic(blk: Block) -> Result<Step> {
    match blk.in_ty() {
        Ty::Num => blk.eval_o(|n, cx| {
            Number::try_from(n)
                .map(|n| n.as_f64().is_finite())
                .and_then(|x| cx.done_o(x))
        }),
        x => Err(Error::wrong_op_input_type(x, blk.op_tag())),
    }
}

// ------ Mul ------------------------------------------------------------------
fn mul_num_help() -> HelpMessage {
    variadic_help(
        "*",
        "multiply arguments together",
        vec![
            HelpExample {
                desc: "multiply 2 three times",
                code: "\\ 2 | * 3",
            },
            HelpExample {
                desc: "multiply multiple numbers together",
                code: "× 1 2 3 4 5",
            },
        ],
    )
}

fn mul_num_intrinsic(blk: Block) -> Result<Step> {
    variadic_intrinsic_num(blk, std::ops::Mul::mul)
}

// ------ Root -----------------------------------------------------------------
fn root_help() -> HelpMessage {
    HelpMessage {
        desc: "calculate the nth root of a number".into(),
        params: vec![HelpParameter::Required("index".into())],
        examples: vec![
            HelpExample {
                desc: "the square root of 4",
                code: "\\ 4 | root 2",
            },
            HelpExample {
                desc: "the cube root of 27",
                code: "\\ 27 | root 3",
            },
        ],
        ..HelpMessage::new("root")
    }
}

fn root_intrinsic(mut blk: Block) -> Result<Step> {
    if blk.in_ty() != &Ty::Num {
        return Err(Error::wrong_op_input_type(blk.in_ty(), blk.op_tag()));
    }
    let index = blk
        .next_arg()?
        .supplied(None)?
        .returns(Ty::Num)?
        .concrete()?;
    blk.eval_o(move |radicand, cx| {
        let index = index
            .resolve(|| radicand.clone(), &cx)
            .and_then(Number::try_from)?
            .as_f64();
        let radicand = Number::try_from(radicand)?.as_f64();
        let x = if (index - 2.0).abs() < 1e-10 {
            radicand.sqrt()
        } else if (index - 3.0).abs() < 1e-10 {
            radicand.cbrt()
        } else {
            radicand.powf(index.recip())
        };
        cx.done_o(Number::from(x))
    })
}

// ------ Sub ------------------------------------------------------------------
fn sub_num_help() -> HelpMessage {
    variadic_help(
        "-",
        "subtract arguments from one another",
        vec![
            HelpExample {
                desc: "subtract 2 from 1",
                code: "\\ 1 | - 2",
            },
            HelpExample {
                desc: "subtract multiple numbers together",
                code: "\\ 1 | - 2 3 4 5",
            },
        ],
    )
}

fn sub_num_intrinsic(blk: Block) -> Result<Step> {
    variadic_intrinsic_num(blk, std::ops::Sub::sub)
}
