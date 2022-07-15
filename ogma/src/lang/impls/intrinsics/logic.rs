use super::*;

pub fn add_intrinsics(impls: &mut Implementations) {
    add! { impls,
        (and, Logic)
        (if, Logic)
        ("not", bool, not_bool, Logic)
        (or, Logic)
    };
}

// ------ And ------------------------------------------------------------------
fn and_help() -> HelpMessage {
    variadic_help(
        "and",
        "returns true if all arguments are true",
        vec![HelpExample {
            desc: "10 is less than 20 and equal to 10",
            code: "\\ 10 | and { < 20 } { = 10 }",
        }],
    )
}

fn and_intrinsic(blk: Block) -> Result<Step> {
    variadic_intrinsic_in_agnostic::<bool, _>(blk, |prev, next| {
        let x = prev && next;
        (x, !x) // short circuit if x is false
    })
}

// ------ If -------------------------------------------------------------------
fn if_help() -> HelpMessage {
    HelpMessage {
        desc: "evaluate expression if predicate is met
input is carried through to each of the expressions
`expr-if-true` and `expr-if-false` must evaluate to the same type
`if` can be overloaded such that it can test multiple predicates"
            .into(),
        params: vec![
            HelpParameter::Required("predicate-1".into()),
            HelpParameter::Required("expr-if-true-1".into()),
            HelpParameter::Optional("predicate-2".into()),
            HelpParameter::Optional("expr-if-true-2".into()),
            HelpParameter::Required("... expr-if-false".into()),
        ],
        examples: vec![
            HelpExample {
                desc: "return 2 if 3, otherwise 1",
                code: "\\ 3 | if { = 3 } 2 1",
            },
            HelpExample {
                desc: "return 2 if 3, 1 if 2, otherwise 0",
                code: "\\ 10 | if {= 3} 2 {= 2} 1 0",
            },
        ],
        ..HelpMessage::new("if")
    }
}

fn if_intrinsic(mut blk: Block) -> Result<Step> {
    let args = blk.args_len();
    if args % 2 == 0 {
        let mut e = Error::insufficient_args(blk.blk_tag(), args as u8, None);
        e.help_msg =
            Some("`if` requires odd number of arguments to match true/false expressions".into());
        return Err(e);
    }

    struct Cond {
        pred: eng::Argument,
        expr: eng::Argument,
    }

    let mut args = Vec::with_capacity(args / 2);
    while blk.args_len() > 1 {
        args.push(Cond {
            pred: blk
                .next_arg()?
                .supplied(None)?
                .returns(Ty::Bool)?
                .concrete()?,
            expr: blk.next_arg()?.supplied(None)?.concrete()?,
        });
    }
    let else_ = blk.next_arg()?.supplied(None)?.concrete()?;

    let out_ty = else_.out_ty().clone();

    // validate all the branches
    for cond in &args {
        if out_ty != *cond.expr.out_ty() {
            return Err(Error::eval(
                &cond.expr.tag,
                "branch arms do not have matching output types",
                "this branch has a different output type".to_string(),
                "branching impls require consistent output types".to_string(),
            ));
        }
    }

    blk.eval(out_ty, move |input, cx| {
        for Cond { pred, expr } in &args {
            let predicate: bool = pred.resolve(|| input.clone(), &cx)?.try_into()?;
            if predicate {
                return expr.resolve(|| input, &cx).and_then(|x| cx.done(x));
            }
        }
        else_.resolve(|| input, &cx).and_then(|x| cx.done(x))
    })
}

// ------ Not ------------------------------------------------------------------
fn not_bool_help() -> HelpMessage {
    HelpMessage {
        desc: "negates a boolean value".into(),
        examples: vec![HelpExample {
            desc: "1 is NOT greater than 2",
            code: "\\ 1 | > 2 | not",
        }],
        ..HelpMessage::new("not")
    }
}

fn not_bool_intrinsic(mut blk: Block) -> Result<Step> {
    blk.assert_input(&Ty::Bool)?;
    blk.assert_output(Ty::Bool); // takes a bool, returns a bool

    blk.eval_o(|val, cx| bool::try_from(val).and_then(|x| cx.done_o(!x)))
}

// ------ Or -------------------------------------------------------------------
fn or_help() -> HelpMessage {
    variadic_help(
        "or",
        "returns true if any arguments are true",
        vec![HelpExample {
            desc: "1 is less than OR equal to 2",
            code: "\\ 1 | or { < 2 } { = 2 }",
        }],
    )
}

fn or_intrinsic(blk: Block) -> Result<Step> {
    variadic_intrinsic_in_agnostic::<bool, _>(blk, |prev, next| {
        let x = prev || next;
        (x, x) // short-circuit if true!
    })
}
