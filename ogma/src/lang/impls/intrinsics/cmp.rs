use super::*;
use std::cmp;

pub fn add_intrinsics(impls: &mut Implementations) {
    add! { impls,
        (cmp, Cmp)
        (eq, Cmp)
        (max, Cmp)
        (min, Cmp)
    };
}

// ------ Cmp ------------------------------------------------------------------
fn cmp_help() -> HelpMessage {
    HelpMessage {
        desc: "compare <rhs> to input".into(),
        params: vec![HelpParameter::Required("rhs".into())],
        examples: vec![HelpExample {
            desc: "compare 2 to 1",
            code: "\\ 1 | cmp 2",
        }],
        ..HelpMessage::new("cmp")
    }
}

fn cmp_intrinsic(mut blk: Block) -> Result<Step> {
    blk.assert_output(cmp::Ordering::as_type()); // all 'cmp's return an Ord

    match blk.in_ty() {
        Ty::Nil => {
            blk.next_arg()?
                .supplied(None)?
                .returns(Ty::Nil)?
                .concrete()?; // we don't use rhs but we do req its existence
            blk.eval_o(|_, cx| cx.done_o(cmp::Ordering::Equal))
        }
        Ty::Bool => {
            let rhs = blk
                .next_arg()?
                .supplied(None)?
                .returns(Ty::Bool)?
                .concrete()?;
            blk.eval_o(move |lhs, cx| {
                let lhs: bool = lhs.try_into()?;
                let rhs: bool = rhs.resolve(|| lhs.into(), &cx)?.try_into()?;
                cx.done_o(lhs.cmp(&rhs))
            })
        }
        Ty::Num => {
            let rhs = blk
                .next_arg()?
                .supplied(None)?
                .returns(Ty::Num)?
                .concrete()?;
            blk.eval_o(move |lhs, cx| {
                let lhs: Number = lhs.try_into()?;
                let rhs: Number = rhs.resolve(|| lhs.into(), &cx)?.try_into()?;
                cx.done_o(lhs.cmp(&rhs))
            })
        }
        Ty::Str => {
            let rhs = blk
                .next_arg()?
                .supplied(None)?
                .returns(Ty::Str)?
                .concrete()?;
            blk.eval_o(move |lhs, cx| {
                let lhs: Str = lhs.try_into()?;
                let rhs: Str = rhs.resolve(|| lhs.clone().into(), &cx)?.try_into()?;
                cx.done_o(lhs.cmp(&rhs))
            })
        }
        Ty::Def(x) if x.as_ref() == "Ord" => {
            let ordty = Type::Def(types::ORD.get());
            let rhs = blk.next_arg()?.supplied(None)?.returns(ordty)?.concrete()?;
            // cmp Ord to Ord returns another Ord
            blk.eval_o(move |lhs, cx| {
                let lhs_variant = lhs.variant_idx().expect("Ord type");
                let rhs = rhs.resolve(|| lhs, &cx)?.variant_idx().expect("Ord type");
                cx.done_o(lhs_variant.cmp(&rhs))
            })
        }
        Ty::Def(x) if x.is_tuple() => {
            let els = match x.structure() {
                types::TypeVariant::Product(x) => x.len(),
                _ => 0,
            };

            let (var, code) = build_tuple_cmp_code(els);

            let mut injector = eng::CodeInjector::new(code, blk.defs())
                .map_err(|e| eprintln!("{}", e))
                .expect("this should parse fine");

            let ty = blk.in_ty().clone();

            // map the RHS to a var. RHS returns the same type as block's input
            injector.map_arg_to_var(&mut blk, var, None, ty.clone())?;

            let injector = injector
                .compile(ty, blk.defs())
                .map_err(|e| e.wrap_code_injection(blk.blk_tag()))?;

            let oty = injector.out_ty();
            let exp_ty = Ty::Def(types::ORD.get());

            if oty != &exp_ty {
                Err(Error::unexp_code_injection_output_ty(
                    oty,
                    &exp_ty,
                    blk.blk_tag(),
                ))
            } else {
                blk.eval(exp_ty, move |input, cx| {
                    let v = injector.eval(input, &cx)?;
                    cx.done(v)
                })
            }
        }
        x => Err(Error::wrong_op_input_type(x, blk.op_tag())),
    }
}

/// follows the pattern `let {get t# | cmp $rhs.t#} $c#` and `if {\\ $c# | != Ord::Eq} $c#`.
fn build_tuple_cmp_code(els: usize) -> (&'static str, String) {
    use std::fmt::Write;

    let var_name = "rhs";

    let mut code = (0..els).fold(String::from("let "), |mut s, i| {
        write!(
            &mut s,
            "{{get t{0} | cmp ${var}.t{0}}} $c{0} ",
            i,
            var = var_name
        )
        .ok();
        s
    });

    code += "| if ";

    let els = els.saturating_sub(1); // don't test _every_ element, pass the last through
    let mut code = (0..els).fold(code, |mut s, i| {
        write!(&mut s, "{{\\ $c{0} | != Ord::Eq}} $c{0} ", i).ok();
        s
    });

    write!(&mut code, "$c{}", els).ok();

    (var_name, code)
}

// ------ Eq -------------------------------------------------------------------
fn eq_help() -> HelpMessage {
    HelpMessage {
        desc: "returns if <rhs> is equal to input".into(),
        params: vec![HelpParameter::Required("rhs".into())],
        examples: vec![
            HelpExample {
                desc: "does 2 equal 1",
                code: "\\ 1 | eq 2",
            },
            HelpExample {
                desc: "1 equals 1",
                code: "\\ 1 | eq 1",
            },
        ],
        ..HelpMessage::new("eq")
    }
}

fn eq_intrinsic(mut blk: Block) -> Result<Step> {
    blk.assert_output(Ty::Bool); // equals always returns a boolean value (at least our intrinsic does)

    match blk.in_ty() {
        Ty::Nil => {
            // we don't use rhs but we do req its existence
            blk.next_arg()?
                .supplied(None)?
                .returns(Ty::Nil)?
                .concrete()?;
            blk.eval_o(|_, cx| cx.done_o(true))
        }
        Ty::Bool => {
            let rhs = blk
                .next_arg()?
                .supplied(None)?
                .returns(Ty::Bool)?
                .concrete()?;
            blk.eval_o(move |lhs, cx| {
                let lhs: bool = lhs.try_into()?;
                let rhs: bool = rhs.resolve(|| lhs.into(), &cx)?.try_into()?;
                cx.done_o(lhs.eq(&rhs))
            })
        }
        Ty::Num => {
            let rhs = blk
                .next_arg()?
                .supplied(None)?
                .returns(Ty::Num)?
                .concrete()?;
            blk.eval_o(move |lhs, cx| {
                let lhs: Number = lhs.try_into()?;
                let rhs: Number = rhs.resolve(|| lhs.into(), &cx)?.try_into()?;
                cx.done_o(lhs.eq(&rhs))
            })
        }
        Ty::Str => {
            let rhs = blk
                .next_arg()?
                .supplied(None)?
                .returns(Ty::Str)?
                .concrete()?;
            blk.eval_o(move |lhs, cx| {
                let lhs: Str = lhs.try_into()?;
                let rhs: Str = rhs.resolve(|| lhs.clone().into(), &cx)?.try_into()?;
                cx.done_o(lhs.eq(&rhs))
            })
        }
        Ty::Def(x) if x.as_ref() == "Ord" => {
            let ordty = Type::Def(types::ORD.get());
            let rhs = blk.next_arg()?.supplied(None)?.returns(ordty)?.concrete()?;
            blk.eval_o(move |lhs, cx| {
                let lhs_variant = lhs.variant_idx().expect("Ord type");
                let rhs = rhs.resolve(|| lhs, &cx)?.variant_idx().expect("Ord type");
                cx.done_o(lhs_variant.eq(&rhs))
            })
        }
        Ty::Def(x) if x.is_tuple() => {
            let els = match x.structure() {
                types::TypeVariant::Product(x) => x.len(),
                _ => 0,
            };

            let (var, code) = build_tuple_eq_code(els);

            let mut injector = eng::CodeInjector::new(code, blk.defs())
                .map_err(|e| eprintln!("{}", e))
                .expect("this should parse fine");

            let ty = blk.in_ty().clone();

            // map the RHS to a var. RHS returns the same type as block's input
            injector.map_arg_to_var(&mut blk, var, None, ty.clone())?;

            let injector = injector
                .compile(ty, blk.defs())
                .map_err(|e| e.wrap_code_injection(blk.blk_tag()))?;

            let oty = injector.out_ty();
            let exp_ty = Ty::Bool;

            if oty != &exp_ty {
                Err(Error::unexp_code_injection_output_ty(
                    oty,
                    &exp_ty,
                    blk.blk_tag(),
                ))
            } else {
                blk.eval(exp_ty, move |input, cx| {
                    let v = injector.eval(input, &cx)?;
                    cx.done(v)
                })
            }
        }
        x => Err(Error::wrong_op_input_type(x, blk.op_tag())),
    }
}

/// follows the pattern `and {get t# | = $rhs.t#}`.
fn build_tuple_eq_code(els: usize) -> (&'static str, String) {
    use std::fmt::Write;

    let var_name = "rhs";

    let s = (0..els).fold(String::from("and "), |mut s, i| {
        write!(&mut s, "{{ get t{0} | = ${var}.t{0} }} ", i, var = var_name).ok();
        s
    });

    (var_name, s)
}

// ------ Max ------------------------------------------------------------------
fn max_help() -> HelpMessage {
    variadic_help(
        "max",
        "return the maximum value",
        vec![
            HelpExample {
                desc: "maximum of 2 and 3",
                code: "\\ 2 | max 3",
            },
            HelpExample {
                desc: "maximum of multiple args",
                code: "max 1 2 3 4 5",
            },
        ],
    )
}

fn max_intrinsic(blk: Block) -> Result<Step> {
    variadic_intrinsic_in_constrained::<Number, _>(blk, |prev, next| {
        let x = std::cmp::max(prev, next);
        (x, false)
    })
}

// ------ Min ------------------------------------------------------------------
fn min_help() -> HelpMessage {
    variadic_help(
        "min",
        "return the minimum value",
        vec![
            HelpExample {
                desc: "minimum of 2 and 3",
                code: "\\ 2 | min 3",
            },
            HelpExample {
                desc: "minimum of multiple args",
                code: "min 1 2 3 4 5",
            },
        ],
    )
}

fn min_intrinsic(blk: Block) -> Result<Step> {
    variadic_intrinsic_in_constrained::<Number, _>(blk, |prev, next| {
        let x = std::cmp::min(prev, next);
        (x, false)
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn build_tuple_eq_test() {
        let f = build_tuple_eq_code;
        assert_eq!(&f(1).1, "and { get t0 | = $rhs.t0 } ");
        assert_eq!(
            &f(2).1,
            "and { get t0 | = $rhs.t0 } { get t1 | = $rhs.t1 } "
        );
        assert_eq!(
            &f(3).1,
            "and { get t0 | = $rhs.t0 } { get t1 | = $rhs.t1 } { get t2 | = $rhs.t2 } "
        );
    }

    #[test]
    fn build_tuple_cmp_test() {
        let f = build_tuple_cmp_code;
        assert_eq!(&f(1).1, "let {get t0 | cmp $rhs.t0} $c0 | if $c0");
        assert_eq!(
            &f(2).1,
            "let {get t0 | cmp $rhs.t0} $c0 {get t1 | cmp $rhs.t1} $c1 | if {\\ $c0 | != Ord::Eq} $c0 $c1"
        );
        assert_eq!(
            &f(3).1,
            "let {get t0 | cmp $rhs.t0} $c0 \
                 {get t1 | cmp $rhs.t1} $c1 \
                 {get t2 | cmp $rhs.t2} $c2 | if \
                    {\\ $c0 | != Ord::Eq} $c0 \
                    {\\ $c1 | != Ord::Eq} $c1 \
                    $c2"
        );
    }
}
