use super::*;
use std::cmp;

pub fn add_intrinsics(impls: &mut Implementations) {
    add! { impls,
        (cmp, Cmp)
        (eq, Cmp)
    //         (max, Cmp)
    //         (min, Cmp)
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
        Ty::Def(x) if x.name().str().starts_with("U_") => {
            todo!();
            //             let els = match x.structure() {
            //                 types::TypeVariant::Product(x) => x.len(),
            //                 _ => 0,
            //             };
            //             blk.next_arg_do_not_remove(None)?.returns(blk.in_ty())?.concrete()?; // this checks same lhs=rhs type
            //             let def = &lang::syntax::parse::definition_impl(
            //                 build_tuple_cmp_def_str(els),
            //                 Location::Ogma,
            //                 blk.defs,
            //             )
            //             .map_err(|(e, _)| e)?;
            //             let ordty = Ty::Def(types::ORD.get());
            //             let evaltr = eng::DefImplEvaluator::build(&mut blk, def)?.returns(&ordty)?;
            //             blk.eval(ordty, move |input, cx| {
            //                 evaltr.eval(input, cx.clone()).and_then(|(x, _)| cx.done(x))
            //             })
        }
        x => Err(Error::wrong_op_input_type(x, blk.op_tag())),
    }
}

/// follows the pattern `let {get t# | cmp $rhs.t#} $c#` and `if {\\ $c# | != Ord::Eq} $c#`.
fn build_tuple_cmp_def_str(els: usize) -> String {
    use std::fmt::Write;
    let mut s = "def tuple-cmp (rhs) { let ".to_string();
    for i in 0..els {
        write!(&mut s, "{{get t{0} | cmp $rhs.t{0}}} $c{0} ", i).ok();
    }
    s += "| if ";
    let els = els.saturating_sub(1);
    for i in 0..els {
        write!(&mut s, "{{\\ $c{0} | != Ord::Eq}} $c{0} ", i).ok();
    }
    write!(&mut s, "$c{} }}", els).ok(); // instead of testing every element, pass the last through
    s
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
        Ty::Def(x) if x.name().str().starts_with("U_") => {
            // TODO
            // Tuple inferring will not since they are not stored in the types
            todo!()
            //             let els = match x.structure() {
            //                 types::TypeVariant::Product(x) => x.len(),
            //                 _ => 0,
            //             };
            //             blk.next_arg_do_not_remove(None)?.returns(blk.in_ty())?; // this checks same lhs=rhs type
            //             let def = &lang::syntax::parse::definition_impl(
            //                 build_tuple_eq_def_str(els),
            //                 Location::Ogma,
            //                 blk.defs,
            //             )
            //             .map_err(|(e, _)| e)?;
            //             let evaltr = eng::DefImplEvaluator::build(&mut blk, def)?.returns(&Ty::Bool)?;
            //             blk.eval(Ty::Bool, move |input, cx| {
            //                 evaltr.eval(input, cx.clone()).and_then(|(x, _)| cx.done(x))
            //             })
        }
        x => Err(Error::wrong_op_input_type(x, blk.op_tag())),
    }
}

/// follows the pattern `and {get t# | = $rhs.t#}`.
fn build_tuple_eq_def_str(els: usize) -> String {
    use std::fmt::Write;
    let mut s = "def tuple-eq (rhs) { and ".to_string();
    for i in 0..els {
        write!(&mut s, "{{get t{0} | = $rhs.t{0}}} ", i).ok();
    }
    s.push('}');
    s
}

// ------ Max ------------------------------------------------------------------
// fn max_help() -> HelpMessage {
//     variadic_help(
//         "max",
//         "return the maximum value",
//         vec![
//             HelpExample {
//                 desc: "maximum of 2 and 3",
//                 code: "\\ 2 | max 3",
//             },
//             HelpExample {
//                 desc: "maximum of multiple args",
//                 code: "max 1 2 3 4 5",
//             },
//         ],
//     )
// }

// fn max_intrinsic(blk: Block) -> Result<Step> {
//     variadic_intrinsic::<Number, _>(blk, |prev, next| {
//         let x = prev.map(|prev| std::cmp::max(prev, next)).unwrap_or(next);
//         (x, false)
//     })
// }

// ------ Min ------------------------------------------------------------------
// fn min_help() -> HelpMessage {
//     variadic_help(
//         "min",
//         "return the minimum value",
//         vec![
//             HelpExample {
//                 desc: "minimum of 2 and 3",
//                 code: "\\ 2 | min 3",
//             },
//             HelpExample {
//                 desc: "minimum of multiple args",
//                 code: "min 1 2 3 4 5",
//             },
//         ],
//     )
// }

// fn min_intrinsic(blk: Block) -> Result<Step> {
//     variadic_intrinsic::<Number, _>(blk, |prev, next| {
//         let x = prev.map(|prev| std::cmp::min(prev, next)).unwrap_or(next);
//         (x, false)
//     })
// }

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn build_tuple_eq_test() {
        let f = build_tuple_eq_def_str;
        assert_eq!(&f(1), "def tuple-eq (rhs) { and {get t0 | = $rhs.t0} }");
        assert_eq!(
            &f(2),
            "def tuple-eq (rhs) { and {get t0 | = $rhs.t0} {get t1 | = $rhs.t1} }"
        );
        assert_eq!(&f(3), "def tuple-eq (rhs) { and {get t0 | = $rhs.t0} {get t1 | = $rhs.t1} {get t2 | = $rhs.t2} }");
    }

    #[test]
    fn build_tuple_cmp_test() {
        let f = build_tuple_cmp_def_str;
        assert_eq!(
            &f(1),
            "def tuple-cmp (rhs) { \
         let {get t0 | cmp $rhs.t0} $c0 | if \
         $c0 }"
        );
        assert_eq!(
            &f(2),
            "def tuple-cmp (rhs) { \
         let {get t0 | cmp $rhs.t0} $c0 {get t1 | cmp $rhs.t1} $c1 | if \
         {\\ $c0 | != Ord::Eq} $c0 \
         $c1 }"
        );
        assert_eq!(
            &f(3),
            "def tuple-cmp (rhs) { \
         let {get t0 | cmp $rhs.t0} $c0 {get t1 | cmp $rhs.t1} $c1 {get t2 | cmp $rhs.t2} $c2 | if \
         {\\ $c0 | != Ord::Eq} $c0 \
         {\\ $c1 | != Ord::Eq} $c1 \
         $c2 }"
        );
    }
}
