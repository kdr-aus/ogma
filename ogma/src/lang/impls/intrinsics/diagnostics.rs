use super::*;

pub fn add_intrinsics(impls: &mut Implementations) {
    add! { impls,
        (benchmark, Diagnostics)
        (typify, Diagnostics)
    };
}

// ------ Typify ---------------------------------------------------------------
fn typify_help() -> HelpMessage {
    todo!();
    variadic_help(
        "Tuple",
        "construct a tuple of the result of each expression
tuples impl `eq` and `cmp` if all its fields also implement `eq` and `cmp`
tuples have unique types: `U_<t0_Ty>-<t1_Ty>_`
access of the fields is using `get t#` with the field number",
        vec![
            HelpExample {
                desc: "create a two element tuple of numbers. type: U_Num-Num_",
                code: "Tuple 1 2",
            },
            HelpExample {
                desc: "create 3 numbers after input. type: U_Num-Num-Num_",
                code: "\\ 3 | Tuple {+ 1} {+ 2} {+ 3}",
            },
            HelpExample {
                desc: "tuples are heterogeneous. type: U_Num-Str-Bool_",
                code: "Tuple 1 'foo' #t",
            },
            HelpExample {
                desc: "get the first and third element",
                code: "Tuple 1 'foo' 2 | + {get t0} {get t2}",
            },
        ],
    )
}

fn typify_intrinsic(mut blk: Block) -> Result<Step> {
    todo!();
    let len = blk.args_len();
    if len < 2 {
        return Err(Error::insufficient_args(&blk.blk_tag, len));
    }
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(blk.next_arg(None)?);
    }

    let ty = Arc::new(Tuple::ty(v.iter().map(|x| x.out_ty().clone()).collect()));

    blk.eval(Type::Def(ty.clone()), move |input, cx| {
        let mut data = Vec::with_capacity(v.len());
        for arg in &v {
            data.push(arg.resolve(|| input.clone(), &cx)?);
        }
        cx.done(OgmaData::new(ty.clone(), None, data))
    })
}
