use super::*;

pub fn add_intrinsics(impls: &mut Implementations) {
    add! { impls,
        (benchmark, Diagnostics)
        (typify, Diagnostics)
    };
}

// ------ Typify ---------------------------------------------------------------
fn typify_help() -> HelpMessage {
    // TODO -- implement properly
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
    // TODO -- implement properly
    let arg = blk.next_arg(None)?;

    blk.eval_o(move |_, cx| {
        let annotation = Str::from(arg.type_annotation().into_owned());
        cx.done_o(annotation)
    })
}
