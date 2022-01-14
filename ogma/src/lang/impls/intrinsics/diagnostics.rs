use super::*;

pub fn add_intrinsics(impls: &mut Implementations) {
    add! { impls,
        (benchmark, Diagnostics)
        (typify, Diagnostics)
    };
}

// ------ Typify ---------------------------------------------------------------
fn typify_help() -> HelpMessage {
    HelpMessage {
        desc: "output an expanded, type annotated, string of the argument".into(),
        params: vec![HelpParameter::Required("argument".into())],
        examples: vec![
            HelpExample {
                desc: "output the types of the ls command",
                code: "typify ls",
            },
            HelpExample {
                desc: "output the types of an expression",
                code: "typify { ls | filter size > 3 }",
            },
        ],
        ..HelpMessage::new("typify")
    }
}

fn typify_intrinsic(mut blk: Block) -> Result<Step> {
    let arg = blk.next_arg(None)?;

    blk.eval_o(move |_, cx| {
        let annotation = Str::from(arg.type_annotation().into_owned());
        cx.done_o(annotation)
    })
}
