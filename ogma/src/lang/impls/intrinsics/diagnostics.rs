use super::*;
use std::time::Instant;

pub fn add_intrinsics(impls: &mut Implementations) {
    add! { impls,
        (benchmark, Diagnostics)
        (typify, Diagnostics)
    };
}

// ------ Benchmark ------------------------------------------------------------
fn benchmark_help() -> HelpMessage {
    HelpMessage {
        desc: "time the expression evaluation\npipes <input> to <expr>".into(),
        params: vec![HelpParameter::Required("expr".into())],
        examples: vec![
            HelpExample {
                desc: "time loading in a file",
                code: "benchmark { open file.csv }",
            },
            HelpExample {
                desc: "time filtering a table",
                code: "\\ file.csv | benchmark filter = col 1",
            },
        ],
        ..HelpMessage::new("benchmark")
    }
}

fn benchmark_intrinsic(mut blk: Block) -> Result<Step> {
    let expr = blk.next_arg()?.supplied(None)?.concrete()?;
    blk.eval_o(move |val, cx| {
        let start = Instant::now();
        expr.resolve(|| val, &cx)?;
        cx.done_o(benchmark_table(start, Instant::now()))
    })
}

fn benchmark_table(start: Instant, end: Instant) -> Table {
    let d = end - start;
    let (ms, us) = (d.subsec_millis(), d.subsec_micros());
    let us = us - (ms * 1000);
    ::table::Table::from(vec![
        vec![
            o("duration"),
            o("seconds"),
            o("milliseconds"),
            o("microseconds"),
        ],
        vec![o(format!("{:?}", d)), n(d.as_secs()), n(ms), n(us)],
    ])
    .into()
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
    let arg = blk.next_arg()?; // get the next argument
    let argnode = arg.node(); // store the node index
    let arg = arg.supplied(None)?.concrete()?; // ensure the argument compiles

    // if it compiles, we should have the maximal amount of type info
    let s = eng::annotate_types(&blk, argnode); // build the type string
    let s = Str::from(s);

    blk.eval_o(move |_, cx| {
        cx.done_o(s.clone())
    })
}
