use super::*;
use comp::Compiler;
use graphs::*;
use types::Types;

pub enum Error {
    NoTypes,
    Ambiguous { ty1: Type, ty2: Type },
}

/// Infer the input of an Op node by testing various input types to see if it compiles.
pub fn input(op: OpNode, compiler: &Compiler) -> std::result::Result<Type, Error> {
    // NOTE - the types are returned in arbitary order
    // if we wanted to make this deterministic we could sort on name
    let types = compiler.defs.types().iter();

    let mut inferred = None;

    let _sink1 = &mut Default::default();
    let _sink2 = &mut Default::default();

    eprintln!(
        "Inferring input for {}",
        compiler.ag()[op.idx()].op().unwrap().1.str()
    );

    for (_name, ty) in types {
        eprintln!("🔬 Testing compilation with inferred input: {}", _name);

        let compiled = compiler
            .compile_block(op, ty.clone(), _sink1, _sink2)
            .is_ok();
        if compiled {
            eprintln!("🏁 Able to be compiled with input type: {}", _name);
        }

        match (compiled, inferred.take()) {
            (true, Some(ty1)) => {
                eprintln!("❌ FAILED -- Can compiled with two or more input types");
                return Err(Error::Ambiguous {
                    ty1,
                    ty2: ty.clone(),
                });
            }
            (true, None) => inferred = Some(ty.clone()),
            (false, x) => inferred = x,
        }
    }

    inferred.ok_or_else(|| Error::NoTypes)
}

pub fn output(op: OpNode, compiler: Compiler) -> std::result::Result<Compiler, Compiler> {
    // NOTE - the types are returned in arbitary order
    // if we wanted to make this deterministic we could sort on name
    let types = compiler.defs.types().iter();

    eprintln!(
        "Inferring output for {}",
        compiler.ag()[op.idx()].op().unwrap().1.str()
    );

    let parent = op.parent(compiler.ag());

    for (_name, ty) in types {
        eprintln!("🔬 Testing compilation with inferred output: {}", _name);

        // set the OUTPUT of the block to 'ty'
        let mut compiler = compiler.clone();
        let chgd = compiler.apply_graph_chgs(std::iter::once(tygraph::Chg::InferOutput(
            op.idx(),
            ty.clone(),
        ).into()));

        if !chgd {
            continue; // no point in trying to compile if nothing changed
        }

        // recurse into compile call -- breaking when the parent expr gets compiled
        match compiler.compile(parent) {
            Ok(compiler) => {
                eprintln!("🏁 Able to be compiled with output type: {}", _name);

                // break early, output inferring is greedy
                return Ok(compiler);
            }
            Err(_) => (), // continue
        }
    }

    Err(compiler) // no luck, return the unaltered compiler
}

impl Error {
    pub fn crate_err(&self, blk: &Tag) -> crate::Error {
        use crate::common::err::*;

        match self {
            Self::NoTypes => crate::Error {
                cat: Category::Semantics,
                desc: "op does not compile with any known types".into(),
                traces: trace(blk, None),
                help_msg: Some("try specifying input type to the block".into()),
                ..Default::default()
            },
            // TODO make this error better,
            // name the attempeted types
            // give a code example of type annotation
            Self::Ambiguous { ty1, ty2 } => crate::Error {
                cat: Category::Semantics,
                desc: "ambiguous inference. more than one input type can compile op".into(),
                traces: trace(blk, None),
                help_msg: Some("try specifying input type to the block".into()),
                ..Default::default()
            },
        }
    }
}

impl<'a> Block<'a> {
    /// Looks into the TG and fetches if this block's output type is known.
    /// It also will _infer_ the output type by deduction from TG context.
    ///
    /// If `None` type is going to be returned, flag the block's node as one that might have to
    /// have its output inferred.
    pub fn output_ty(&mut self) -> Option<Type> {
        let opnode = self.node;

        let ret = self.tg[opnode.idx()]
            .output
            .ty()
            .or_else(|| {
                opnode
                    .next(&self.ag)
                    .map(|next| {
                        // there is a next block
                        // return if there is a known input type
                        self.tg[next.idx()].input.ty()
                    })
                    .unwrap_or_else(|| {
                        // there is no next block
                        // use the output of the parent expr
                        self.tg[opnode.parent(&self.ag).idx()].output.ty()
                    })
            })
            .cloned();

        if ret.is_none() {
            *self.infer_output = true;
        }

        ret
    }
}
