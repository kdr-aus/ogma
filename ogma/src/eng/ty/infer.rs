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

    let _sink = &mut Vec::new();

    eprintln!(
        "Inferring input for {}",
        compiler.ag()[op.idx()].op().unwrap().1.str()
    );

    for (_name, ty) in types {
        eprintln!("🔬 Testing compilation with inferred input: {}", _name);

        let compiled = compiler.compile_block(op, ty.clone(), _sink).is_ok();
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

impl Error {
    pub fn crate_err(&self, blk: &Tag) -> crate::Error {
        use crate::common::err::*;

        match self {
            Self::NoTypes => crate::Error {
                cat: Category::Semantics,
                desc: "op does not compile with any known types".into(),
                traces: trace(blk, None),
                help_msg: Some("try specifying input type to the block".into()),
            },
            Self::Ambiguous { ty1, ty2 } => crate::Error {
                cat: Category::Semantics,
                desc: "ambiguous inference. more than one input type can compile op".into(),
                traces: trace(blk, None),
                help_msg: Some("try specifying input type to the block".into()),
            },
        }
    }
}
