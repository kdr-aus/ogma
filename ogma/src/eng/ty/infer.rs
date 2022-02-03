use super::*;
use comp::Compiler;
use graphs::*;
use types::Types;

/// Infer the input of an Op node by testing various input types to see if it compiles.
pub fn input(op: OpNode, compiler: &Compiler) -> Option<Type> {
    // NOTE - the types are returned in arbitary order
    // if we wanted to make this deterministic we could sort on name
    let types = compiler.defs.types().iter();

    let mut inferred = None;

    let _sink = &mut Vec::new();

    for (_name, ty) in types {
        eprintln!("🔬 Testing compilation with inferred input: {}", _name);

        let compiled = compiler.compile_block(op, ty.clone(), _sink).is_ok();
        if compiled {
            eprintln!("🏁 Able to be compiled with input type: {}", _name);
        }

        if compiled && inferred.is_some() {
            eprintln!("❌ FAILED -- Can compiled with two or more input types");
            return None; // short-circuit, ambiguous inferrence
        } else if compiled {
            inferred = Some(ty.clone());
        }
    }

    inferred
}
