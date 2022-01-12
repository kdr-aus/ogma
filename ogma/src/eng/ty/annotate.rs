//! Module handling type _annotations_, human readable type information.

use crate::prelude::*;
use std::fmt;

fn annotate_argument(arg: &ast::Argument, in_ty: Type) -> Result<String> {
    use ast::Argument::*;

    // TODO the Pound matching code is repetitive with arg_recursive,
    // Work out how to generalise this.
    let (tag, out_ty) = match arg {
        Ident(ident) => (ident, Type::Str),
        Num(_num, tag) => (tag, Type::Num),
        Pound('t', tag) => (tag, Type::Bool),
        Pound('f', tag) => (tag, Type::Bool),
        Pound('n', tag) => (tag, Type::Nil),
        Pound('i', tag) => (tag, in_ty),
        Pound(ch, tag) => return Err(Error::unknown_spec_literal(*ch, &tag)),
        x => todo!(),
    };

    Ok(format!("{}:{}", tag, AnnotationDisplay(out_ty)))
}

struct AnnotationDisplay(Type);

impl fmt::Display for AnnotationDisplay {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Type::*;

        let x = match &self.0 {
            Nil => "Nil",
            Bool => "Bool",
            Num => "Num",
            Str => "Str",
            Tab => "Table",
            TabRow => "TableRow",
            Def(d) => d.name().str(),
        };

        write!(f, "{}", x)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ast::{Argument::*, *};

    fn aa(arg: ast::Argument) -> String {
        annotate_argument(&arg, Type::Tab).unwrap()
    }

    fn tag(s: &str) -> Tag {
        Tag {
            anchor: Location::Shell,
            line: s.to_string().into(),
            start: 0,
            end: s.len(),
        }
    }

    #[test]
    fn annotate_ident() {
        assert_eq!(aa(Ident(tag("foo-bar"))), "foo-bar:Str");
    }

    #[test]
    fn annotate_number() {
        assert_eq!(aa(Num(1.into(), tag("1.0"))), "1.0:Num");
    }

    #[test]
    fn annotate_literal() {
        assert_eq!(aa(Pound('t', tag("#t"))), "#t:Bool");
        assert_eq!(aa(Pound('f', tag("#f"))), "#f:Bool");
        assert_eq!(aa(Pound('n', tag("#n"))), "#n:Nil");
        assert_eq!(aa(Pound('i', tag("#i"))), "#i:Table");
    }
}
