//! Module handling type _annotations_, human readable type information.

use crate::prelude::*;

pub fn annotate_expression(arg: &ast::Argument) -> String {
    use ast::Argument::*;

    match arg {
        Ident(ident) => {
            format!("{}:Str", ident)
        }
        Num(_num, tag) => {
            format!("{}:Num", tag)
        }
        x => todo!(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use annotate_expression as ae;
    use ast::{Argument::*, *};

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
        assert_eq!(ae(&Ident(tag("foo-bar"))), "foo-bar:Str");
    }

    #[test]
    fn annotate_number() {
        assert_eq!(ae(&Num(1.into(), tag("1.0"))), "1.0:Num");
    }
}
