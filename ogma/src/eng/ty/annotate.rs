//! Module handling type _annotations_, human readable type information.

use super::*;
use std::{borrow::Cow, fmt};

impl Type {
    pub fn fmt_annotation(&self) -> Display {
        Display(self)
    }
}

impl Argument {
    /// Annotate this argument with type information.
    pub fn type_annotation(&self) -> Cow<'_, str> {
        match &self.hold {
            Hold::Expr(evaluator) => return evaluator.type_annotation().into(),
            Hold::Lit(_) => if self.tag.str().is_empty() {
                format!("'':{}", self.out_ty.fmt_annotation())
            } else {
                format!("{}:{}", self.tag, self.out_ty.fmt_annotation())
            }
            .into(),
            Hold::Var(_) => format!("${}:{}", self.tag, self.out_ty.fmt_annotation()).into(),
        }
    }
}

struct Annotator<'a> {
    in_ty: Type,
    locals: &'a Locals,
    defs: &'a Definitions,
    block_tag: &'a Tag,
}

impl Clone for Annotator<'_> {
    fn clone(&self) -> Self {
        Self {
            in_ty: self.in_ty.clone(),
            locals: self.locals,
            defs: self.defs,
            block_tag: self.block_tag,
        }
    }
}

/// Formatter for [`Type`] annonations.
pub struct Display<'a>(pub &'a Type);

impl fmt::Display for Display<'_> {
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
        let annotator = Annotator {
            in_ty: Type::Tab,
            defs: &Definitions::default(),
            locals: &Locals::default(),
            block_tag: &tag(""),
        };
        argument(&arg, annotator).unwrap()
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

    #[test]
    fn annotate_var() {
        let mut locals = Locals::default();
        locals.add_new_var("foo".into(), Type::Nil, tag("#foo"));
        locals.add_new_var("a-d".into(), Type::Bool, tag("#a-d"));
        locals.add_param("param".into(), Num(10.into(), tag("10")), locals.clone());

        let aa = |arg| {
            let annotator = Annotator {
                in_ty: Type::Tab,
                defs: &Definitions::default(),
                locals: &locals,
                block_tag: &tag(""),
            };

            argument(&arg, annotator).unwrap()
        };

        assert_eq!(aa(Var(tag("foo"))), "$foo:Nil");
        assert_eq!(aa(Var(tag("a-d"))), "$a-d:Bool");
        assert_eq!(aa(Var(tag("param"))), "$param:Num");
    }

    #[test]
    fn annotate_expr() {
        let pe = |s: &str| {
            lang::syntax::parse::expression(s, Default::default(), &Default::default()).unwrap()
        };

        assert_eq!(aa(Expr(pe("ls"))), "{:Table ls }:Table");
        assert_eq!(aa(Expr(pe("ls | filter foo < 3"))), "{:Table ls }:Table");
    }
}
