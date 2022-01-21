//! Module handling type _annotations_, human readable type information.

use super::*;
use std::{borrow::Cow, fmt};

impl Type {
    /// Display this type for type annotation.
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
