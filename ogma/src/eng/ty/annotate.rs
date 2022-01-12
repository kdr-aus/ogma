//! Module handling type _annotations_, human readable type information.

use lang::var::Locals;
use std::fmt;
use super::*;

struct Annotator<'a> {
    in_ty: Type,
    locals: &'a Locals,
    defs: &'a Definitions,
    block_tag: &'a Tag
}

fn annotate_argument(arg: &ast::Argument, annotator: Annotator) -> Result<String> {
    let (s,ty) = annotate_argument_inner(arg, annotator)?;
    Ok(format!("{}:{}", s, AnnotationDisplay(ty)))
}

fn annotate_argument_inner(arg: &ast::Argument, annotator: Annotator) -> Result<(String, Type)> {
    use ast::Argument::*;

    // TODO the Pound matching code is repetitive with arg_recursive,
    // Work out how to generalise this.
    Ok(match arg {
        Ident(ident) => (ident.to_string(), Type::Str),
        Num(_num, tag) => (tag.to_string(), Type::Num),
        Pound('t', tag) => (tag.to_string(), Type::Bool),
        Pound('f', tag) => (tag.to_string(), Type::Bool),
        Pound('n', tag) => (tag.to_string(), Type::Nil),
        Pound('i', tag) => (tag.to_string(), annotator.in_ty),
        Pound(ch, tag) => return Err(Error::unknown_spec_literal(*ch, &tag)),
            Var(var) => {
                let ty = match annotator.locals
                    .get(var.str())
                    .ok_or_else(|| Error::var_not_found(&var))?
                {
                    Local::Param(arg, _) => {
                            annotate_argument_inner(arg, annotator)
                            .map_err(|e| e.add_trace(&var))?.1
                    }
                    Local::Var(v) => {
                        v.ty().clone()
                    }
                };
                        (format!("${}", var), ty)
            }
        Expr(expr) => {
            let Annotator { in_ty, block_tag, defs, locals } = annotator;
            let eval = Evaluator::construct(in_ty, expr.clone(), defs, locals.clone())
                    .map_err(|e| e.add_trace(block_tag))?;
            let oty = eval.ty().clone();

            ("expr".to_string(), oty)
        }
        x => todo!(),
    })
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
        let annotator = Annotator {
            in_ty: Type::Tab,
            defs: &Definitions::default(),
            locals: &Locals::default(),
            block_tag: &tag(""),
        };
        annotate_argument(&arg, annotator).unwrap()
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

            annotate_argument(&arg, annotator).unwrap()
        };

        assert_eq!(aa(Var(tag("foo"))), "$foo:Nil");
        assert_eq!(aa(Var(tag("a-d"))), "$a-d:Bool");
        assert_eq!(aa(Var(tag("param"))), "$param:Num");
    }
}
