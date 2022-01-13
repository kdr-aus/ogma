//! Module handling type _annotations_, human readable type information.

use super::*;
use ast::IBlock;
use lang::var::Locals;
use std::fmt;

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

fn argument(arg: &ast::Argument, annotator: Annotator) -> Result<String> {
    let (s, ty) = argument_inner(arg, annotator)?;
    Ok(format!("{}:{}", s, AnnotationDisplay(&ty)))
}

fn argument_inner(arg: &ast::Argument, annotator: Annotator) -> Result<(String, Type)> {
    use ast::Argument::*;

    dbg!(arg, &annotator.in_ty);

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
            let ty = match annotator
                .locals
                .get(var.str())
                .ok_or_else(|| Error::var_not_found(&var))?
            {
                Local::Param(arg, _) => {
                    argument_inner(arg, annotator)
                        .map_err(|e| e.add_trace(&var))?
                        .1
                }
                Local::Var(v) => v.ty().clone(),
            };
            (format!("${}", var), ty)
        }
        Expr(expr) => {
            let eval = Evaluator::construct(
                annotator.in_ty.clone(),
                expr.clone(),
                annotator.defs,
                annotator.locals.clone(),
            )
            .map_err(|e| e.add_trace(annotator.block_tag))?;
            let oty = eval.ty().clone();
            let text = expression(expr, &eval, annotator)?;

            (text, oty)
        }
        x => todo!(),
    })
}

fn expression(
    expr: &ast::Expression,
    evaluator: &Evaluator,
    mut annotator: Annotator,
) -> Result<String> {
    let mut s = format!("{{:{} ", AnnotationDisplay(&annotator.in_ty));

    for (blk, step) in expr.blocks.iter().zip(evaluator.steps()) {
        s.push_str(&block(blk, &annotator)?);
        s.push(' ');
    }

    s.push('}');

    Ok(s)
}

fn block(blk: &ast::Block, annotator: &Annotator) -> Result<String> {
    let mut op = blk.op().str().to_string();

    for arg in blk.terms().iter().filter_map(|term| match term {
        ast::Term::Arg(arg) => Some(arg),
        _ => None,
    }) {
        op.push(' ');
        op.push_str(&argument(arg, annotator.clone())?);
    }

    Ok(op)
}

struct AnnotationDisplay<'a>(&'a Type);

impl fmt::Display for AnnotationDisplay<'_> {
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
