//! Module handling type _annotations_, human readable type information.
use super::*;
use graphs::{astgraph::*, *};
use std::fmt::{self, Write};

pub fn types(blk: &Block, arg: graphs::ArgNode, verbose: bool) -> String {
    let mut s = String::new();
    fmt(&mut s, blk, arg.idx(), verbose);
    s
}

fn fmt(s: &mut String, blk: &Block, node: petgraph::prelude::NodeIndex, v: bool) {
    use AstNode::*;

    let Block {
        compiler: Compiler { ag, tg, .. },
        ..
    } = blk;

    let out_ty = tg[node].output.ty();

    match &ag[node] {
        Ident(t) => {
            if t.str().is_empty() {
                write!(s, "''")
            } else {
                write!(s, "{}", t)
            }
            .unwrap();
            if v {
                fmt_ty(s, out_ty)
            }
        }
        Num { val: _, tag } => {
            write!(s, "{}", tag).unwrap();
            if v {
                fmt_ty(s, out_ty)
            }
        }
        Pound { ty: _, tag } => {
            write!(s, "{}", tag).unwrap();
            fmt_ty(s, out_ty)
        }
        Var(t) => {
            write!(s, "${}", t).unwrap();
            fmt_ty(s, out_ty)
        }
        Expr(_) => {
            write!(s, "{{").unwrap();

            let op = ExprNode(node).first_op(ag); // get the first op
            fmt_op(s, blk, op, v); // recurse into the formatter with first op

            write!(s, " }}").unwrap();
            fmt_ty(s, out_ty)
        }
        Op { op: _, blk: _, within: _ } => fmt_op(s, blk, OpNode(node), v),
        Def { .. } | Intrinsic { .. } | Flag { .. } => unreachable!(),
    }
}

fn fmt_op(s: &mut String, blk: &Block, op: OpNode, v: bool) {
    let Block {
        compiler: Compiler { ag, tg, .. },
        ..
    } = blk;

    let out_ty = tg[op.idx()].output.ty();
    let in_ty = tg[op.idx()].input.ty();

    // fmt as - ':IN op:OUT'
    // if not verbose, leave the trailing out
    fmt_ty(s, in_ty);
    write!(s, " {}", op.op_tag(ag)).unwrap();
    if v {
        fmt_ty(s, out_ty);
    }

    // obtain the path taken
    let args = in_ty
        .and_then(|t| ag.get_impl(op, t))
        .map(|cmd| ag.get_args(cmd))
        .unwrap_or_default();

    for arg in args {
        s.push(' '); // leading space
        fmt(s, blk, arg.idx(), v); // recurse to format arg
    }

    if let Some(next) = op.next(ag) {
        // there's a next block
        write!(s, " |").unwrap();
        fmt_op(s, blk, next, v); // recurse into next op
    }
}

fn fmt_ty(s: &mut String, t: Option<&Type>) {
    match t {
        Some(t) => write!(s, ":{}", t.fmt_annotation()),
        None => write!(s, ":?"),
    }
    .unwrap()
}

impl Type {
    /// Display this type for type annotation.
    pub fn fmt_annotation(&self) -> Display {
        Display(self)
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
