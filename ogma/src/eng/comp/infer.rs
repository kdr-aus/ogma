use super::*;
use petgraph::prelude::NodeIndex;
use std::iter::once;
use tygraph::Chg::*;

impl<'d> Compiler<'d> {
    pub fn infer_inputs(self: &mut Box<Self>) -> Result<bool> {
        // use the targeted ops inferring method
        let success = self.infer_inputs_tgt_ops();
        if success.is_ok() {
            return success;
        }

        self.infer_inputs_tgt_shallow_expr()
    }

    fn infer_inputs_tgt_ops(&mut self) -> Result<bool> {
        // we get _lowest_ nodes that are:
        // 1. Op variants,
        // 2. are not compiled,
        // 3. have unknown inputs
        let infer_nodes = self.ag.sinks(|n| {
            // 1. op variants
            self.ag[n].op().is_some()
            // 2. not compiled
            && !self.compiled_ops.contains_key(&n.index())
            // 3. unknown input
            && self.tg[n].input.is_unknown()
        });

        let mut err = None;
        let mut chgs = Vec::new();

        for op in infer_nodes.into_iter().map(OpNode) {
            match input_via_block_compilation(op, self) {
                Ok(ty) => chgs.push(InferInput(op.idx(), ty.clone())),
                Err(e) => err = Some(e.input_op(op.blk_tag(self.ag()))),
            }
        }

        match err {
            Some(e) if chgs.is_empty() => Err(e),
            _ => self.apply_graph_chgs(chgs.into_iter().map(Into::into)),
        }
    }

    fn infer_inputs_tgt_shallow_expr(self: &mut Box<Self>) -> Result<bool> {
        if self.inference_depth > 5 {
            panic!("reached inference depth; this is an internal error, please raise an issue at <https://github.com/kdr-aus/ogma/issues>");
        }

        // we get _shallowest_ expr nodes that:
        // 1. are not compiled,
        // 2. have unknown input
        let infer_nodes = {
            let set = self
                .ag
                .expr_nodes()
                // are not compiled
                .filter(|n| !self.compiled_exprs.contains_key(&n.index()))
                // have unknown input
                .filter(|n| self.tg[n.idx()].input.is_unknown())
                .collect::<HashSet<_>>();

            set.iter()
                .copied()
                // get shallowest node if it shows up in path only once
                .filter(|n| {
                    self.ag
                        .path_from_root(n.idx())
                        .filter(|&n| set.contains(&ExprNode(n)))
                        .count()
                        == 1
                })
                .collect::<Vec<_>>()
        };

        let mut success = false;
        let mut err = None;

        for expr in infer_nodes {
            // infer input
            let x = input_via_expr_compilation(expr, &self);

            match x {
                // success!
                Ok(c) => {
                    success = true;
                    *self = c; // update self with new compiler
                    break; // return early
                }
                // else, bring back compiler, and set err
                Err(e) => err = Some(e.input_expr(expr.tag(self.ag()))),
            }
        }

        if success {
            Ok(true) // at least one trial worked
        } else {
            match err {
                Some(e) => Err(e),
                None => Ok(false), // no errors, but no success
            }
        }
    }

    pub fn infer_outputs(self: &mut Box<Self>) -> Result<bool> {
        if let Some(opnode) = self.output_infer_opnode.take() {
            // infer output
            let x = output(opnode, self);

            match x {
                Ok(c) => {
                    // bring back the compiler to self
                    *self = c;
                    Ok(true) // success
                }
                Err(e) => Err(e.output(opnode.op_tag(self.ag()))),
            }
        } else {
            Ok(false)
        }
    }
}

enum Error {
    NoTypes,
    Ambiguous { ty1: Type, ty2: Type },
}

fn input_via_block_compilation(
    op: OpNode,
    compiler: &Compiler,
) -> std::result::Result<Type, Error> {
    // NOTE - the types are returned in arbitary order
    // if we wanted to make this deterministic we could sort on name
    let types = compiler.defs.types().iter();

    let mut inferred = None;

    let _sink1 = &mut Default::default();
    let _sink2 = &mut Default::default();

    for (_name, ty) in types {
        let compiled = compiler
            .compile_block(op, ty.clone(), _sink1, _sink2)
            .is_ok();

        if compiled {
            match inferred.take() {
                Some(ty1) => {
                    return Err(Error::Ambiguous {
                        ty1,
                        ty2: ty.clone(),
                    });
                }
                None => inferred = Some(ty.clone()),
            }
        }
    }

    inferred.ok_or(Error::NoTypes)
}

fn input_via_expr_compilation<'a>(
    expr: ExprNode,
    compiler: &Compiler_<'a>,
) -> std::result::Result<Compiler_<'a>, Error> {
    //     let parent = expr.parent(compiler.ag());

    // NOTE: I believe this should break on success compilation of parent expr, not itself??
    // seem to be passing tests with this so keep it so...
    test_compile_types(compiler, expr.idx(), expr, false)
}

fn output<'a>(op: OpNode, compiler: &Compiler_<'a>) -> std::result::Result<Compiler_<'a>, Error> {
    test_compile_types(compiler, op.idx(), op.parent(compiler.ag()), true)
}

fn test_compile_types<'a>(
    compiler: &Compiler_<'a>,
    node: NodeIndex,
    breakon: ExprNode,
    output: bool,
) -> std::result::Result<Compiler_<'a>, Error> {
    // NOTE - the types are returned in arbitary order
    // if we wanted to make this deterministic we could sort on name
    let types = compiler.defs.types().iter();

    let mut inferred = None;

    for (_name, ty) in types {
        let mut compiler: Compiler_ = compiler.clone();
        compiler.inference_depth += 1;

        let chg = if output {
            InferOutput(node, ty.clone())
        } else {
            InferInput(node, ty.clone())
        };

        let x = compiler
            .apply_graph_chgs(once(chg.into()))
            .and_then(|_| compiler.compile(breakon));

        if let Ok(c) = x {
            match inferred.take() {
                Some((ty1, _)) => {
                    return Err(Error::Ambiguous {
                        ty1,
                        ty2: ty.clone(),
                    });
                }
                None => inferred = Some((ty.clone(), c)),
            }
        }
    }

    inferred.map(|(_, c)| c).ok_or(Error::NoTypes)
}

impl Error {
    pub fn output(&self, op: &Tag) -> crate::Error {
        use crate::common::err::*;

        let x = format!("try annotating output type: `{}:<type> ...`", op);

        match self {
            Self::NoTypes => crate::Error {
                cat: Category::Semantics,
                desc: "no output types suit compiling this op".into(),
                traces: trace(op, x),
                ..Default::default()
            },
            // TODO make this error better,
            // give a code example of type annotation
            Self::Ambiguous { ty1, ty2 } => crate::Error {
                cat: Category::Semantics,
                desc: "ambiguous inference. more than one output type can compile op".into(),
                traces: vec![
                    Trace::from_tag(
                        op,
                        format!(
                            "this op can be compiled with `{}` and `{}` as output types",
                            ty1, ty2
                        ),
                    ),
                    Trace::from_tag(op, x),
                ],
                ..Default::default()
            },
        }
    }

    pub fn input_op(&self, op: &Tag) -> crate::Error {
        use crate::common::err::*;

        let x = format!("try annotating input type: `{{:<type> {} ... }}`", op);

        match self {
            Self::NoTypes => crate::Error {
                cat: Category::Semantics,
                desc: "no input types suit compiling this op".into(),
                traces: trace(op, x),
                ..Default::default()
            },
            Self::Ambiguous { ty1, ty2 } => crate::Error {
                cat: Category::Semantics,
                desc: "ambiguous inference. more than one input type can compile op".into(),
                traces: vec![
                    Trace::from_tag(
                        op,
                        format!(
                            "this op can be compiled with `{}` and `{}` as input types",
                            ty1, ty2
                        ),
                    ),
                    Trace::from_tag(op, x),
                ],
                ..Default::default()
            },
        }
    }

    pub fn input_expr(&self, expr: &Tag) -> crate::Error {
        use crate::common::err::*;

        let x = {
            let t = expr.to_string();
            match t.strip_prefix('{') {
                Some(s) => format!("{{:<type> {}", s),
                None => format!("{{:<type> {} }}", t),
            }
        };

        match self {
            Self::NoTypes => crate::Error {
                cat: Category::Semantics,
                desc: "no input types suit compiling this expression".into(),
                traces: trace(expr, x),
                ..Default::default()
            },
            Self::Ambiguous { ty1, ty2 } => crate::Error {
                cat: Category::Semantics,
                desc: "ambiguous inference. more than one input type can compile expression".into(),
                traces: vec![
                    Trace::from_tag(
                        expr,
                        format!(
                            "this expression can be compiled with `{}` and `{}` as input types",
                            ty1, ty2
                        ),
                    ),
                    Trace::from_tag(expr, x),
                ],
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
        let Block {
            node: opnode,
            compiler: Compiler { ag, tg, .. },
            infer_output,
            ..
        } = self;

        let ret = tg[opnode.idx()]
            .output
            .ty()
            .or_else(|| {
                opnode
                    .next(ag)
                    .map(|next| {
                        // there is a next block
                        // return if there is a known input type
                        tg[next.idx()].input.ty()
                    })
                    .unwrap_or_else(|| {
                        // there is no next block
                        // use the output of the parent expr
                        tg[opnode.parent(ag).idx()].output.ty()
                    })
            })
            .cloned();

        if ret.is_none() {
            **infer_output = true;
        }

        ret
    }
}
