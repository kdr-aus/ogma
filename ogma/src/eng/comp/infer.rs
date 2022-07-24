use super::*;
use petgraph::prelude::NodeIndex;
use std::iter::once;
use tygraph::Chg::*;

impl<'d> Compiler<'d> {
    /// Infer inputs into _blocks_.
    ///
    /// This is generally faster and is NOT recursive.
    pub fn infer_inputs_block(self: &mut Box<Self>) -> Result<bool> {
        self.infer_inputs_tgt_ops()
    }

    /// Infer inputs into _expressions_.
    ///
    /// This is slow and recurses, which could be problematic.
    pub fn infer_inputs_expr(self: &mut Box<Self>) -> Result<bool> {
        self.infer_inputs_tgt_shallow_expr()
    }

    fn infer_inputs_tgt_ops(&mut self) -> Result<bool> {
        // we get _lowest_ nodes that are:
        // 1. Op variants,
        // 2. are not compiled,
        // 3. have unknown inputs
        let infer_nodes = self.ag.sinks(|n| {
            // 1. op variants
            self.ag[n].op().is_some() &&
            // 2. not compiled
            !self.compiled_ops.contains_key(&n.index()) &&
            // 3. has multiple valid types
            self.tg[n].input.is_multiple()
        });

        let mut chgs = Vec::new();

        // TODO
        // I see a few issues with this type of ineference
        // 1. It tries all types, it should only try the types reduced in the set
        // 2. Compilation failure does not mean invalid type, failure could occurs because of some
        //    other requirement (think unsealed variables)
        // 3. If compilation failure were to ditctate the type to use, we could just reduce the
        //    types set even further, rather than going through ambiguous error typing.

        for op in infer_nodes.into_iter().map(OpNode) {
            trial_inferred_types(op, self, &mut chgs);
        }

        self.apply_graph_chgs(chgs.into_iter().map(Into::into))
    }

    fn infer_inputs_tgt_shallow_expr(self: &mut Box<Self>) -> Result<bool> {
        self.assert_inference_depth();

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
            let x = input_via_expr_compilation(expr, self);

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

    /// Infer the outputs with the current compiler state.
    pub fn infer_outputs(self: &mut Box<Self>) -> Result<bool> {
        self.assert_inference_depth();

        if let Some(opnode) = self
            .output_infer_opnode
            // TAKE the infer node, since we are processing it.
            .take()
            // BUT do not process if the output is NOT unknown
            .filter(|n| self.tg[n.idx()].output.is_unknown())
        {
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

    fn assert_inference_depth(&self) {
        if self.inference_depth > 5 {
            panic!("reached inference depth; this is an internal error, please raise an issue at <https://github.com/kdr-aus/ogma/issues>");
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
    // TODO this should be changed to use the nodes inferred types, not all types
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

/// Tries to compile the `op` with each type in the inferred types set.
/// Unsuccesful compilations will add a `RemoveInput` change into the `chgs`.
fn trial_inferred_types(op: OpNode, compiler: &Compiler, chgs: Chgs) {
    let _sink1 = &mut Default::default();
    let _sink2 = &mut Default::default();

    let set = compiler.tg[op.idx()]
        .input
        .tys()
        .expect("`op` is expected to be an inferred input node with multiple types");

    for ty in set.iter() {
        let compiled = compiler
            .compile_block(op, ty.clone(), _sink1, _sink2)
            .is_ok();

        if !compiled {
            chgs.push(RemoveInput(op.into(), ty.clone()).into());
        }
    }
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
    let ag = compiler.ag();
    let brk = op.parent(ag);
    //     let brk = brk.parent(ag).map(|x| x.parent(ag)).unwrap_or(brk);

    test_compile_types(compiler, op.idx(), brk, true)
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
