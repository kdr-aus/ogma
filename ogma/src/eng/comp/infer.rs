use super::*;
use petgraph::prelude::NodeIndex;
use std::iter::once;
use tygraph::{Chg::*, TypesSet};

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
        // we get _deepest_ nodes that are:
        // 1. Op variants,
        // 2. are not compiled,
        // 3. have multiple inputs
        // 4. is sealed, or contains no variables
        let infer_nodes = self.ag.sinks(|n| {
            // 1. op variants
            self.ag[n].op().is_some() &&
            // 2. not compiled
            !self.compiled_ops.contains_key(&n.index()) &&
            // 3. has multiple valid types
            self.tg[n].input.is_multiple() &&
            // 4. is sealed, or contains no variables
            (self.lg.sealed(n) || !self.ag.detect_var(OpNode(n)))
        });

        let mut chgs = Vec::default();

        for op in infer_nodes.into_iter().map(OpNode) {
            trial_inferred_types(op, self, &mut chgs);
        }

        self.apply_graph_chgs(chgs.into_iter())
    }

    fn infer_inputs_tgt_shallow_expr(self: &mut Box<Self>) -> Result<bool> {
        self.assert_inference_depth()?;

        // we get _shallowest_ expr nodes that:
        // 1. are not compiled,
        // 2. have multiple input
        let infer_nodes = {
            let set = self
                .ag
                .expr_nodes()
                // are not compiled
                .filter(|n| !self.compiled_exprs.contains_key(&n.index()))
                // have multiple input
                .filter(|n| self.tg[n.idx()].input.is_multiple())
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
        let mut chgs = Vec::new();

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
                Err(Error::Reduce(ts)) => chgs.extend(
                    ts.into_iter()
                        .map(|t| tygraph::Chg::RemoveInput(expr.idx(), t).into()),
                ),
                Err(e) => {
                    let d = e.is_depth_limit();
                    let e = e.input_expr(expr.tag(self.ag()));
                    if d {
                        // if the error is a depth limit, need to short circuit and propagate upwards
                        return Err(e);
                    } else {
                        // else, bring back compiler, and set err
                        err = Some(e)
                    }
                }
            }
        }

        if success {
            Ok(true) // at least one trial worked
        } else if !chgs.is_empty() {
            self.apply_graph_chgs(chgs.into_iter())
        } else {
            match err {
                Some(e) => Err(e),
                None => Ok(false), // no errors, but no success
            }
        }
    }

    /// Infer the outputs with the current compiler state.
    pub fn infer_outputs(self: &mut Box<Self>) -> Result<bool> {
        self.assert_inference_depth()?;

        let nodes: Vec<_> = {
            let x = &mut self.output_infer_opnodes;
            // notice the reverse comparison, we do this to get a descending order, trialling the
            // 'deepest' first
            x.sort_unstable_by_key(|a| std::cmp::Reverse(a.index()));
            x.dedup();

            // only take where the output is ambiguous
            x.drain(..)
                .filter(|n| self.tg[n.idx()].output.is_multiple())
                .collect()
        };

        // This code mimics the inputs, but has enough differing calls to not be abstracted
        let mut success = false;
        let mut err = None;
        let mut chgs = Vec::new();

        for opnode in nodes {
            // infer output
            let x = output(opnode, self);

            match x {
                // success!
                Ok(c) => {
                    success = true;
                    *self = c; // update self with new compiler
                    break; // return early
                }
                Err(Error::Reduce(ts)) => chgs.extend(
                    ts.into_iter()
                        .map(|t| tygraph::Chg::RemoveOutput(opnode.idx(), t).into()),
                ),
                Err(e) => {
                    let d = e.is_depth_limit();
                    let e = e.output(opnode.op_tag(self.ag()), opnode.blk_tag(self.ag()));
                    if d {
                        // if the error is a depth limit, need to short circuit and propagate upwards
                        return Err(e);
                    } else {
                        // else, bring back compiler, and set err
                        err = Some(e);
                    }
                }
            }
        }

        if success {
            Ok(true) // at least one trial worked
        } else if !chgs.is_empty() {
            self.apply_graph_chgs(chgs.into_iter())
        } else {
            match err {
                Some(e) => Err(e),
                None => Ok(false), // no errors, but no success
            }
        }
    }

    fn assert_inference_depth(&self) -> Result<()> {
        (self.inference_depth < 5)
            .then_some(())
            .ok_or_else(crate::Error::inference_depth)
    }
}

enum Error {
    NoTypes,
    Ambiguous(TypesSet),
    DepthLimit(crate::Error),
    Reduce(Vec<Type>),
}

/// Tries to compile the `op` with each type in the inferred types set.
/// Pushes `RemoveInput` if failed.
fn trial_inferred_types(op: OpNode, compiler: &Compiler, chgs: &mut Vec<graphs::Chg>) {
    let mut sink1 = Default::default();

    let set = compiler.tg[op.idx()]
        .input
        .tys()
        .expect("`op` is expected to be an inferred input node with multiple types");

    let failed = set
        .iter()
        .cloned()
        .filter(|ty| {
            let mut chgs = Chgs {
                chgs: std::mem::take(&mut sink1),
                ..Chgs::default()
            };

            let compiled = compiler.compile_block(op, ty.clone(), &mut chgs).is_ok();

            let Chgs {
                chgs,
                infer_output,
                adds_vars: _,
            } = chgs;
            sink1 = chgs;

            let lg_chg_req = sink1.drain(..).any(|chg| chg.is_lg_chg());

            // remove input if failed compilation, and
            // does not infer output
            // we keep in if infer_output is true, since we need more information about types
            // before we can compile this block, and removing input inferences will just reduce it
            // to an empty set.
            !compiled && !infer_output && !lg_chg_req
        })
        .map(|ty| RemoveInput(op.into(), ty))
        .map(Into::into);

    chgs.extend(failed)
}

fn input_via_expr_compilation<'a>(
    expr: ExprNode,
    compiler: &Compiler_<'a>,
) -> std::result::Result<Compiler_<'a>, Error> {
    // NOTE: I believe this should break on success compilation of parent expr, not itself??
    // seem to be passing tests with this so keep it so...
    test_compile_types(compiler, expr.idx(), expr, false)
}

fn output<'a>(op: OpNode, compiler: &Compiler_<'a>) -> std::result::Result<Compiler_<'a>, Error> {
    let brk = op.parent(compiler.ag());

    test_compile_types(compiler, op.idx(), brk, true)
}

fn test_compile_types<'a>(
    compiler: &Compiler_<'a>,
    node: NodeIndex,
    breakon: ExprNode,
    output: bool,
) -> std::result::Result<Compiler_<'a>, Error> {
    let types = if output {
        compiler.tg()[node].output.tys()
    } else {
        compiler.tg()[node].input.tys()
    }
    .expect("only testing inferred types set");

    let mut validset = types.clone();
    let mut rm = Vec::new();

    let mut inferred = None;

    for ty in types.iter() {
        let mut compiler: Compiler_ = compiler.clone();
        compiler.inference_depth += 1;

        let chg = if output {
            ObligeOutput(node, ty.clone())
        } else {
            ObligeInput(node, ty.clone())
        };

        let x = compiler.apply_graph_chgs(once(chg.into()));

        let x = match x {
            Ok(x) => {
                debug_assert!(x, "expecting a change to actually occur");
                compiler.compile(breakon)
            }
            Err(_) => {
                rm.push(ty.clone());
                continue;
            }
        };

        match (x, inferred.take()) {
            // success; but there was another success
            (Ok(_), Some(_)) => return Err(Error::Ambiguous(validset)),
            // success, first one, set the return
            (Ok(c), None) => inferred = Some(c),
            // a bubbled up depth error, propagate upwards
            (Err(e), _) if e.is_inference_depth_error() => return Err(Error::DepthLimit(e)),
            // upon error we reduce the types set to help with error reporting
            (Err(_), x) => {
                validset.remove(ty);
                inferred = x;
            }
        }
    }

    match (inferred, rm.is_empty()) {
        (Some(x), _) => Ok(x),
        // rm is NOT empty
        (None, false) => Err(Error::Reduce(rm)),
        (None, true) => Err(Error::NoTypes),
    }
}

impl Error {
    fn is_depth_limit(&self) -> bool {
        matches!(self, Self::DepthLimit(_))
    }

    fn output(self, op: &Tag, blk_tag: &Tag) -> crate::Error {
        use crate::common::err::*;

        let (xtag, x) = if op.str() == "." {
            (
                blk_tag,
                format!("try annotating output type: `{blk_tag}:<type>`"),
            )
        } else {
            (op, format!("try annotating output type: `{op}:<type> ...`"))
        };

        match self {
            Self::NoTypes => crate::Error {
                cat: Category::Semantics,
                desc: "no output types suit compiling this op".into(),
                traces: trace(op, x),
                ..Default::default()
            },
            Self::Ambiguous(set) => crate::Error {
                cat: Category::Semantics,
                desc: "ambiguous inference. more than one output type can compile op".into(),
                traces: vec![
                    Trace::from_tag(
                        op,
                        format!("this op can be compiled with output types: {set}"),
                    ),
                    Trace::from_tag(xtag, x),
                ],
                ..Default::default()
            },
            Self::DepthLimit(e) => {
                Self::add_trace(e, op, "trying to infer output for this command")
            }
            Self::Reduce(_) => unreachable!("handle before calling this"),
        }
    }

    fn input_expr(self, expr: &Tag) -> crate::Error {
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
            Self::Ambiguous(set) => crate::Error {
                cat: Category::Semantics,
                desc: "ambiguous inference. more than one input type can compile expression".into(),
                traces: vec![
                    Trace::from_tag(
                        expr,
                        format!("this expression can be compiled with input types: {set}"),
                    ),
                    Trace::from_tag(expr, x),
                ],
                ..Default::default()
            },
            Self::DepthLimit(e) => {
                Self::add_trace(e, expr, "annotate the input type for this expression")
            }
            Self::Reduce(_) => unreachable!("handle before calling this"),
        }
    }

    /// we do a bit of jiggering the trace vector here.
    /// the reason is this, the _deepest_ inference error is not usually the best
    /// one to annotate, rather, the _first_ node which fails (effectively the root
    /// invoker of the inference chain) should be the one annotated.
    /// to provide good error messages, the _last_ in the bubbling should be the
    /// _first_ displayed.
    /// So we take the head from the trace list, copy the message, set the old
    /// message to be just a trace stack message, and we will end up with the
    /// shallowest node on top
    fn add_trace(mut e: crate::Error, tag: &Tag, msg: impl Into<String>) -> crate::Error {
        if e.traces.is_empty() {
            e.add_trace(tag, msg.into())
        } else {
            let prv = &mut e.traces[0];
            let m = prv.desc.take();
            prv.desc = Some("sub-inferencing failed".to_string());
            let t = crate::common::err::Trace::from_tag(tag, m);
            e.traces.insert(0, t);
            e
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
            chgs: Chgs { infer_output, .. },
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
            *infer_output = true;
        }

        ret
    }
}
