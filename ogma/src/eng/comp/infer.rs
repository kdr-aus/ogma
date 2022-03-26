use super::*;
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
                Err(e) => err = Some(e.crate_err(op.blk_tag(&self.ag))),
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
            // replace a dummy compiler value
            let this = take(self);
            // infer input
            let x = input_via_expr_compilation(expr, this);

            match x {
                // success!
                Ok(c) => {
                    success = true;
                    *self = c; // update self with new compiler
                    break; // return early
                }
                // else, bring back compiler, and set err
                Err((c, e)) => {
                    err = Some(e.crate_err(expr.tag(&c.ag)));
                    *self = c; // overwrite dummy self
                }
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

    pub fn infer_outputs(self: &mut Box<Self>) -> bool {
        if let Some(opnode) = self.output_infer_opnode.take() {
            // replace a dummy compiler value
            let this = take(self);
            // infer output
            let x = output(opnode, this);
            // store if we were successful
            let success = x.is_ok();
            // bring back the compiler to self, throw out the dummy
            *self = x.unwrap_or_else(|c| c);
            // return the inferring result
            success
        } else {
            false
        }
    }
}

// take a clone of this compiler, replacing it with a dummy
fn take<'a>(this: &mut Compiler_<'a>) -> Compiler_<'a> {
    std::mem::replace(
        this,
        Box::new(Compiler {
            ag: Default::default(),
            tg: Default::default(),
            lg: Default::default(),
            compiled_ops: Default::default(),
            compiled_exprs: Default::default(),
            output_infer_opnode: Default::default(),
            flowed_edges: Default::default(),
            callsite_params: Default::default(),
            defs: this.defs,
            inference_depth: 0,
        }),
    )
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

        match (compiled, inferred.take()) {
            (true, Some(ty1)) => {
                return Err(Error::Ambiguous {
                    ty1,
                    ty2: ty.clone(),
                });
            }
            (true, None) => inferred = Some(ty.clone()),
            (false, x) => inferred = x,
        }
    }

    inferred.ok_or(Error::NoTypes)
}

fn input_via_expr_compilation(
    expr: ExprNode,
    compiler: Compiler_,
) -> std::result::Result<Compiler_, (Compiler_, Error)> {
    // NOTE - the types are returned in arbitary order
    // if we wanted to make this deterministic we could sort on name
    let compiler_outer = compiler;
    let types = compiler_outer.defs.types().iter();

    let mut inferred = None;

    for (_name, ty) in types {
        // set the INPUT of the block to 'ty'
        let mut compiler: Compiler_ = compiler_outer.clone();
        compiler.inference_depth += 1;

        let x = compiler
            .apply_graph_chgs(once(InferInput(expr.idx(), ty.clone()).into()))
            // recurse into compile call -- breaking when the parent expr gets compiled
            .and_then(|_| compiler.compile(expr));

        if let Ok(c) = x {
            match inferred.take() {
                Some((ty1, _)) => {
                    return Err((
                        compiler_outer,
                        Error::Ambiguous {
                            ty1,
                            ty2: ty.clone(),
                        },
                    ));
                }
                None => inferred = Some((ty.clone(), c)),
            }
        }
    }

    inferred
        .map(|(_, c)| c)
        .ok_or((compiler_outer, Error::NoTypes))
}

fn output(op: OpNode, compiler: Compiler_) -> std::result::Result<Compiler_, Compiler_> {
    // NOTE - the types are returned in arbitary order
    // if we wanted to make this deterministic we could sort on name
    let types = compiler.defs.types().iter();

    let parent = op.parent(compiler.ag());

    for (_name, ty) in types {
        // set the OUTPUT of the block to 'ty'
        let mut compiler: Compiler_ = compiler.clone();

        let x = compiler
            .apply_graph_chgs(once(InferOutput(op.idx(), ty.clone()).into()))
            // recurse into compile call -- breaking when the parent expr gets compiled
            .and_then(|_| compiler.compile(parent));

        if let Ok(compiler) = x {
            // break early, output inferring is greedy
            return Ok(compiler);
        }
    }

    Err(compiler) // no luck, return the unaltered compiler
}

impl Error {
    pub fn crate_err(&self, blk: &Tag) -> crate::Error {
        use crate::common::err::*;

        match self {
            Self::NoTypes => crate::Error {
                cat: Category::Semantics,
                desc: "op does not compile with any known types".into(),
                traces: trace(blk, None),
                help_msg: Some("try specifying input type to the block".into()),
                ..Default::default()
            },
            // TODO make this error better,
            // give a code example of type annotation
            Self::Ambiguous { ty1, ty2 } => crate::Error {
                cat: Category::Semantics,
                desc: "ambiguous inference. more than one input type can compile op".into(),
                traces: trace(
                    blk,
                    format!("this can be compiled with `{}` and `{}`", ty1, ty2),
                ),
                help_msg: Some("try specifying input type to the block".into()),
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
