use super::*;
use std::iter::once;
use tygraph::Chg::*;

impl<'d> Compiler<'d> {
    pub fn infer_inputs(&mut self) -> Result<bool> {
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
            match input_via_block_compilation(op, &self) {
                Ok(ty) => chgs.push(InferInput(op.idx(), ty.clone())),
                Err(e) => err = Some(e.crate_err(op.blk_tag(&self.ag))),
            }
        }

        match err {
            Some(e) if chgs.is_empty() => Err(e),
            _ => Ok(self.apply_graph_chgs(chgs.into_iter().map(Into::into))),
        }
    }

    fn infer_inputs_tgt_shallow_expr(&mut self) -> Result<bool> {
        if self.inferrence_depth > 5 {
            panic!("reached inferrence depth");
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

        dbg!(&infer_nodes);

        let mut success = false;
        let mut err = None;

        for expr in infer_nodes {
            // replace a dummy compiler value
            let this = self.take();
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

    pub fn infer_outputs(&mut self) -> bool {
        if let Some(opnode) = self.output_infer_opnode.take() {
            // replace a dummy compiler value
            let this = self.take();
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

    // take a clone of this compiler, replacing it with a dummy
    fn take(&mut self) -> Self {
        std::mem::replace(
            self,
            Compiler {
                ag: Default::default(),
                tg: Default::default(),
                lg: Default::default(),
                compiled_ops: Default::default(),
                compiled_exprs: Default::default(),
                output_infer_opnode: Default::default(),
                flowed_edges: Default::default(),
                callsite_params: Default::default(),
                defs: self.defs,
                inferrence_depth: 0,
            },
        )
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

    eprintln!(
        "Inferring input for {}",
        compiler.ag()[op.idx()].op().unwrap().1.str()
    );

    for (_name, ty) in types {
        eprintln!("🔬 Testing compilation with inferred input: {}", _name);

        let compiled = compiler
            .compile_block(op, ty.clone(), _sink1, _sink2)
            .is_ok();
        if compiled {
            eprintln!("🏁 Able to be compiled with input type: {}", _name);
        }

        match (compiled, inferred.take()) {
            (true, Some(ty1)) => {
                eprintln!("❌ FAILED -- Can compiled with two or more input types");
                return Err(Error::Ambiguous {
                    ty1,
                    ty2: ty.clone(),
                });
            }
            (true, None) => inferred = Some(ty.clone()),
            (false, x) => inferred = x,
        }
    }

    inferred.ok_or_else(|| Error::NoTypes)
}

fn input_via_expr_compilation(
    expr: ExprNode,
    compiler: Compiler,
) -> std::result::Result<Compiler, (Compiler, Error)> {
    // NOTE - the types are returned in arbitary order
    // if we wanted to make this deterministic we could sort on name
    let compiler_outer = compiler;
    let types = compiler_outer.defs.types().iter();

    let mut inferred = None;

    eprintln!("Inferring input for {}", expr.tag(compiler_outer.ag()));

    for (_name, ty) in types {
        eprintln!("🔬 Testing compilation with inferred input: {}", _name);

        // set the INPUT of the block to 'ty'
        let mut compiler = compiler_outer.clone();
        compiler.apply_graph_chgs(once(InferInput(expr.idx(), ty.clone()).into()));

        compiler.inferrence_depth += 1;

        // recurse into compile call -- breaking when the op gets compiled
        match compiler.compile(expr) {
            Ok(c) => {
                eprintln!("🏁 Able to be compiled with input type: {}", _name);
                match inferred.take() {
                    Some((ty1, _)) => {
                        eprintln!("❌ FAILED -- Can compiled with two or more input types");
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
            Err(_) => (), // continue
        }
    }

    inferred
        .map(|(_, c)| c)
        .ok_or_else(|| (compiler_outer, Error::NoTypes))
}

fn output(op: OpNode, compiler: Compiler) -> std::result::Result<Compiler, Compiler> {
    // NOTE - the types are returned in arbitary order
    // if we wanted to make this deterministic we could sort on name
    let types = compiler.defs.types().iter();

    eprintln!(
        "Inferring output for {}",
        compiler.ag()[op.idx()].op().unwrap().1.str()
    );

    let parent = op.parent(compiler.ag());

    for (_name, ty) in types {
        eprintln!("🔬 Testing compilation with inferred output: {}", _name);

        // set the OUTPUT of the block to 'ty'
        let mut compiler = compiler.clone();
        let chgd = compiler.apply_graph_chgs(once(InferOutput(op.idx(), ty.clone()).into()));

        if !chgd {
            continue; // no point in trying to compile if nothing changed
        }

        // recurse into compile call -- breaking when the parent expr gets compiled
        match compiler.compile(parent) {
            Ok(compiler) => {
                eprintln!("🏁 Able to be compiled with output type: {}", _name);

                // break early, output inferring is greedy
                return Ok(compiler);
            }
            Err(_) => (), // continue
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
            // name the attempeted types
            // give a code example of type annotation
            Self::Ambiguous { ty1, ty2 } => crate::Error {
                cat: Category::Semantics,
                desc: "ambiguous inference. more than one input type can compile op".into(),
                traces: trace(blk, None),
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
        let opnode = self.node;

        let ret = self.tg[opnode.idx()]
            .output
            .ty()
            .or_else(|| {
                opnode
                    .next(&self.ag)
                    .map(|next| {
                        // there is a next block
                        // return if there is a known input type
                        self.tg[next.idx()].input.ty()
                    })
                    .unwrap_or_else(|| {
                        // there is no next block
                        // use the output of the parent expr
                        self.tg[opnode.parent(&self.ag).idx()].output.ty()
                    })
            })
            .cloned();

        if ret.is_none() {
            *self.infer_output = true;
        }

        ret
    }
}
