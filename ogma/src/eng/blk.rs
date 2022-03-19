use super::*;
use graphs::*;

impl<'a> Block<'a> {
    /// The operation (command) tag.
    pub fn op_tag(&self) -> &Tag {
        self.ag[self.node.idx()]
            .op()
            .expect("blocks node is an OP")
            .0
    }

    /// The entire block tag.
    pub fn blk_tag(&self) -> &Tag {
        self.ag[self.node.idx()]
            .op()
            .expect("blocks node is an OP")
            .1
    }

    /// Assert that this block will return the given type.
    ///
    /// Asserting an output type gives the type inferer knowledge about this block's output.
    /// It is recommended to assert this as soon as possible in the implementation, so if
    /// compilation fails, the output information is still captured.
    ///
    /// # Panics
    /// - For debug builds, panics if an output type has already been set on this block.
    /// Only a single assertion should be made in an implementation.
    /// - For debug builds, this assertion is checked against the evalulation output type.
    pub fn assert_output(&mut self, ty: Type) {
        #[cfg(debug_assertions)]
        {
            debug_assert!(
                self.output_ty.is_none(),
                "Block.output_ty cannot be set more than once"
            );
            self.output_ty = Some(ty.clone());
        }

        self.chgs
            .push(graphs::tygraph::Chg::KnownOutput(self.node.idx(), ty).into());
    }

    pub fn peek_next_arg_node(&self) -> Option<graphs::ArgNode> {
        self.args.last().copied()
    }

    /// Assert this argument is a variable and construct a reference to it.
    ///
    /// If the block does not contain a reference to an up-to-date locals, and error is returned.
    ///
    /// **Note** that the variable will be defined at the **_next_** block in the chain, not the
    /// current one.
    ///
    /// # Type safety
    /// The variable will be created expecting the type `ty`. `set_data` only validates types in
    /// debug builds, be sure that testing occurs of code path to avoid UB in release.
    pub fn create_var_ref(&mut self, arg: ArgNode, ty: Type) -> Result<Variable> {
        match &self.ag[arg.idx()] {
            astgraph::AstNode::Var(var) => match arg.op(&self.ag).next(&self.ag) {
                Some(next) => self
                    .lg
                    .new_var(next.idx(), Str::new(var.str()), ty, var.clone())
                    .map_err(|chg| {
                        self.chgs.push(chg.into());
                        Error::update_locals_graph(var)
                    }),
                None => Ok(Variable::noop(var.clone(), ty)),
            },
            x => {
                use astgraph::AstNode::*;
                let v = match x {
                    Ident(_) => "identifier",
                    Num { .. } => "number",
                    Expr(_) => "expression",
                    Var(_) => "variable",
                    Pound { .. } => "special-literal",
                    Op { .. } | Intrinsic { .. } | Def { .. } | Flag(_) => unreachable!(),
                };

                Err(Error::unexp_arg_variant(x.tag(), v))
            }
        }
    }

    /// Create a variable reference not off a specific argument, but by manually specifying the
    /// variable name.
    ///
    /// This is useful for expressions that need to supply more than just the input. For instance
    /// the `fold` command will supply the `$row` variable which is a track of the TableRow.
    ///
    /// Consider using the helper `Block::inject_manual_var_next_arg` which uses the next arguments
    /// argnode.
    pub fn inject_manual_var_into_arg_locals<N>(
        &mut self,
        arg: graphs::ArgNode,
        name: N,
        ty: Type,
    ) -> Result<Variable>
    where
        N: Into<Str>,
    {
        // we define it into the arg node
        let tag = arg.tag(&self.ag);
        self.lg
            .new_var(arg.idx(), name, ty, tag.clone())
            .map_err(|chg| {
                self.chgs.push(chg.into());
                Error::update_locals_graph(tag)
            })
    }

    /// Helper for `Block::inject_manual_var_into_arg_locals` which peeks the next argument on the
    /// stack to use as the `arg` input.
    pub fn inject_manual_var_next_arg<N>(&mut self, name: N, ty: Type) -> Result<Variable>
    where
        N: Into<Str>,
    {
        let n = self
            .peek_next_arg_node()
            .ok_or_else(|| Error::insufficient_args(self.op_tag(), self.args_count, None))?;
        self.inject_manual_var_into_arg_locals(n, name, ty)
    }

    fn get_var_def_or_add_change(
        &mut self,
        name: Str,
        ty: Type,
        tag: Tag,
        op: OpNode,
    ) -> Result<Variable> {
        todo!("wire in");
        //         let locals = self.lg.get(op).ok_or_else(|| Error::locals_unavailable(&tag))?;
        //
        //         match locals.get(&name) {
        //             Some(Local::Var(v)) if v.defined_at() == op => Ok(v.clone()),
        //             _ => {
        //                 let e = Error::locals_unavailable(&tag);
        //                 // flag to add
        //                 todo!();
        // //                 self.chgs.push(locals_graph::Chg::NewVar {
        // //                     name,
        // //                     ty,
        // //                     tag,
        // //                     defined_at: op
        // //                 }.into());
        //
        //                 Err(e)
        //             }
        //         }
    }
}
