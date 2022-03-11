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
    /// # Type safety
    /// The variable will be created expecting the type `ty`. `set_data` only validates types in
    /// debug builds, be sure that testing occurs of code path to avoid UB in release.
    pub fn create_var_ref(&mut self, arg: ArgNode, ty: Type) -> Result<Variable> {
        todo!()
//         match (self.locals.as_mut(), &self.ag[self.node.idx()]) {
//             (Some(locals), astgraph::AstNode::Var(var)) => {
//                 todo!()
// //                 Ok(locals.add_new_var(Str::new(var.str()), ty, var.clone()))
//             }
//             (None, astgraph::AstNode::Var(var)) => Err(Error::locals_unavailable(var)),
//             (_, x) => {
//                 use astgraph::AstNode::*;
//                 let v = match x {
//                     Ident(_) => "identifier",
//                     Num { .. } => "number",
//                     Expr(_) => "expression",
//                     Var(_) => "variable",
//                     Pound { .. } => "special-literal",
//                     Op { .. } | Intrinsic { .. } | Def(_) | Flag(_) => unreachable!(),
//                 };
// 
//                 Err(Error::unexp_arg_variant(x.tag(), v))
//             }
//         }
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
        todo!("review and wire in");

        // this is a little hairy...
        // Calling Locals::add_new_var will always update the locals, which will end up creating an
        // infinite loop since there would always be a change to the local map.
        // This indicated at a deeper bug, where a secondary call for injection would cause
        // stacking of variables.
        // But! If a variable is tested for existence, it might be referencing something that is
        // scoped _outside_ of the node. The node **definitely** needs a **new** variable location.
        //
        // To combat this, we basically test twice.
        // First, see if there is a variable reference in the blk's locals,
        // Second, see if there is a variable reference in the arg's locals,
        // Third, if the indices match, then a new variable should be created

//         let argop = arg.child_op(&self.ag);
//         let argtag = self.ag[arg.idx()].tag().clone();
//         match argop {
//             // there is no child arg op, which means no locals to add a variable to
//             // in this case we add a noop variable
//             None => Ok(Variable::noop(argtag, ty)),
//             Some(argop) => {
//                 let name = name.into();
// 
//                 let blk_var = self
//                     .lg
//                     .get(self.node)
//                     .and_then(|locals| locals.get(name.as_str()))
//                     .and_then(|local| match local {
//                         Local::Var(v) => Some(v),
//                         _ => None,
//                     });
// 
//                 let mut locals = self.lg.get(argop).ok_or_else(||
//             // if there are no locals for arg, error out
//             Error::locals_unavailable(&argtag))?;
// 
//                 let existing_var = match (blk_var, locals.get(name.as_str())) {
//                     // No block match, return existing
//                     (None, Some(Local::Var(v))) => Some(v),
//                     // Block matches
//                     (Some(bv), Some(Local::Var(v))) => {
//                         // block index doesn't match, return existing
//                         (bv.idx() != v.idx()).then(|| v)
//                     }
//                     // definitely not the previously created variable
//                     (_, Some(Local::Param(_))) => None,
//                     // no match, create new
//                     (_, None) => None,
//                 };
// 
//                 match existing_var {
//                     Some(v) => Ok(v.clone()),
//                     None => {
//                         // add a **new variable location**
//                         todo!();
//                         // clone the locals and add a variable
//                         // error out, but add this locals as a change to the lg
// //                         Ok(self
// //                             .lg
// //                             .get_mut(&argop.index())
// //                             .expect("tested for existence")
// //                             .add_new_var(name, ty, argtag))
//                     }
//                 }
//             }
//         }
    }

    /// Helper for `Block::inject_manual_var_into_arg_locals` which peeks the next argument on the
    /// stack to use as the `arg` input.
    pub fn inject_manual_var_next_arg<N>(&mut self, name: N, ty: Type) -> Result<Variable>
    where
        N: Into<Str>,
    {
        let n = self
            .peek_next_arg_node()
            .ok_or_else(|| Error::insufficient_args(self.op_tag(), self.args_count))?;
        self.inject_manual_var_into_arg_locals(n, name, ty)
    }

    fn get_var_def_or_add_change(&mut self, name: Str, ty: Type, tag: Tag, op: OpNode) -> Result<Variable> {
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
