use super::*;

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

        self.tg_chgs
            .push(graphs::tygraph::Chg::KnownOutput(self.node.idx(), ty));
    }
}
