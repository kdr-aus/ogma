use super::*;
use std::ops::Deref;

type TypeGraphInner = petgraph::stable_graph::StableGraph<Knowledge, Flow>;

#[derive(Debug, PartialEq, Eq)]
pub enum Knowledge {
    Unknown,
    Known(Type),
    Obliged(Type),
    Inferred(Type),
}

#[derive(Debug)]
pub enum Flow {
    /// Output knowledge flows into the input.
    OI,
    /// Input knowledge flows into the input.
    II,
    /// Output knowledge flows into the output.
    OO,
    /// Input knowledge flows into the output.
    IO,
}

#[derive(Debug)]
pub struct TypeGraph(TypeGraphInner);

// Note that we do not expose a mutable deref, keep mutation contained in this module.
impl Deref for TypeGraph {
    type Target = TypeGraphInner;
    fn deref(&self) -> &TypeGraphInner {
        &self.0
    }
}

impl TypeGraph {
    /// Builds a type graph based off the ast graph.
    pub fn build(ast_graph: &AstGraph) -> Self {
        let mut g = TypeGraph(ast_graph.map(|_, _| Knowledge::Unknown, |_, _| Flow::OI));
        g.0.clear_edges(); // remove all the edges
        g
    }

    /// Apply _known_ types from the AST nodes.
    ///
    /// For instance, a number variant node can be assigned the type number.
    pub fn apply_ast_types(&mut self, ag: &AstGraph) {
        for nidx in ag.node_indices() {
            let node = &ag[nidx];

            use AstNode::*;
            let ty = match node {
                Op(_) | Flag(_) => None,
                Ident(_) => Some(Type::Str),
                Num { .. } => Some(Type::Num),
                Pound { ch: 'n', .. } => Some(Type::Nil),
                Pound { ch: 't', .. } | Pound { ch: 'f', .. } => Some(Type::Bool),
                Pound { .. } => None,
                Var(_) => None,
                Expr(_) => None,
            };

            if let Some(ty) = ty.map(Knowledge::Known) {
                let current = self
                    .0
                    .node_weight_mut(nidx)
                    .expect("Type and Ast graphs should have same indices");
                assert!(
                    matches!(current, Knowledge::Unknown),
                    "overwriting a non-unknown type node"
                );
                *current = ty;
            }
        }
    }
}
