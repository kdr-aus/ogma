use super::*;
use std::ops::Deref;

type TypeGraphInner = petgraph::stable_graph::StableGraph<Node, Flow>;

#[derive(Debug, PartialEq, Eq)]
pub struct Node {
    pub input: Knowledge,
    pub output: Knowledge,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Knowledge {
    Unknown,
    Known(Type),
    Obliged(Type),
    Inferred(Type),
}

#[derive(Debug, PartialEq, Eq)]
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
        let mut g = TypeGraph(ast_graph.map(
            |_, _| Node {
                input: Knowledge::Unknown,
                output: Knowledge::Unknown,
            },
            |_, _| Flow::OI,
        ));

        g.0.clear_edges(); // remove all the edges
        g
    }

    /// Apply _known_ types from the AST nodes.
    ///
    /// For instance, a number variant node can be assigned the type number as an output.
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
                    matches!(current.output, Knowledge::Unknown),
                    "overwriting a non-unknown type node"
                );
                current.output = ty;
            }
        }
    }

    /// Apply known edges for the flow of types from the ast graph:
    ///
    /// - The _input_ of an expression goes to the _input_ of the first op,
    /// - The _output_ of the last op in an expression to the _output_ of the expression,
    /// - The _output_ of a block into the _input_ of the next block,
    /// - For _defs_, the _input_ flows down into the expression.
    ///     - This is because defs will **always** use the input defined on the op.
    pub fn apply_ast_edges(&mut self, ag: &AstGraph) {
        // NOTE: The graph .neighbors call returns items in the _reverse_ order they were added.
        // It also does not support a .rev() call.

        // The input of an expression goes to the input of the first op
        for expr in ag.node_indices().filter(|&n| ag[n].expr().is_some()) {
            if let Some(op) = ag.neighbors(expr).last() {
                // last, since this would have been the first op to add
                self.0.add_edge(expr, op, Flow::II); // input -> input
            }
        }

        // the output of the last op in an expression to the output of the expression
        for expr in ag.node_indices().filter(|&n| ag[n].expr().is_some()) {
            if let Some(op) = ag.neighbors(expr).next() {
                // first, since this would have been the last op to add
                self.0.add_edge(op, expr, Flow::OO); // output -> output
            }
        }

        // the output of a block into the input of the next block
        for expr in ag.node_indices().filter(|&n| ag[n].expr().is_some()) {
            let froms = ag.neighbors(expr).skip(1); // starts at nth-1 op
            let tos = ag.neighbors(expr); // starts at last op

            for (from, to) in froms.zip(tos) {
                self.0.add_edge(from, to, Flow::OI); // output -> input
            }
        }

        // TODO: handle defs
    }
}
