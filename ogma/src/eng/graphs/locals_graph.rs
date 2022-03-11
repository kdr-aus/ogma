use super::*;
use petgraph::prelude::*;
use std::{cell::Cell, rc::Rc, ops::Deref};

type Vars = Rc<HashMap<Str, Local>>;

type LocalsGraphInner = petgraph::stable_graph::StableGraph<Vars, (), petgraph::Directed, u32>;

pub enum Chg {
    NewVar {
        name: Str,
        ty: Type,
        tag: Tag,
        defined_at: OpNode
    }
}

#[derive(Default, Debug, Clone)]
pub struct LocalsGraph {
    graph: LocalsGraphInner,
    count: Rc<Cell<usize>>,
}

impl LocalsGraph {
    /// Builds a locals graph based off the ast graph.
    pub fn build(ast_graph: &astgraph::AstGraph) -> Self {
        let m = Rc::new(Default::default());
        let mut graph = ast_graph.map(
            |_, _| Rc::clone(&m),
            |_, _| (),
        );

        graph.clear_edges(); // remove all the edges
        
        Self {
            graph,
            count: Default::default()
        }
    }

    pub fn insert_root(&mut self, locals: Locals) {
        todo!()
    }

    /// Returns if the graph as altered.
    pub fn apply_chg(&mut self, chg: Chg) -> bool {
        todo!()
    }
}
