use super::*;
use petgraph::prelude::*;
use std::{cell::Cell, ops::Deref, rc::Rc};

#[derive(Debug, Copy, Clone)]
struct Local {
    local: u32,
    defined: NodeIndex,
}

type Vars = HashMap<Str, Local>;

type LocalsGraphInner = petgraph::stable_graph::StableGraph<Vars, (), petgraph::Directed, u32>;

pub enum Chg {
    NewVar {
        name: Str,
        ty: Type,
        tag: Tag,
        defined_at: NodeIndex,
    },
}

/// A graph structure which tracks variables, allowing for lexical scoping and shadowing.
///
/// The graph creates links which act as the 'scoping' for variables.
/// When a variable is added, it flows along its paths, **accreting** variables along the way.
/// The accretion is crucial, since variable addition may be out of order.
#[derive(Default, Debug, Clone)]
pub struct LocalsGraph {
    graph: LocalsGraphInner,
    count: usize,
    locals: Vec<eng::Local>,
    sealed: HashSet<NodeIndex>
}

impl LocalsGraph {
    /// Builds a locals graph based off the ast graph.
    pub fn build(ast_graph: &astgraph::AstGraph) -> Self {
        let mut graph = ast_graph.map(|_, _| Default::default(), |_, _| ());

        graph.clear_edges(); // remove all the edges

        let mut this = Self {
            graph,
            count: 0,
            locals: Vec::new(),
            sealed: Default::default()
        }
        .init_edges(ast_graph);

        // seal initial nodes since no variables will be introduced into them
        this.seal_node(ExprNode(0.into()).first_op(ast_graph));

        this
    }

    /// Crucially, no edges are provided between def boundaries.
    /// The idea is that the compiler will add variables into the def subexpression when injecting
    /// parameters.
    fn init_edges(mut self, ag: &astgraph::AstGraph) -> Self {
        let g = &mut self.graph;

        // blocks flow between each other in expressions
        for op in ag.op_nodes() {
            if let Some(next) = op.next(ag) {
                g.update_edge(op.idx(), next.idx(), ());
            }
        }

        // each op flows into each of its arguments
        for arg in ag.arg_nodes() {
            g.update_edge(arg.op(ag).idx(), arg.idx(), ());
        }

        // each expr flows into its first op
        for expr in ag.expr_nodes() {
            g.update_edge(expr.idx(), expr.first_op(ag).idx(), ());
        }

        self
    }

    pub fn seed(&mut self, vars: var::SeedVars) {
        let Self {
            graph,
            count,
            locals,
            sealed
        } = self;

        let map = graph.node_weight_mut(0.into()).expect("exists");

        for (name, var) in vars.drain() {
            let idx = locals.len();

            debug_assert_eq!(idx, var.idx());

            locals.push(eng::Local::Var(var));

            *count += 1;

            map.insert(
                name,
                Local {
                    local: idx as u32,
                    defined: 0.into(),
                },
            );
        }

        self.flow(0.into()); // since all updates go into root map, do a flow to get them into op maps
    }

    pub fn var_count(&self) -> usize {
        self.count
    }

    /// Fetch a variable if it is found on the node's locals map.
    pub fn get(&self, node: NodeIndex, name: &str) -> Option<&eng::Local> {
        self.graph[node]
            .get(name)
            .map(|l| l.local as usize)
            .map(|i| &self.locals[i])
    }

    /// Much like `get`, but runs checks to assert if `name` is definitely not found, returning a
    /// hard error.
    ///
    /// If `name` is not found but there could be updates to the graph which introduce `name`, then
    /// a soft error is returned.
    pub fn get_checked(&self, node: NodeIndex, name: &str, tag: &Tag) -> Result<&eng::Local> {
        self.get(node, name).ok_or_else(|| if self.sealed.contains(&node) {
            Error::var_not_found(tag)
        } else {
                        dbg!("this one");
            Error::update_locals_graph(tag)
        })
    }

    /// Returns if this node will not be updated, sealing the variable set.
    pub fn sealed(&self, node: NodeIndex) -> bool {
        self.sealed.contains(&node)
    }

    /// A new variable should be added.
    ///
    /// To be robust against partial compilation, adding a new variable is done by applying changes
    /// to the locals graph. This way it is gated on success and can be applied later, rather than
    /// in this call.
    /// So that new variable are not continually added, if the _defined_ node already contains this
    /// variable (defined at the **defined** node), then the variable is returned immediately.
    /// While this does incur a performance penalty (compilation always will take 2 passes), it
    /// does ensure that no duplicates of variables occur.
    ///
    /// `Ok(Variable)` indicates that the variable has been created and can be used.
    /// `Err(Chg)` will return a change entry that can be process via [`apply_chg`].
    pub fn new_var<N: Into<Str>>(&self, defined_at: NodeIndex, name: N, ty: Type, tag: Tag) -> std::result::Result<Variable, Chg> {
        let name = name.into();
        self.graph[defined_at].get(&name).filter(|l| l.defined == defined_at)
            .map(|l| match &self.locals[l.local as usize] {
                eng::Local::Var(var) => var.clone(),
                _ => unreachable!("this call should not create a param local"),
            })
            .ok_or_else(|| Chg::NewVar {
                name,
                ty,
                tag,
                defined_at
            })
    }

    /// Returns if the graph as altered.
    pub fn apply_chg(&mut self, chg: Chg) -> bool {
        match chg {
            Chg::NewVar {
                name,
                ty,
                tag,
                defined_at
            } => {
                self.add_new_var(name, ty, tag, defined_at);
                self.flow(defined_at); // propogate change
                true // graph altered
            }
        }
    }

    fn flow(&mut self, from: NodeIndex) {
        let mut stack = self
            .graph
            .neighbors(from)
            .map(|to| (from, to))
            .collect::<Vec<_>>();

        while let Some((from, to)) = stack.pop() {
            self.accrete(from, to);

            // to is now update, flow from there
            let from = to;
            stack.extend(self.graph.neighbors(from).map(|to| (from, to)));
        }
    }

    fn accrete(&mut self, from: NodeIndex, to_idx: NodeIndex) {
        // to get around lifetime issues, we swap out the `to` map to mutate it,
        // then swap it back in once we are done
        let mut to = std::mem::take(&mut self.graph[to_idx]);
        let from = &self.graph[from];

        for (k, v) in from {
            // if to does not contain this key, add it in!
            if !to.contains_key(k) {
                to.insert(k.clone(), *v);
            } else {
                let tov = to.get_mut(k).expect("will exist");
                // if the to variable was defined at to, it would be more recent.
                // if not, update the map local here to be from
                if tov.defined != to_idx {
                    *tov = *v;
                }
            }
        }

        // reinstate the map
        self.graph[to_idx] = to;
    }

    fn add_new_var(&mut self, name: Str, ty: Type, tag: Tag, defined: NodeIndex) {
                debug_assert!(!matches!(self.graph[defined].get(&name), Some(l) if l.defined == defined), "sense check that a new variable is not being created over an existing, matching one");

                let var = Variable {
                    tag,
                    ty,
                    env_idx: self.count
                };

                self.count += 1;
                let local = self.locals.len() as u32;

                self.locals.push(eng::Local::Var(var));
                
                self.graph[defined].insert(name, Local {
                    local,
                    defined
                });
    }

    /// Seal a op node, flagging that there will not be any more variables introduced.
    /// An op's successful compilation would seal it.
    pub fn seal_node(&mut self, op: OpNode) {
        // sealing will seal itself, but also it's flow targets, since that is where changes would
        // be made
        let op = op.idx();
        self.sealed.insert(op);
        for n in self.graph.neighbors(op) {
            self.sealed.insert(n);
        }
    }
}
