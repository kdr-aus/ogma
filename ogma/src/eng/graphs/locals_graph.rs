use super::*;
use astgraph::AstGraph;
use petgraph::prelude::*;
use std::{cell::Cell, ops::Deref, rc::Rc};

#[derive(Debug, Copy, Clone)]
struct Local {
    local: u32,
    defined: NodeIndex,
}

#[derive(Default, Debug, Clone)]
struct Vars {
    map: HashMap<Str, Local>,
    /// Marker indicating that this map will not have any more variables introduced into it.
    sealed: bool,
}

type LocalsGraphInner = petgraph::stable_graph::StableGraph<Vars, (), petgraph::Directed, u32>;

pub enum Chg {
    NewVar {
        name: Str,
        ty: Type,
        tag: Tag,
        defined_at: NodeIndex,
    },
    /// A pointer to an argument node to be used in place of the variable.
    NewLazy {
        name: Str,
        to: ArgNode,
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
}

impl LocalsGraph {
    /// Builds a locals graph based off the ast graph.
    pub fn build(ast_graph: &AstGraph) -> Self {
        let mut graph = ast_graph.map(|_, _| Default::default(), |_, _| ());

        graph.clear_edges(); // remove all the edges

        let mut this = Self {
            graph,
            count: 0,
            locals: Vec::new(),
        }
        .init_edges(ast_graph);

        // seal initial node since no variables will be introduced into them
        this.seal_node(0.into(), ast_graph);

        this
    }

    /// Crucially, no edges are provided between def boundaries.
    /// The idea is that the compiler will add variables into the def subexpression when injecting
    /// parameters.
    fn init_edges(mut self, ag: &AstGraph) -> Self {
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
        } = self;

        let Vars { map, sealed } = graph.node_weight_mut(0.into()).expect("exists");

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
            .map
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
        self.get(node, name).ok_or_else(|| {
            if self.sealed(node) {
                Error::var_not_found(tag)
            } else {
                Error::update_locals_graph(tag)
            }
        })
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
    /// `Err(Chg)` will return a change entry that can be process via [`Self::apply_chg`].
    pub fn new_var<N: Into<Str>>(
        &self,
        defined_at: NodeIndex,
        name: N,
        ty: Type,
        tag: Tag,
    ) -> std::result::Result<Variable, Chg> {
        let name = name.into();
        self.graph[defined_at]
            .map
            .get(&name)
            .filter(|l| l.defined == defined_at)
            .map(|l| match &self.locals[l.local as usize] {
                eng::Local::Var(var) => var.clone(),
                _ => unreachable!("this call should not create a param local"),
            })
            .ok_or_else(|| Chg::NewVar {
                name,
                ty,
                tag,
                defined_at,
            })
    }

    /// A new lazy argument pointer should be added.
    ///
    /// To be robust against partial compilation, adding a new pointer is done by applying changes
    /// to the locals graph. This way it is gated on success and can be applied later, rather than
    /// in this call, similar to `new_var`.
    ///
    /// `Ok(())` indicates that the pointer has been created.
    /// `Err(Chg)` will return a change entry that can be process via [`Self::apply_chg`].
    pub fn new_lazy<N: Into<Str>>(
        &self,
        defined_at: NodeIndex,
        name: N,
        point_to: ArgNode,
        tag: Tag,
    ) -> std::result::Result<(), Chg> {
        let name = name.into();
        self.graph[defined_at]
            .map
            .get(&name)
            .filter(|l| l.defined == defined_at)
            .map(|l| match &self.locals[l.local as usize] {
                eng::Local::Var(_) => unreachable!("this call should not create a var local"),
                _ => (),
            })
            .ok_or_else(|| Chg::NewLazy {
                name,
                to: point_to,
                tag,
                defined_at,
            })
    }

    /// Returns if the graph as altered.
    pub fn apply_chg(&mut self, chg: Chg) -> bool {
        match chg {
            Chg::NewVar {
                name,
                ty,
                tag,
                defined_at,
            } => {
                self.add_new_var(name, ty, tag, defined_at);
                self.flow(defined_at); // propogate change
                true // graph altered
            }
            Chg::NewLazy {
                name,
                to,
                tag,
                defined_at,
            } => {
                self.add_new_lazy(name, to, tag, defined_at);
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
        let mut to = std::mem::take(&mut self.graph[to_idx].map);
        let from = &self.graph[from].map;

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
        self.graph[to_idx].map = to;
    }

    fn add_new_var(&mut self, name: Str, ty: Type, tag: Tag, defined: NodeIndex) {
        debug_assert!(
            !matches!(self.graph[defined].map.get(&name), Some(l) if l.defined == defined),
            "sense check that a new variable is not being created over an existing, matching one"
        );

        let var = Variable {
            tag,
            ty,
            env_idx: self.count,
        };

        self.count += 1;
        let local = self.locals.len() as u32;

        self.locals.push(eng::Local::Var(var));

        self.graph[defined]
            .map
            .insert(name, Local { local, defined });
    }

    fn add_new_lazy(&mut self, name: Str, to: ArgNode, tag: Tag, defined: NodeIndex) {
        debug_assert!(
            !matches!(self.graph[defined].map.get(&name), Some(l) if l.defined == defined),
            "sense check that a new variable is not being created over an existing, matching one"
        );

        let local = self.locals.len() as u32;
        self.locals.push(eng::Local::Ptr { to, tag });

        self.graph[defined]
            .map
            .insert(name, Local { local, defined });
    }

    /// Seal an op or expr node, flagging that there will not be any more variables introduced.
    /// An op's successful compilation would seal it.
    pub fn seal_node(&mut self, node: NodeIndex, ag: &AstGraph) {
        self.graph[node].sealed = true; // seal itself
        let mut wlkr = self.graph.neighbors(node).detach();
        while let Some(n) = wlkr.next_node(&self.graph) {
            self.graph[n].sealed = true; // seal flow targets
            if let Some(e) = ag[n].expr().map(|_| ExprNode(n)) {
                // if flow target is an expression, seal the expr's first op as well
                self.graph[e.first_op(ag).idx()].sealed = true;
            }
        }
    }

    /// Returns if this node will not be updated, sealing the variable set.
    ///
    /// This not only looks at itself, but the parent paths, since an unsealed node in the chain
    /// might introduce a variable which propagates along.
    pub fn sealed(&self, node: NodeIndex) -> bool {
        // self is sealed,
        self.graph[node].sealed
            // and its ancestors are sealed (notice the recursion)
            && self.graph.neighbors_directed(node, Incoming).all(|n| self.sealed(n))
    }
}

#[cfg(debug_assertions)]
impl LocalsGraph {
    pub fn debug_write(&self, s: &mut String, ag: &AstGraph) -> fmt::Result {
        use fmt::Write;

        writeln!(s, "### State")?;
        writeln!(s, "```kserd")?;
        writeln!(s, r#"header = ["Index","Tag","Sealed","Vars"]"#)?;
        writeln!(s, "data = [")?;

        struct X<'a> {
            n: NodeIndex,
            tag: &'a str,
            sealed: bool,
            vars: String,
        }

        let mut xs = ag
            .op_nodes()
            .map(|x| x.idx())
            .chain(ag.expr_nodes().map(|x| x.idx()))
            .chain(ag.arg_nodes().map(|x| x.idx()))
            .map(|n| {
                let Vars { map, sealed } = &self.graph[n];
                let mut vars = map
                    .iter()
                    .map(|(name, i)| {
                        let ty = match &self.locals[i.local as usize] {
                            eng::Local::Var(v) => v.ty().to_string(),
                            eng::Local::Ptr { .. } => "?".into(),
                        };
                        format!("{}:{}", name, ty)
                    })
                    .collect::<Vec<_>>();
                vars.sort_unstable();
                let vars = vars.into_iter().fold(String::new(), |s, x| s + &x + ", ");

                X {
                    n,
                    tag: ag[n].tag().str(),
                    sealed: *sealed,
                    vars,
                }
            })
            .collect::<Vec<_>>();

        xs.sort_unstable_by(|a, b| a.n.cmp(&b.n));
        xs.dedup_by_key(|x| x.n);

        for X {
            n,
            tag,
            sealed,
            vars,
        } in xs
        {
            writeln!(s, r#"    [{},"{}",{},"{}"]"#, n.index(), tag, sealed, vars)?;
        }

        writeln!(s, "]")?;
        writeln!(s, "rowslim = 200")?;
        writeln!(s, "```")?;

        writeln!(s, "### Graph")?;
        debug_write_flowchart(
            &self.graph,
            s,
            |n, _| ag.is_arg_node(n) || ag[n].op().is_some() || ag[n].expr().is_some(),
            |n, w, s| {
                write!(
                    s,
                    "{}: {}{}",
                    n.index(),
                    ag[n].tag(),
                    if w.sealed { " <br> sealed" } else { "" }
                )
            },
            |_, s| write!(s, " "),
        )?;

        Ok(())
    }
}
