use super::*;
use astgraph::AstGraph;
use petgraph::prelude::*;

type Map = HashMap<Str, Local>;

#[derive(Copy, Clone, Debug)]
enum E {
    Flow,
    Seal,
}

/// A index pointer into the locals stack.
#[derive(Debug, Copy, Clone)]
struct Local {
    local: u32,
    defined: NodeIndex,
}

#[derive(Default, Debug, Clone)]
struct Vars {
    /// A map of all the available variables.
    map: Map,
    /// Flags if this node is sealed.
    sealed: bool,
}

type LocalsGraphInner = petgraph::stable_graph::StableGraph<Vars, E, petgraph::Directed, u32>;

#[derive(Debug)]
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
    /// Seal the op node, indicating no further variable additions will be made.
    Seal(OpNode),
    /// Removes a connection between the op and arg.
    /// This is useful for ops such as `let` which might need it's arguments to be able to compile
    /// without `let` op needing to be 'sealed'.
    BreakEdge {
        op: OpNode,
        arg: ArgNode
    }
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

impl E {
    fn is_flow(&self) -> bool {
        matches!(self, E::Flow)
    }

    fn is_seal(&self) -> bool {
        matches!(self, E::Seal)
    }
}

impl LocalsGraph {
    /// Builds a locals graph based off the ast graph.
    pub fn build(ast_graph: &AstGraph) -> Self {
        let mut graph = ast_graph.map(|_, _| Default::default(), |_, _| E::Seal);

        graph.clear_edges(); // remove all the edges

        Self {
            graph,
            count: 0,
            locals: Vec::new(),
        }
        .init_edges(ast_graph)
    }

    /// Crucially, no edges are provided between def boundaries.
    /// The idea is that the compiler will add variables into the def subexpression when injecting
    /// parameters.
    fn init_edges(mut self, ag: &AstGraph) -> Self {
        let g = &mut self.graph;

        // blocks flow between each other in expressions
        // all ops are indeterminate to add
        for op in ag.op_nodes() {
            if let Some(next) = op.next(ag) {
                g.update_edge(op.idx(), next.idx(), E::Flow);
                g.update_edge(next.idx(), op.idx(), E::Seal);
            }
        }

        // each op flows into each of its arguments
        // sealing checks the _prev_ argument, or the expr for the root
        // it also defaults to the op, but this can be broken
        // all args assert that they are sealed
        for arg in ag.arg_nodes() {
            g[arg.idx()].sealed = true;

            let op = arg.op(ag);

            g.update_edge(op.idx(), arg.idx(), E::Flow);
            g.update_edge(arg.idx(), op.idx(), E::Seal);

            match op.prev(ag) {
                Some(prev) => g.update_edge(arg.idx(), prev.idx(), E::Seal),
                None => g.update_edge(arg.idx(), op.parent(ag).idx(), E::Seal),
            };
        }

        // each expr flows into its first op
        // sealing flows in opposite direction
        // expressions are indeterminate to add, since sub-expressions of defs may have parameters
        // that need to finalise. the only node which would be sealed is the root node
        for expr in ag.expr_nodes() {
            let fop = expr.first_op(ag).idx();
            g.update_edge(expr.idx(), fop, E::Flow);
            g.update_edge(fop, expr.idx(), E::Seal);
        }

        // seal the root expression node
        self.seal(ExprNode(0.into()));

        self
    }

    pub fn seed(&mut self, vars: var::SeedVars) {
        let Self {
            graph,
            count,
            locals,
        } = self;

        let Vars { map, sealed: _ } = graph.node_weight_mut(0.into()).expect("exists");

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

    /// Get a local `name` at `node`.
    ///
    /// Note that this does not check for sealing, that should be done before using this reference.
    fn get_(&self, node: NodeIndex, name: &str) -> Option<&eng::Local> {
        self.graph[node]
            .map
            .get(name)
            .map(|l| &self.locals[l.local as usize])
    }

    /// Gets the local `name` at `node`.
    ///
    /// If the locals graph cannot provide a concrete answer, [`Error::update_locals_graph`] is
    /// returned.
    pub fn get(&self, node: NodeIndex, name: &str, tag: &Tag) -> Result<&eng::Local> {
        self.sealed(node)
            .then(|| {
                self
                    .get_(node, name)
                    .ok_or_else(|| Error::var_not_found(tag))
            })
            .ok_or_else(|| Error::update_locals_graph(tag))
            .and_then(|x| x)
    }

    /// Gets the local `name` at `node`.
    ///
    /// If the locals graph cannot provide a concrete answer because there are unsealed nodes in
    /// lexical scope, `(false, None)` is returned.
    /// Otherwise `(true, Option)` is returned.
    pub fn get_opt(&self, node: NodeIndex, name: &str) -> (bool, Option<&eng::Local>) {
        match self.sealed(node) {
            true => (true, self.get_(node, name)),
            false => (false, None),
        }
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
            .ok_or(Chg::NewVar {
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
            .map(|l| {
                if let eng::Local::Var(_) = &self.locals[l.local as usize] {
                    unreachable!("this call should not create a var local")
                }
            })
            .ok_or(Chg::NewLazy {
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
            Chg::Seal(op) => {
                let a = &mut self.graph[op.idx()];
                if a.sealed {
                    false
                } else {
                    a.sealed = true;
                    true
                }
            }
            Chg::BreakEdge { op, arg } => {
                if let Some(e) = self.graph.find_edge(arg.idx(), op.idx()) {
                    self.graph.remove_edge(e);
                    true
                } else {
                    false
                }
            }
        }
    }

    fn neighbours_flow(&self, n: NodeIndex) -> impl Iterator<Item = NodeIndex> + '_ {
        self
            .graph
            .edges(n)
            .filter_map(|e| e.weight().is_flow().then(|| e.target()))
    }

    fn neighbours_seal(&self, n: NodeIndex) -> impl Iterator<Item = NodeIndex> + '_ {
        self
            .graph
            .edges(n)
            .filter_map(|e| e.weight().is_seal().then(|| e.target()))
    }



    fn flow(&mut self, from: NodeIndex) {
        let mut stack = self.neighbours_flow(from).map(|to| (from, to))
            .collect::<Vec<_>>();

        while let Some((from, to)) = stack.pop() {
            self.accrete(from, to);

            // to is now update, flow from there
            let from = to;
            stack.extend(self.neighbours_flow(from).map(|to| (from, to)));
        }
    }

    fn accrete(&mut self, from: NodeIndex, to: NodeIndex) {
        // to get around lifetime issues, we swap out the `to` map to mutate it,
        // then swap it back in once we are done
        let to_ = std::mem::take(&mut self.graph[to].map);
        let to_ = accrete(&self.graph[from].map, to_, to);
        // reinstate the map
        self.graph[to].map = to_;
    }

    fn add_new_var(&mut self, name: Str, ty: Type, tag: Tag, defined: NodeIndex) {
        debug_assert!(
            !matches!(self.graph[defined].map.get(&name), Some(l) if l.defined == defined),
            "sense check that a new variable is not being created over an existing, matching one"
        );

        let var = Variable::new(tag, ty, self.count);

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

    /// Checks that this node is sealed and no variables will be introduced along the path to root.
    pub fn sealed(&self, node: NodeIndex) -> bool
    {
        let mut q = std::collections::VecDeque::new();
        q.push_back(node);

        while let Some(node) = q.pop_front() {
            if !self.graph[node].sealed {
                return false;
            }

            q.extend(self.neighbours_seal(node));
        }

        true
    }

    /// Mark this expression node as one which will not introduce variables.
    ///
    /// This is meant for definition sub-expressions for when the parameters have been finalised.
    pub fn seal(&mut self, expr: ExprNode) {
        self.graph[expr.idx()].sealed = true;
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

        for X { n, tag, sealed, vars } in xs {
            writeln!(s, r#"    [{},"{tag}",{sealed},"{vars}"]"#, n.index())?;
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
                    match w.sealed {
                        true => " <br> sealed",
                        false => "",
                    }
                )
            },
            |n, s| write!(s, "{n:?}",),
        )?;

        Ok(())
    }
}

fn accrete(from: &Map, mut to: Map, to_idx: NodeIndex) -> Map {
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

    to
}
