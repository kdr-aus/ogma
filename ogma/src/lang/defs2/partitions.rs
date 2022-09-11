use crate::prelude::*;
use petgraph::prelude::*;

type Inner = StableGraph<Node, (), Directed, u32>;

type NodesList = Arc<[NodeIndex]>;

enum Node {
    Boundary { name: Str, exports: NodesList },
    Type { name: Str, imports: NodesList },
    Impl { name: Str, imports: NodesList },
}

pub struct Partitions {
    root: NodeIndex,
    shell: NodeIndex,
    plugins: NodeIndex,

    graph: Inner,
}
