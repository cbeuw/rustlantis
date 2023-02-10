use std::cmp::min;

use log::debug;
use petgraph::algo::{connected_components, is_cyclic_directed};
use petgraph::graph::NodeIndex;
use petgraph::prelude::DiGraph;
use petgraph::Graph;
use rand::seq::IteratorRandom;
use rand::Rng;

const MAX_BASIC_BLOCKS: usize = 100;
const MAX_FUNCTIONS: usize = 10;
const EXTRA_INCOMING_EDGE_RATE: f64 = 0.1;

/// Skeleton: a DAG (we are not adding back edges for now)
/// where nodes are partitioned into domination sets.
/// A domination set has one dominator and zero or more dominated nodes.
/// A path from any node outside a domination set to any node in the set
/// must go through the dominator of the set. In other words, all incoming
/// edges to a domination set are connected to the dominator, not other nodes.
///
/// Each node is a basic block, and a domination set is a function,
/// as functions can only start with the first basic block.

/// Whether a node is a dominator or not
#[derive(PartialEq, Eq, Debug)]
pub enum Dom {
    Dom,
    NonDom,
}

pub fn build_skeleton(rng: &mut impl Rng) -> DiGraph<Dom, ()> {
    let mut graph = Graph::<Dom, ()>::new();
    let node_count = rng.gen_range(1..MAX_BASIC_BLOCKS);
    // A sorted vec of nodes
    debug!("adding {node_count} nodes");
    let nodes: Vec<NodeIndex> = (0..node_count)
        .map(|_| graph.add_node(Dom::NonDom))
        .collect();
    // We shouldn't have to manually sort it
    assert!(nodes.is_sorted());
    // Pick out the dominators. We guarantee that the first node is a dominator since all nodes must be in a dom set.
    let function_count = rng.gen_range(1..=min(MAX_FUNCTIONS, node_count));
    debug!("adding {function_count} dominators");

    graph[nodes[0]] = Dom::Dom;
    for &idx in nodes[1..].iter().choose_multiple(rng, function_count - 1) {
        graph[idx] = Dom::Dom;
    }

    // Now the nodes list look like this
    // dom0 . . dom1 . . . . . . . dom2 . . . . . dom3 . dom4 dom5 . . . . . . .
    // Nodes in the interval [dom_n, dom_n+1) form a domination set (i.e. a function).
    // Nodes within a domination set can form a connected DAG with no additional restrictions.
    // There can be external edges that go to other dominators, and edges between domination
    // sets must form a DAG too.
    //
    // To construct a DAG (guaranteeing no cycles), we only allow an edge from a lower node to a higher node.
    // So for each node, it can connect to either a higher node in the same dom set, or a higher dominator in another dom set.

    let mut dom_sets: Vec<_> = vec![];
    {
        // Build dom sets
        let mut nodes_iter = nodes.iter();
        while !nodes_iter.is_empty() {
            let mut set = vec![*nodes_iter.next().expect("iterator is't empty")];
            // take_while() consumes the iterator rather than advancing it, so we need to clone it and manually advance_by
            set.extend(
                nodes_iter
                    .clone()
                    .take_while(|&&idx| graph[idx] != Dom::Dom)
                    .copied(),
            );
            nodes_iter
                .advance_by(set.len() - 1)
                .expect("shold not run out of nodes");

            dom_sets.push(set);
        }
    }

    // To ensure every node is connected to,
    // we connect each non-dom node from one random lower node in the dom set, then randomly pick lower nodes to connect from (which may be 0)
    // similarly, we connect each dominator from one random lower node (except for dom0 where there are no lower nodes), then randomly pick lower nodes to connect from

    for set in dom_sets.iter() {
        // Connect dominator to at least one lower node (dom or non-dom)
        {
            let dom = set[0];
            // If this is None then dom is dom0 so it has no incoming edges
            let lower_nodes = nodes.iter().take_while(|&&idx| idx < dom);
            if let Some(&lower) = lower_nodes.clone().choose(rng) {
                graph.add_edge(lower, dom, ());
            }
            // Then randomly connect dominator from more lower nodes
            // TODO: geometric or choose_multiple
            for &lower in lower_nodes {
                if rng.gen_bool(EXTRA_INCOMING_EDGE_RATE) {
                    graph.update_edge(lower, dom, ());
                }
            }
        }

        for &node in &set[1..] {
            // Connect each non-dom node in set with at least one lower node (dom or non-dom)
            let set_lower_nodes = set.iter().take_while(|&&idx| idx < node);
            let &lower = set_lower_nodes
                .clone()
                .choose(rng)
                .expect("non-dom nodes always have lower in-set nodes");
            graph.add_edge(lower, node, ());
            // Then randomly connect dominator from more lower nodes
            // TODO: geometric or choose_multiple
            for &lower in set_lower_nodes {
                if rng.gen_bool(EXTRA_INCOMING_EDGE_RATE) {
                    graph.update_edge(lower, node, ());
                }
            }
        }
    }

    // FIXME: these assertions may be expensive
    assert_eq!(connected_components(&graph), 1);
    assert!(!is_cyclic_directed(&graph));
    graph
}
