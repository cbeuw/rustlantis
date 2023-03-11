use std::collections::HashMap;

use mir::{
    syntax::{Body, Local, Place, ProjectionElem, Ty},
    vec::{self, IndexVec},
};
use petgraph::{stable_graph::{DefaultIx, NodeIndex}, Graph};

// A program-global graph recording all places that can be reached through projections
pub struct PlaceTable {
    current_locals: HashMap<Local, NodeIndex>,
    places: Graph<PlaceNode, ProjectionElem>,
}

struct PlaceNode {
    ty: Ty,
    init: bool,
}

impl PlaceTable {
    pub fn new() -> Self {
        Self {
            current_locals: HashMap::new(),
            places: Graph::new(),
        }
    }

    pub fn enter_fn(&mut self, body: &Body) {
        self.current_locals = HashMap::new();
        body.args_decl_iter().for_each(|(local, decl)| {
            let idx = self.places.add_node(PlaceNode {
                ty: decl.ty.clone(),
                init: body.is_arg(local),
            });
            self.current_locals.insert(local, idx);
        });
        let idx = self.places.add_node(PlaceNode {
            ty: body.return_ty(),
            init: false,
        });
        self.current_locals.insert(Local::RET, idx);
        // TODO: projections
    }

    pub fn add_local(&mut self, local: Local, ty: Ty) {
        let pidx = self.places.add_node(PlaceNode { ty, init: false });
        self.current_locals.insert(local, pidx);
    }

    fn reachable_nodes(&self) {

    }
}
