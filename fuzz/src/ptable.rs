use std::{
    collections::{HashMap, VecDeque},
    marker::PhantomData,
};

use mir::{
    syntax::{Body, FieldIdx, Local, Place, ProjectionElem, Ty},
    vec::{self, Idx, IndexVec},
};
use petgraph::{
    graph::Node,
    prelude::EdgeIndex,
    stable_graph::{DefaultIx, NodeIndex},
    visit::{EdgeRef, IntoEdgesDirected, IntoNeighborsDirected},
    Directed, Direction, Graph,
};
use smallvec::{smallvec, SmallVec};

pub type PlaceIndex = NodeIndex;
pub type ProjectionIndex = EdgeIndex;
pub type Path = SmallVec<[ProjectionIndex; 8]>;

// A program-global graph recording all places that can be reached through projections
pub struct PlaceTable {
    current_locals: HashMap<Local, PlaceIndex>,
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
            places: Graph::default(),
        }
    }

    pub fn enter_fn(&mut self, body: &Body) {
        self.current_locals = HashMap::new();
        body.args_decl_iter().for_each(|(local, decl)| {
            // arguments are init on Call, otherwise the call site is UB
            let pidx = self.add_place(decl.ty.clone(), true);
            self.current_locals.insert(local, pidx);
        });
        let pidx = self.add_place(body.return_ty(), false);
        self.current_locals.insert(Local::RET, pidx);
    }

    pub fn add_local(&mut self, local: Local, ty: Ty) {
        let pidx = self.add_place(ty, false);
        self.current_locals.insert(local, pidx);
    }

    fn add_place(&mut self, ty: Ty, init: bool) -> PlaceIndex {
        let pidx = self.places.add_node(PlaceNode {
            ty: ty.clone(),
            init,
        });
        match ty {
            Ty::Tuple(elems) => elems.iter().enumerate().for_each(|(idx, elem)| {
                let sub_pidx = self.add_place(elem.clone(), init);
                self.places
                    .add_edge(pidx, sub_pidx, ProjectionElem::Field(FieldIdx::new(idx)));
            }),
            Ty::Adt(_) => todo!(),
            Ty::RawPtr(_, _) => todo!(),
            _ => { /* primitives, no projection */ }
        }
        pidx
    }

    /// Get PlaceIndex from a Place
    pub fn get_node(&self, place: &Place) -> Option<PlaceIndex> {
        let mut node = *self.current_locals.get(&place.local())?;
        let mut proj_iter = place.projection().iter();
        while let Some(proj) = proj_iter.next() {
            let found = self
                .places
                .edges_directed(node, Direction::Outgoing)
                .find(|edge| edge.weight() == proj);
            if let Some(edge) = found {
                node = edge.target();
            } else {
                return None;
            }
        }
        Some(node)
    }

    fn sub_fields(&self, pidx: PlaceIndex) {}

    pub fn mark_place_init(&mut self, pidx: PlaceIndex) {
        self.places[pidx].init = true;
    }

    fn reachable_from_local(&self, local: Local) -> ProjectionIter<'_> {
        let local_node = self.current_locals[&local];
        ProjectionIter {
            pt: self,
            root: local,
            to_visit: self
                .places
                .edges_directed(local_node, Direction::Outgoing)
                .map(|e| smallvec![e.id()])
                .collect(),
            root_visited: false,
        }
    }

    fn reachable_nodes(&self) {}
}

struct PlacePath {
    source: Local,
    path: Path,
}

impl PlacePath {
    fn to_place(&self, pt: &PlaceTable) -> Place {
        let projs: SmallVec<[ProjectionElem; 8]> =
            self.path.iter().map(|&proj| pt.places[proj]).collect();
        Place::from_projected(self.source, &projs)
    }

    fn target_node<'pt>(&self, pt: &'pt PlaceTable) -> &'pt PlaceNode {
        if let Some(last_edge) = self.path.last() {
            let target_idx = pt
                .places
                .edge_endpoints(*last_edge)
                .expect("edge in graph")
                .1;
            &pt.places[target_idx]
        } else {
            let local_idx = pt.current_locals[&self.source];
            &pt.places[local_idx]
        }
    }
}

/// A breadth-first iterator over all projections from a local variable
/// Within each level, projections are returned in reverse insertion order
/// FIXME: this breaks if there's a reference cycle in the graph 
struct ProjectionIter<'pt> {
    pt: &'pt PlaceTable,
    root: Local,
    to_visit: VecDeque<Path>,
    root_visited: bool,
}

impl<'pt> Iterator for ProjectionIter<'pt> {
    type Item = PlacePath;
    fn next(&mut self) -> Option<Self::Item> {
        if !self.root_visited {
            self.root_visited = true;
            return Some(PlacePath {
                source: self.root,
                path: smallvec![],
            });
        }
        if let Some(path) = self.to_visit.pop_front() {
            let last_edge = *path.last().expect("path in queue is never empty");

            let (_, target) = self.pt.places.edge_endpoints(last_edge).unwrap();
            let new_edges = self.pt.places.edges_directed(target, Direction::Outgoing);
            self.to_visit.extend(new_edges.map(|e| {
                let mut new_path = path.clone();
                new_path.push(e.id());
                new_path
            }));

            Some(PlacePath {
                source: self.root,
                path,
            })
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use mir::{
        syntax::{Local, Ty},
        vec::Idx,
    };

    use super::PlaceTable;

    #[test]
    fn nested_tuple() {
        /*
            ┌──────┬──────┐
            │      │      │
            i8     │     i64
                ┌──┴──┐
                │     │
               i16   i32
        */
        let ty = Ty::Tuple(vec![Ty::I8, Ty::Tuple(vec![Ty::I16, Ty::I32]), Ty::I64]);

        let mut pt = PlaceTable::new();
        let local = Local::new(1);
        pt.add_local(local, ty);
        let visited: Vec<Ty> = pt
            .reachable_from_local(local)
            .map(|ppath| ppath.target_node(&pt).ty.clone())
            .collect();
        assert_eq!(
            &visited,
            &[
                Ty::Tuple(vec![Ty::I8, Ty::Tuple(vec![Ty::I16, Ty::I32]), Ty::I64]), // (i8, (i16, i32), i64)
                Ty::I64,                                                             // i64
                Ty::Tuple(vec![Ty::I16, Ty::I32]),                                   // (i16, 132)
                Ty::I8,                                                              // i8
                Ty::I32,                                                             // i32
                Ty::I16,                                                             // i16
            ]
        );
    }
}
