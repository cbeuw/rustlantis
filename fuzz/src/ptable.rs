use std::{collections::VecDeque, iter::Fuse};

use bimap::{BiBTreeMap, BiMap};
use mir::{
    syntax::{Body, FieldIdx, Local, Place, ProjectionElem, Ty},
    vec::Idx,
};
use petgraph::{
    prelude::EdgeIndex,
    stable_graph::NodeIndex,
    visit::{EdgeRef, IntoEdgesDirected},
    Direction, Graph,
};
use smallvec::{smallvec, SmallVec};

pub type PlaceIndex = NodeIndex;
pub type ProjectionIndex = EdgeIndex;
pub type Path = SmallVec<[ProjectionIndex; 8]>;

// A program-global graph recording all places that can be reached through projections
pub struct PlaceTable {
    current_locals: BiBTreeMap<Local, PlaceIndex>,
    places: Graph<PlaceNode, ProjectionElem>,
}

#[derive(Debug, Clone)]
pub struct PlaceNode {
    pub ty: Ty,
    pub init: bool,
}

impl PlaceTable {
    pub fn new() -> Self {
        Self {
            current_locals: BiBTreeMap::new(),
            places: Graph::default(),
        }
    }

    pub fn enter_fn(&mut self, body: &Body) {
        self.current_locals = BiBTreeMap::new();
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
        let mut node = *self.current_locals.get_by_left(&place.local())?;
        let proj_iter = place.projection().iter();
        for proj in proj_iter {
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

    pub fn mark_place_init(&mut self, pidx: PlaceIndex) {
        self.places[pidx].init = true;
    }

    pub fn is_place_init(&self, pidx: PlaceIndex) -> bool {
        self.subfields(pidx)
            .all(|ppath| ppath.target_node(self).init)
    }

    // Returns an iterator over all places subsumed by a place
    fn subfields(&self, pidx: PlaceIndex) -> ProjectionIter<'_> {
        ProjectionIter::new(self, pidx, false)
    }

    // Returns an iterator over all places reachable from local through projections
    fn reachable_from_local(&self, local: Local) -> ProjectionIter<'_> {
        let local_node = *self.current_locals.get_by_left(&local).unwrap();
        ProjectionIter::new(self, local_node, true)
    }

    pub fn reachable_nodes(&self) -> impl Iterator<Item = PlacePath> + Clone + '_ {
        let local_iter = self.current_locals.right_values();
        local_iter.flat_map(|&node| ProjectionIter::new(self, node, true))
    }
}

#[derive(Debug, Clone)]
pub struct PlacePath {
    source: NodeIndex,
    path: Path,
}

impl PlacePath {
    pub fn to_place(&self, pt: &PlaceTable) -> Place {
        let projs: SmallVec<[ProjectionElem; 8]> =
            self.path.iter().map(|&proj| pt.places[proj]).collect();
        Place::from_projected(
            *pt.current_locals.get_by_right(&self.source).unwrap(),
            &projs,
        )
    }

    pub fn target_index(&self, pt: &PlaceTable) -> PlaceIndex {
        if let Some(last_edge) = self.path.last() {
            pt.places
                .edge_endpoints(*last_edge)
                .expect("edge in graph")
                .1
        } else {
            self.source
        }
    }

    pub fn target_node<'pt>(&self, pt: &'pt PlaceTable) -> &'pt PlaceNode {
        let target_idx = self.target_index(pt);
        &pt.places[target_idx]
    }
}

/// A breadth-first iterator over all projections from a local variable
/// Within each level, projections are returned in reverse insertion order
/// FIXME: this breaks if there's a reference cycle in the graph
#[derive(Clone)]
pub struct ProjectionIter<'pt> {
    pt: &'pt PlaceTable,
    root: NodeIndex,
    to_visit: VecDeque<Path>,
    root_visited: bool,
    follow_deref: bool,
}

impl<'pt> ProjectionIter<'pt> {
    fn new(pt: &'pt PlaceTable, root: PlaceIndex, follow_deref: bool) -> Self {
        ProjectionIter {
            pt,
            root,
            to_visit: pt
                .places
                .edges_directed(root, Direction::Outgoing)
                .filter(|e| {
                    if follow_deref {
                        true
                    } else {
                        *e.weight() != ProjectionElem::Deref
                    }
                })
                .map(|e| smallvec![e.id()])
                .collect(),
            root_visited: false,
            follow_deref,
        }
    }
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
            self.to_visit.extend(
                new_edges
                    .filter(|e| {
                        if self.follow_deref {
                            true
                        } else {
                            !matches!(e.weight(), ProjectionElem::Deref)
                        }
                    })
                    .map(|e| {
                        let mut new_path = path.clone();
                        new_path.push(e.id());
                        new_path
                    }),
            );

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
        syntax::{Local, ProjectionElem, Ty},
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

        let mut pt = PlaceTable::new();
        let ty = Ty::Tuple(vec![Ty::I8, Ty::Tuple(vec![Ty::I16, Ty::I32]), Ty::I64]);
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

    #[test]
    fn tuple_projection() {
        let mut pt = PlaceTable::new();
        let local = Local::new(1);
        let ty = Ty::Tuple(vec![Ty::I8, Ty::I32]);
        pt.add_local(local, ty);

        let place = pt
            .reachable_from_local(local)
            .filter(|ppath| !ppath.path.is_empty())
            .map(|ppath| ppath.to_place(&pt))
            .next()
            .unwrap();

        assert!(matches!(place.projection()[0], ProjectionElem::Field(..)));
    }
}
