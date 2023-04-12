use std::collections::VecDeque;

use abi::size::Size;
use bimap::BiBTreeMap;
use mir::syntax::{Body, FieldIdx, Local, Operand, Place, ProjectionElem, Rvalue, Ty};
use petgraph::{prelude::EdgeIndex, stable_graph::NodeIndex, visit::EdgeRef, Direction, Graph};
use smallvec::{smallvec, SmallVec};

use crate::mem::{AbstractByte, AllocId, AllocationBuilder, BasicMemory, RunAndOffset};

type PlaceGraph = Graph<PlaceNode, ProjectionElem>;
pub type PlaceIndex = NodeIndex;
pub type ProjectionIndex = EdgeIndex;
pub type Path = SmallVec<[ProjectionIndex; 4]>;

pub struct PlaceTable {
    current_locals: BiBTreeMap<Local, PlaceIndex>,
    // A program-global graph recording all places that can be reached through projections
    places: PlaceGraph,
    memory: BasicMemory,
}

#[derive(Debug, Clone)]
pub struct PlaceNode {
    pub ty: Ty,
    alloc_id: AllocId,
    pub dataflow: usize,

    // Only Tys fitting into a single Run have these
    run_and_offset: Option<RunAndOffset>,
    size: Option<Size>,
}

pub trait ToPlaceIndex {
    fn to_place_index(&self, pt: &PlaceTable) -> Option<PlaceIndex>;
}

impl ToPlaceIndex for Place {
    fn to_place_index(&self, pt: &PlaceTable) -> Option<PlaceIndex> {
        pt.get_node(self)
    }
}

impl ToPlaceIndex for Local {
    fn to_place_index(&self, pt: &PlaceTable) -> Option<PlaceIndex> {
        pt.get_node(&Place::from_local(*self))
    }
}

impl ToPlaceIndex for PlaceIndex {
    fn to_place_index(&self, _: &PlaceTable) -> Option<PlaceIndex> {
        Some(*self)
    }
}

impl<T> ToPlaceIndex for &T
where
    T: ToPlaceIndex,
{
    fn to_place_index(&self, pt: &PlaceTable) -> Option<PlaceIndex> {
        (*self).to_place_index(pt)
    }
}

impl PlaceTable {
    pub fn new() -> Self {
        Self {
            current_locals: BiBTreeMap::new(),
            places: Graph::default(),
            memory: BasicMemory::new(),
        }
    }

    pub fn enter_fn0(&mut self, body: &Body) {
        self.current_locals = BiBTreeMap::new();

        // Declare args
        body.args_decl_iter().for_each(|(local, decl)| {
            let pidx = self.allocate_local(local, decl.ty.clone());
            // encourage use of args
            self.places[pidx].dataflow = 5;
        });

        // Prepare return place
        let mut return_pidx = Default::default();
        self.memory.allocate_with_builder(|builder| {
            return_pidx = Self::add_place(&mut self.places, body.return_ty(), builder, 0);
        });
        self.current_locals
            .insert_no_overwrite(Local::RET, return_pidx)
            .expect("return place did not already exist");
    }

    pub fn enter_fn(&mut self, body: &Body, args: &[Place]) {
        // Get the PlaceIndices before frame switch
        let args: Vec<PlaceIndex> = args
            .iter()
            .map(|p| p.to_place_index(self).expect("place is in current frame"))
            .collect();
        let return_place = Place::RETURN_SLOT
            .to_place_index(self)
            .expect("return slot is in current frame");

        self.current_locals = BiBTreeMap::new();
        body.args_decl_iter()
            .zip(args)
            .for_each(|((local, decl), source)| {
                let pidx = self.allocate_local(local, decl.ty.clone());
                debug_assert!(
                    self.is_place_init(source),
                    "function arguments must be init"
                );

                // encourage use of args
                self.places[pidx].dataflow = self.places[source].dataflow;
                // FIXME: copy memory from arg to the new places
            });
        self.current_locals
            .insert_no_overwrite(Local::RET, return_place)
            .expect("return place did not already exist");
    }

    pub fn allocate_local(&mut self, local: Local, ty: Ty) -> PlaceIndex {
        let mut pidx = Default::default();
        self.memory.allocate_with_builder(|builder| {
            pidx = Self::add_place(&mut self.places, ty, builder, 0);
        });
        self.current_locals
            .insert_no_overwrite(local, pidx)
            .expect("did not insert existing local or place");
        pidx
    }

    fn add_place(
        places: &mut PlaceGraph,
        ty: Ty,
        alloc_builder: &mut AllocationBuilder,
        dataflow: usize,
    ) -> PlaceIndex {
        let pidx = if let Some(size) = BasicMemory::ty_size(&ty) {
            // FIXME: don't always allocate Runs
            let offset = alloc_builder.new_run(size);
            places.add_node(PlaceNode {
                ty: ty.clone(),
                alloc_id: alloc_builder.alloc_id(),
                dataflow,
                run_and_offset: Some(offset),
                size: Some(size),
            })
        } else {
            places.add_node(PlaceNode {
                ty: ty.clone(),
                alloc_id: alloc_builder.alloc_id(),
                dataflow,
                run_and_offset: None,
                size: None,
            })
        };
        match ty {
            Ty::Tuple(elems) => elems.iter().enumerate().for_each(|(idx, elem)| {
                let sub_pidx = Self::add_place(places, elem.clone(), alloc_builder, dataflow);
                places.add_edge(
                    pidx,
                    sub_pidx,
                    ProjectionElem::TupleField(FieldIdx::new(idx)),
                );
            }),
            Ty::Adt(_) => todo!(),
            Ty::RawPtr(..) => { /* pointer has no subfields  */ }
            _ => { /* primitives, no projection */ }
        }
        pidx
    }

    /// Get PlaceIndex from a Place
    fn get_node(&self, place: &Place) -> Option<PlaceIndex> {
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

    fn update_transitive_superfields<F>(&mut self, start: PlaceIndex, mut update: F)
    where
        F: FnMut(&mut Self, PlaceIndex) -> bool + Copy,
    {
        let supers: Vec<PlaceIndex> = self.immediate_superfields(start).collect();
        for place in supers {
            let cont = update(self, place);
            if cont {
                self.update_transitive_superfields(place, update);
            } else {
                continue;
            }
        }
    }

    fn update_transitive_subfields<F>(&mut self, start: PlaceIndex, mut update: F)
    where
        F: FnMut(&mut Self, PlaceIndex) -> bool + Copy,
    {
        let subs: Vec<PlaceIndex> = self.immediate_subfields(start).collect();
        for place in subs {
            let cont = update(self, place);
            if cont {
                self.update_transitive_subfields(place, update);
            } else {
                continue;
            }
        }
    }

    fn update_dataflow(&mut self, target: PlaceIndex, new_flow: usize) {
        self.places[target].dataflow = new_flow;

        // Subplaces' complexity is overwritten as target's new complexity
        self.update_transitive_subfields(target, |this, place| {
            this.places[place].dataflow = new_flow;
            true
        });

        // Superplaces' complexity is updated to be the max of its children
        self.update_transitive_superfields(target, |this, place| {
            if let Some(max) = this
                .immediate_subfields(place)
                .map(|sub| this.places[sub].dataflow)
                .max()
            {
                this.places[place].dataflow = max;
            }
            true
        })
    }

    pub fn combine_dataflow(&mut self, target: impl ToPlaceIndex, source: impl HasDataflow) {
        let new_flow = source.dataflow(self);
        let target = target.to_place_index(self).expect("place exists");
        self.update_dataflow(target, new_flow)
    }

    pub fn mark_place_init(&mut self, p: impl ToPlaceIndex) {
        let pidx = p.to_place_index(self).unwrap();
        let node = &self.places[pidx];
        if let (Some(offset), Some(size)) = (node.run_and_offset, node.size) {
            self.memory
                .bytes_mut(node.alloc_id, offset, size)
                .iter_mut()
                .for_each(|b| *b = AbstractByte::Init(None));
        }
        self.update_transitive_subfields(pidx, |this, place| {
            let node = &this.places[place];
            if let (Some(offset), Some(size)) = (node.run_and_offset, node.size) {
                this.memory
                    .bytes_mut(node.alloc_id, offset, size)
                    .iter_mut()
                    .for_each(|b| *b = AbstractByte::Init(None));
                false
            } else {
                true
            }
        });
    }

    pub fn set_ref(&mut self, reference: impl ToPlaceIndex, referent: impl ToPlaceIndex) {
        let reference = reference.to_place_index(self).expect("place exists");
        let referent = referent.to_place_index(self).expect("place exists");

        // Remove any old reference edges
        let old = self
            .places
            .edges_directed(reference, Direction::Outgoing)
            .next();
        if let Some(old) = old {
            self.places.remove_edge(old.id());
        }
        assert_eq!(
            self.places
                .edges_directed(reference, Direction::Outgoing)
                .count(),
            0
        );

        // Add new reference
        self.places
            .add_edge(reference, referent, ProjectionElem::Deref);
    }

    pub fn is_place_init(&self, p: impl ToPlaceIndex) -> bool {
        let pidx = p.to_place_index(self).unwrap();
        let node = &self.places[pidx];
        if let (Some(offset), Some(size)) = (node.run_and_offset, node.size) {
            self.memory
                .bytes(node.alloc_id, offset, size)
                .iter()
                .all(|b| b.is_init())
        } else {
            self.immediate_subfields(pidx)
                .all(|sub| self.is_place_init(sub))
        }
    }

    fn immediate_subfields(&self, pidx: PlaceIndex) -> impl Iterator<Item = PlaceIndex> + '_ {
        self.places
            .edges_directed(pidx, Direction::Outgoing)
            .filter_map(|e| {
                if *e.weight() == ProjectionElem::Deref {
                    None
                } else {
                    Some(e.target())
                }
            })
    }

    fn immediate_superfields(&self, pidx: PlaceIndex) -> impl Iterator<Item = PlaceIndex> + '_ {
        self.places
            .edges_directed(pidx, Direction::Incoming)
            .filter_map(|e| {
                if *e.weight() == ProjectionElem::Deref {
                    None
                } else {
                    Some(e.source())
                }
            })
    }

    // Returns an iterator over all places reachable from local through projections
    fn reachable_from_local(&self, local: Local) -> ProjectionIter<'_> {
        let local_node = *self.current_locals.get_by_left(&local).unwrap();
        ProjectionIter::new(self, local_node, true, true)
    }

    pub fn reachable_nodes(&self) -> impl Iterator<Item = PlacePath> + Clone + '_ {
        let local_iter = self.current_locals.left_values();
        local_iter.flat_map(|&local| self.reachable_from_local(local))
    }

    pub fn place_count(&self) -> usize {
        self.places.node_count()
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
/// TODO: maybe dfs is fine
#[derive(Clone)]
pub struct ProjectionIter<'pt> {
    pt: &'pt PlaceTable,
    root: NodeIndex,
    to_visit: VecDeque<Path>,
    root_visited: bool,
    follow_deref: bool,
}

impl<'pt> ProjectionIter<'pt> {
    fn new(pt: &'pt PlaceTable, root: PlaceIndex, visit_root: bool, follow_deref: bool) -> Self {
        ProjectionIter {
            pt,
            root,
            to_visit: pt
                .places
                .edges_directed(root, Direction::Outgoing)
                .filter_map(|e| {
                    if follow_deref || *e.weight() != ProjectionElem::Deref {
                        Some(smallvec![e.id()])
                    } else {
                        None
                    }
                })
                .collect(),
            root_visited: !visit_root,
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
            self.to_visit.extend(new_edges.filter_map(|e| {
                if self.follow_deref || *e.weight() != ProjectionElem::Deref {
                    let mut new_path = path.clone();
                    new_path.push(e.id());
                    Some(new_path)
                } else {
                    None
                }
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

pub trait HasDataflow {
    fn dataflow(&self, pt: &PlaceTable) -> usize;
}

impl HasDataflow for Place {
    fn dataflow(&self, pt: &PlaceTable) -> usize {
        pt.places[self.to_place_index(pt).expect("place exists")].dataflow
    }
}

impl HasDataflow for Operand {
    fn dataflow(&self, pt: &PlaceTable) -> usize {
        match self {
            Operand::Copy(place) | Operand::Move(place) => place.dataflow(pt),
            Operand::Constant(_) => 1,
        }
    }
}

impl HasDataflow for Rvalue {
    fn dataflow(&self, pt: &PlaceTable) -> usize {
        match self {
            Rvalue::Use(operand) | Rvalue::Cast(operand, _) | Rvalue::UnaryOp(_, operand) => {
                operand.dataflow(pt)
            }
            Rvalue::BinaryOp(_, l, r) | Rvalue::CheckedBinaryOp(_, l, r) => {
                l.dataflow(pt) + r.dataflow(pt)
            }
            Rvalue::Len(_) => 1,
            Rvalue::Discriminant(place) => place.dataflow(pt),
            Rvalue::AddressOf(_, place) => place.dataflow(pt),
            Rvalue::Hole => unreachable!("hole"),
        }
    }
}

impl<T> HasDataflow for &T
where
    T: HasDataflow,
{
    fn dataflow(&self, pt: &PlaceTable) -> usize {
        (*self).dataflow(pt)
    }
}

#[cfg(test)]
mod tests {
    use mir::syntax::{BinOp, FieldIdx, Local, Operand, Place, ProjectionElem, Rvalue, Ty};

    use crate::ptable::HasDataflow;

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
        pt.allocate_local(local, ty);

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
        pt.allocate_local(local, ty);

        let place = pt
            .reachable_from_local(local)
            .filter(|ppath| !ppath.path.is_empty())
            .map(|ppath| ppath.to_place(&pt))
            .next()
            .unwrap();

        assert!(matches!(
            place.projection()[0],
            ProjectionElem::TupleField(..)
        ));
    }

    #[test]
    fn recursive_init() {
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
        pt.allocate_local(local, ty);

        let i8 = Place::from_projected(local, &[ProjectionElem::TupleField(FieldIdx::new(0))]);
        let i16_i32 = Place::from_projected(local, &[ProjectionElem::TupleField(FieldIdx::new(1))]);
        let i64 = Place::from_projected(local, &[ProjectionElem::TupleField(FieldIdx::new(2))]);

        let i16 = i16_i32.project(ProjectionElem::TupleField(FieldIdx::new(0)));
        let i32 = i16_i32.project(ProjectionElem::TupleField(FieldIdx::new(1)));

        pt.mark_place_init(&i8);
        assert!(pt.is_place_init(&i8));
        assert!(!pt.is_place_init(local));

        pt.mark_place_init(&i16_i32);
        assert!(pt.is_place_init(&i16));
        assert!(pt.is_place_init(&i32));
        assert!(!pt.is_place_init(local));

        pt.mark_place_init(&i64);
        assert!(pt.is_place_init(local));
    }

    #[test]
    fn dataflow() {
        /*
            ┌──────┬──────┐
            │      │      │
            a      │      c
                ┌──b──┐
                │     │
                d     e
        */

        let mut pt = PlaceTable::new();
        let ty = Ty::Tuple(vec![Ty::I8, Ty::Tuple(vec![Ty::I8, Ty::I8]), Ty::I8]);
        let local = Local::new(1);
        pt.allocate_local(local, ty);

        let a = Place::from_projected(local, &[ProjectionElem::TupleField(FieldIdx::new(0))]);
        let b = Place::from_projected(local, &[ProjectionElem::TupleField(FieldIdx::new(1))]);
        let c = Place::from_projected(local, &[ProjectionElem::TupleField(FieldIdx::new(2))]);

        let d = b.project(ProjectionElem::TupleField(FieldIdx::new(0)));
        let e = b.project(ProjectionElem::TupleField(FieldIdx::new(1)));

        pt.combine_dataflow(&a, Rvalue::Use(Operand::Constant(1.into())));
        assert_eq!(a.dataflow(&pt), 1);
        assert_eq!(Place::from(local).dataflow(&pt), 1);
        pt.combine_dataflow(&c, Rvalue::Use(Operand::Constant(1.into())));
        assert_eq!(c.dataflow(&pt), 1);
        assert_eq!(Place::from(local).dataflow(&pt), 1);

        pt.combine_dataflow(
            &d,
            Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Copy(a.clone()),
                Operand::Copy(c.clone()),
            ),
        );
        assert_eq!(d.dataflow(&pt), 2);

        pt.combine_dataflow(&e, Rvalue::Use(Operand::Constant(1.into())));
        assert_eq!(b.dataflow(&pt), 2);

        assert_eq!(Place::from(local).dataflow(&pt), 2);
    }
}
