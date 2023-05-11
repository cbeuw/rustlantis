use std::vec;

use bimap::BiBTreeMap;
use mir::syntax::{Body, FieldIdx, Local, Operand, Place, ProjectionElem, Rvalue, Ty};
use petgraph::{prelude::EdgeIndex, stable_graph::NodeIndex, visit::EdgeRef, Direction, Graph};
use smallvec::{smallvec, SmallVec};

use crate::mem::{AbstractByte, AllocId, AllocationBuilder, BasicMemory, RunPointer};

type PlaceGraph = Graph<PlaceNode, ProjectionElem>;
pub type PlaceIndex = NodeIndex;
pub type ProjectionIndex = EdgeIndex;
pub type Path = SmallVec<[ProjectionIndex; 4]>;

type Frame = BiBTreeMap<Local, PlaceIndex>;

pub struct PlaceTable {
    /// The callstack and return destination stack
    frames: Vec<(Frame, PlaceIndex)>,

    /// A program-global graph recording all places that can be reached through projections
    places: PlaceGraph,
    memory: BasicMemory,
}

#[derive(Debug, Clone)]
pub struct PlaceNode {
    pub ty: Ty,
    alloc_id: AllocId,
    dataflow: usize,

    // Only Tys fitting into a single Run have these
    run_ptr: Option<RunPointer>,
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
            frames: vec![(
                BiBTreeMap::new(),
                /* fn0 dummy */ PlaceIndex::new(usize::MAX),
            )],
            places: Graph::default(),
            memory: BasicMemory::new(),
        }
    }

    fn current_locals(&self) -> &BiBTreeMap<Local, PlaceIndex> {
        &self.frames.last().expect("call stack isn't empty").0
    }

    fn current_locals_mut(&mut self) -> &mut BiBTreeMap<Local, PlaceIndex> {
        &mut self.frames.last_mut().expect("call stack isn't empty").0
    }

    pub fn enter_fn0(&mut self, body: &Body) {
        // Declare return place
        self.allocate_local(Local::RET, body.return_ty());
        // Declare args
        body.args_decl_iter().for_each(|(local, decl)| {
            let pidx = self.allocate_local(local, decl.ty.clone());
            // encourage use of args
            self.places[pidx].dataflow = 5;
        });
    }

    pub fn enter_fn(&mut self, body: &Body, args: &[Operand], return_dest: &Place) {
        // Get the PlaceIndices before frame switch
        enum ArgOperand {
            Copy(PlaceIndex),
            Move(PlaceIndex),
            Constant,
        }

        let args: Vec<ArgOperand> = args
            .iter()
            .map(|p| match p {
                Operand::Copy(place) => {
                    ArgOperand::Copy(place.to_place_index(self).expect("arg exists"))
                }
                Operand::Move(place) => {
                    ArgOperand::Move(place.to_place_index(self).expect("arg exists"))
                }
                Operand::Constant(_) => ArgOperand::Constant,
            })
            .collect();

        let return_dest = return_dest
            .to_place_index(self)
            .expect("return dest exists");

        // Frame switch
        self.frames.push((BiBTreeMap::new(), return_dest));
        self.allocate_local(Local::RET, body.return_ty());
        body.args_decl_iter()
            .zip(args)
            .for_each(|((local, decl), arg)| {
                let pidx = self.allocate_local(local, decl.ty.clone());

                if let ArgOperand::Copy(source_pidx) | ArgOperand::Move(source_pidx) = arg {
                    debug_assert!(
                        self.is_place_init(source_pidx),
                        "function arguments must be init"
                    );
                    self.copy_place(pidx, source_pidx);
                }
                if let ArgOperand::Move(source_pidx) = arg {
                    self.mark_place_moved(source_pidx);
                }
            });
    }

    pub fn exit_fn(&mut self) {
        // FIXME: this is quite flimsy wrt. statement order
        let callee_ret = Place::RETURN_SLOT
            .to_place_index(self)
            .expect("place exists");
        let (popped_frame, caller_dest) = self.frames.pop().expect("call stack isn't empty");
        // Copy ret
        self.copy_place(caller_dest, callee_ret);

        // Deinit places
        for pidx in popped_frame.right_values() {
            self.memory.deallocate(self.places[*pidx].alloc_id);
        }
    }

    pub fn allocate_local(&mut self, local: Local, ty: Ty) -> PlaceIndex {
        let mut pidx = Default::default();
        self.memory.allocate_with_builder(|builder| {
            pidx = Self::add_place(&mut self.places, ty, builder, 0);
        });
        self.current_locals_mut()
            .insert_no_overwrite(local, pidx)
            .expect("did not insert existing local or place");
        pidx
    }

    pub fn deallocate_local(&mut self, local: Local) {
        let (_, pidx) = self
            .current_locals_mut()
            .remove_by_left(&local)
            .expect("local exists");
        self.memory.deallocate(self.places[pidx].alloc_id);
    }

    fn add_place(
        places: &mut PlaceGraph,
        ty: Ty,
        alloc_builder: &mut AllocationBuilder,
        dataflow: usize,
    ) -> PlaceIndex {
        let alloc_id = alloc_builder.alloc_id();
        let pidx = if let Some(size) = BasicMemory::ty_size(&ty) {
            // FIXME: don't always allocate Runs
            let run_and_offset = alloc_builder.new_run(size);
            places.add_node(PlaceNode {
                ty: ty.clone(),
                alloc_id,
                dataflow,
                run_ptr: Some(RunPointer {
                    alloc_id,
                    run_and_offset,
                    size,
                }),
            })
        } else {
            places.add_node(PlaceNode {
                ty: ty.clone(),
                alloc_id,
                dataflow,
                run_ptr: None,
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

    pub fn copy_place(&mut self, dst: impl ToPlaceIndex, src: impl ToPlaceIndex) {
        let dst = dst.to_place_index(self).expect("place exists");
        let src = src.to_place_index(self).expect("place exists");
        if dst == src {
            return;
        }
        self.update_dataflow(dst, self.places[src].dataflow);

        let (dst_node, src_node) = self.places.index_twice_mut(dst, src);
        assert_eq!(dst_node.ty, src_node.ty);
        if let Some(run_ptr) = src_node.run_ptr {
            self.memory
                .copy(dst_node.run_ptr.expect("dst is terminal"), run_ptr);

            if dst_node.ty.is_any_ptr() {
                self.alias_ref(src, dst);
            }
        } else {
            let projs: Vec<_> = self
                .places
                .edges_directed(dst, Direction::Outgoing)
                .filter_map(|e| (!e.weight().is_deref()).then_some(e.weight()))
                .copied()
                .collect();
            for proj in projs {
                let new_dst = self
                    .project_from_node(dst, &proj)
                    .expect("projection exists");
                let new_src = self
                    .project_from_node(src, &proj)
                    .expect("projection exists");
                self.copy_place(new_dst, new_src);
            }
        }
    }

    fn project_from_node(&self, pidx: PlaceIndex, proj: &ProjectionElem) -> Option<PlaceIndex> {
        self.places
            .edges_directed(pidx, Direction::Outgoing)
            .find(|edge| edge.weight() == proj)
            .map(|e| e.target())
    }

    /// Get PlaceIndex from a Place
    fn get_node(&self, place: &Place) -> Option<PlaceIndex> {
        let mut node = *self.current_locals().get_by_left(&place.local())?;
        let proj_iter = place.projection().iter();
        for proj in proj_iter {
            let next = self.project_from_node(node, proj);
            if let Some(next) = next {
                node = next;
            } else {
                return None;
            }
        }
        Some(node)
    }

    /// Call update on all transitive superfields of start, *excluding* start
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

    /// Call update on all transitive subfields of start, *including* start
    fn update_transitive_subfields<F>(&mut self, start: PlaceIndex, mut update: F)
    where
        F: FnMut(&mut Self, PlaceIndex) -> bool + Copy,
    {
        let cont = update(self, start);
        if cont {
            let subs: Vec<PlaceIndex> = self.immediate_subfields(start).collect();
            for place in subs {
                self.update_transitive_subfields(place, update);
            }
        }
    }

    fn update_dataflow(&mut self, target: PlaceIndex, new_flow: usize) {
        let new_flow = new_flow.min(100);

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

    pub fn get_dataflow(&self, p: impl ToPlaceIndex) -> usize {
        let pidx = p.to_place_index(self).unwrap();
        let node = &self.places[pidx];
        if node.ty.is_any_ptr() {
            if let Some(pointee) = self.project_from_node(pidx, &ProjectionElem::Deref) {
                self.get_dataflow(pointee)
            } else {
                // Use the initial dataflow
                node.dataflow
            }
        } else {
            node.dataflow
        }
    }

    pub fn mark_place_moved(&mut self, p: impl ToPlaceIndex) {
        todo!();
    }

    pub fn mark_place_uninit(&mut self, p: impl ToPlaceIndex) {
        let pidx = p.to_place_index(self).unwrap();

        // If this is a pointer, we have to remove the Deref edge, but not for other projections
        if self.places[pidx].ty.is_any_ptr() && let Some(old) = self.ref_edge(pidx) {
            self.places.remove_edge(old);
        }

        self.update_transitive_subfields(pidx, |this, place| {
            let node = &this.places[place];
            if let Some(run_ptr) = node.run_ptr {
                this.memory
                    .bytes_mut(run_ptr)
                    .iter_mut()
                    .for_each(|b| *b = AbstractByte::Uninit);
                false
            } else {
                true
            }
        });
    }

    pub fn mark_place_init(&mut self, p: impl ToPlaceIndex) {
        let pidx = p.to_place_index(self).unwrap();
        self.update_transitive_subfields(pidx, |this, place| {
            let node = &this.places[place];
            if let Some(run_ptr) = node.run_ptr {
                this.memory
                    .bytes_mut(run_ptr)
                    .iter_mut()
                    .for_each(|b| *b = AbstractByte::Init(None));
                false
            } else {
                true
            }
        });
    }

    /// Returns the pointee in reference -[Deref]-> pointee, if one exists
    fn pointee(&self, reference: PlaceIndex) -> Option<PlaceIndex> {
        assert!(self.places[reference].ty.is_any_ptr());
        self.places
            .edges_directed(reference, Direction::Outgoing)
            .next()
            .map(|deref| deref.target())
    }

    /// Returns the edge in reference -[edge: Deref]-> pointee, if one exists
    fn ref_edge(&self, reference: PlaceIndex) -> Option<ProjectionIndex> {
        assert!(self.places[reference].ty.is_any_ptr());
        self.places
            .edges_directed(reference, Direction::Outgoing)
            .next()
            .map(|deref| deref.id())
    }

    /// Make alias such that original_ref -[Deref]-> pointee <-[Deref]- alias_ref, if one exists
    pub fn alias_ref(&mut self, original_ref: impl ToPlaceIndex, alias_ref: impl ToPlaceIndex) {
        let original_ref = original_ref.to_place_index(self).expect("place exists");
        if let Some(pointee) = self.pointee(original_ref) {
            self.set_ref(alias_ref, pointee);
        }
    }

    /// Creates an edge reference -[Deref]-> pointee
    pub fn set_ref(&mut self, reference: impl ToPlaceIndex, pointee: impl ToPlaceIndex) {
        let reference = reference.to_place_index(self).expect("place exists");
        let pointee = pointee.to_place_index(self).expect("place exists");

        assert_eq!(
            self.places[reference].ty.pointee_ty().unwrap(),
            self.places[pointee].ty
        );

        // Remove any old reference edges
        if let Some(old) = self.ref_edge(reference) {
            self.places.remove_edge(old);
        }
        assert_eq!(
            self.places
                .edges_directed(reference, Direction::Outgoing)
                .count(),
            0
        );

        self.update_dataflow(reference, self.places[pointee].dataflow);

        // Add new reference
        self.places
            .add_edge(reference, pointee, ProjectionElem::Deref);
    }

    pub fn is_place_live(&self, p: impl ToPlaceIndex) -> bool {
        let Some(pidx) = p.to_place_index(self) else {
            return false;
        };
        let node = &self.places[pidx];
        self.memory.is_live(node.alloc_id)
    }

    pub fn is_place_init(&self, p: impl ToPlaceIndex) -> bool {
        if !self.is_place_live(&p) {
            return false;
        }
        let pidx = p.to_place_index(self).unwrap();
        let node = &self.places[pidx];
        if let Some(run_ptr) = node.run_ptr {
            self.memory.bytes(run_ptr).iter().all(|b| b.is_init())
        } else {
            self.immediate_subfields(pidx)
                .all(|sub| self.is_place_init(sub))
        }
    }

    fn immediate_subfields(&self, pidx: PlaceIndex) -> impl Iterator<Item = PlaceIndex> + '_ {
        self.places
            .edges_directed(pidx, Direction::Outgoing)
            .filter_map(|e| (!e.weight().is_deref()).then_some(e.target()))
    }

    fn immediate_superfields(&self, pidx: PlaceIndex) -> impl Iterator<Item = PlaceIndex> + '_ {
        self.places
            .edges_directed(pidx, Direction::Incoming)
            .filter_map(|e| (!e.weight().is_deref()).then_some(e.source()))
    }

    // Returns an iterator over all places reachable from local through projections
    fn reachable_from_local(&self, local: Local) -> ProjectionIter<'_> {
        let local_node = *self.current_locals().get_by_left(&local).unwrap();
        ProjectionIter::new(self, local_node, true, true)
    }

    pub fn reachable_nodes(&self) -> impl Iterator<Item = PlacePath> + Clone + '_ {
        let local_iter = self.current_locals().left_values();
        local_iter.flat_map(|&local| self.reachable_from_local(local))
    }

    /// Whether two places overlap or alias
    pub fn overlap(&self, a: impl ToPlaceIndex, b: impl ToPlaceIndex) -> bool {
        let a = a.to_place_index(self).expect("place exists");
        let b = b.to_place_index(self).expect("place exists");

        let a_sub = ProjectionIter::new(self, a, true, false).map(|ppath| ppath.target_index(self));
        let b_sub: Vec<_> = ProjectionIter::new(self, b, true, false)
            .map(|ppath| ppath.target_index(self))
            .collect();

        for a_node in a_sub {
            for b_node in &b_sub {
                if a_node == *b_node {
                    return true;
                }
            }
        }
        false
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
            *pt.current_locals().get_by_right(&self.source).unwrap(),
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

/// A depth-first iterator over all projections from a local variable
/// FIXME: this breaks if there's a reference cycle in the graph
#[derive(Clone)]
pub struct ProjectionIter<'pt> {
    pt: &'pt PlaceTable,
    root: PlaceIndex,
    path: Path,
    // Stack of nodes to visit and their depth (number of projections from root)
    to_visit: Vec<(ProjectionIndex, usize)>,

    root_visited: bool,
}

impl<'pt> ProjectionIter<'pt> {
    fn new(pt: &'pt PlaceTable, root: PlaceIndex, visit_root: bool, follow_deref: bool) -> Self {
        ProjectionIter {
            pt,
            root,
            path: smallvec![],
            to_visit: pt
                .places
                .edges_directed(root, Direction::Outgoing)
                .filter_map(|e| {
                    if follow_deref || !e.weight().is_deref() {
                        Some((e.id(), 1))
                    } else {
                        None
                    }
                })
                .collect(),
            root_visited: !visit_root,
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
        if let Some((edge, depth)) = self.to_visit.pop() {
            let (_, target) = self.pt.places.edge_endpoints(edge).unwrap();
            self.path.truncate(depth - 1);
            self.path.push(edge);

            let new_edges = self.pt.places.edges_directed(target, Direction::Outgoing);
            self.to_visit.extend(new_edges.filter_map(|e| {
                // Do not follow deref edges since we are not root
                (!e.weight().is_deref()).then_some((e.id(), depth + 1))
            }));

            Some(PlacePath {
                source: self.root,
                path: self.path.clone(),
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
    use mir::syntax::{
        BinOp, FieldIdx, Local, Mutability, Operand, Place, ProjectionElem, Rvalue, Ty,
    };

    use crate::ptable::{HasDataflow, PlaceIndex, ToPlaceIndex};

    use super::PlaceTable;

    fn prepare_t() -> (PlaceTable, Local, Place, Place, Place, Place, Place) {
        /*
            ┌──────┬──────┐
            │      │      │
            a      │      c
                ┌──b──┐
                │     │
                d     e
        */

        let mut pt = PlaceTable::new();
        let ty = Ty::Tuple(vec![Ty::I8, Ty::Tuple(vec![Ty::I16, Ty::I32]), Ty::I64]);
        let local = Local::new(1);
        pt.allocate_local(local, ty);

        let a = Place::from_projected(local, &[ProjectionElem::TupleField(FieldIdx::new(0))]);
        let b = Place::from_projected(local, &[ProjectionElem::TupleField(FieldIdx::new(1))]);
        let c = Place::from_projected(local, &[ProjectionElem::TupleField(FieldIdx::new(2))]);

        let d = b
            .clone()
            .project(ProjectionElem::TupleField(FieldIdx::new(0)))
            .clone();
        let e = b
            .clone()
            .project(ProjectionElem::TupleField(FieldIdx::new(1)))
            .clone();
        (pt, local, a, b, c, d, e)
    }

    #[test]
    fn nested_tuple() {
        let (pt, local, ..) = prepare_t();

        let visited: Vec<Ty> = pt
            .reachable_from_local(local)
            .map(|ppath| ppath.target_node(&pt).ty.clone())
            .collect();
        assert_eq!(
            &visited,
            &[
                Ty::Tuple(vec![Ty::I8, Ty::Tuple(vec![Ty::I16, Ty::I32]), Ty::I64]), // (i8, (i16, i32), i64)
                Ty::I8,                                                              // i8
                Ty::Tuple(vec![Ty::I16, Ty::I32]),                                   // (i16, 132)
                Ty::I16,                                                             // i16
                Ty::I32,                                                             // i32
                Ty::I64,                                                             // i64
            ]
        );
    }

    #[test]
    fn overlap_check() {
        let (pt, local, a, b, c, d, _) = prepare_t();

        assert!(pt.overlap(&b, &local));
        assert!(pt.overlap(&local, &b));
        assert!(pt.overlap(&local, &d));

        assert!(!pt.overlap(&a, &c));
        assert!(!pt.overlap(&a, &d))
    }

    #[test]
    fn pointers() {
        let mut pt = PlaceTable::new();
        // *const (*const i32,)
        let ty = Ty::RawPtr(
            Box::new(Ty::Tuple(vec![Ty::RawPtr(
                Box::new(Ty::I32),
                Mutability::Not,
            )])),
            Mutability::Not,
        );
        let root = Local::new(1);
        pt.allocate_local(root, ty);

        let tuple = Local::new(2);
        pt.allocate_local(
            tuple,
            Ty::Tuple(vec![Ty::RawPtr(Box::new(Ty::I32), Mutability::Not)]),
        );

        let int = Local::new(3);
        pt.allocate_local(int, Ty::I32);

        // root -[Deref]-> tuple -[Field(0)]-> tuple.0 -[Deref]-> int
        let tuple_0 = Place::from_projected(
            tuple,
            &[ProjectionElem::TupleField(FieldIdx::from_usize(0))],
        );
        pt.set_ref(tuple_0.clone(), int);

        pt.set_ref(root, tuple);

        let visited: Vec<PlaceIndex> = pt
            .reachable_from_local(root)
            .map(|ppath| ppath.target_index(&pt))
            .collect();

        // int is not reachable because it is behind a Field projection
        assert_eq!(
            &visited,
            &[
                root.to_place_index(&pt).unwrap(),
                tuple.to_place_index(&pt).unwrap(),
                tuple_0.to_place_index(&pt).unwrap(),
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
        let (mut pt, local, a, b, c, d, e) = prepare_t();

        pt.mark_place_init(&a);
        assert!(pt.is_place_init(&a));
        assert!(!pt.is_place_init(local));

        pt.mark_place_init(&b);
        assert!(pt.is_place_init(&d));
        assert!(pt.is_place_init(&e));
        assert!(!pt.is_place_init(local));

        pt.mark_place_init(&c);
        assert!(pt.is_place_init(local));
    }

    #[test]
    fn recursive_uninit() {
        let (mut pt, local, a, b, c, d, e) = prepare_t();
        pt.mark_place_init(local);

        pt.mark_place_uninit(&d);
        assert!(!pt.is_place_init(&d));

        pt.mark_place_uninit(&e);
        assert!(!pt.is_place_init(&b));

        pt.mark_place_uninit(local);
        assert!(!pt.is_place_init(&a));
        assert!(!pt.is_place_init(&c));
    }

    #[test]
    fn dataflow() {
        let (mut pt, local, a, b, c, d, e) = prepare_t();

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
