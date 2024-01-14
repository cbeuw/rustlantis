use std::{collections::HashMap, fmt, mem, ops::Range};

use abi::size::Size;
use index_vec::{define_index_type, IndexVec};
use mir::{
    syntax::{TyId, TyKind},
    tyctxt::TyCtxt,
};
use rangemap::RangeMap;
use smallvec::SmallVec;

use crate::ptable::ProjectionIndex;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum AbstractByte {
    /// An uninitialized byte.
    Uninit,
    /// An initialized byte, optionally with some provenance (if it is encoding a pointer).
    Init,
}

impl fmt::Debug for AbstractByte {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Uninit => write!(f, "UU"),
            Self::Init => write!(f, "II"),
        }
    }
}

impl AbstractByte {
    pub fn is_init(&self) -> bool {
        self == &AbstractByte::Init
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BorrowType {
    Raw,
    Shared,
    Exclusive,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Borrow {
    borrow_type: BorrowType,
    edge: ProjectionIndex,
}

/// A Run represents a contiguous region of memory free of padding
#[derive(Debug, Clone)]
pub struct Run {
    bytes: Box<[AbstractByte]>,
    ref_stack: RangeMap<Vec<Borrow>>,
}

impl Run {
    pub fn new_uninit(size: Size) -> Self {
        let bytes = vec![AbstractByte::Uninit; size.bytes() as usize].into_boxed_slice();
        let ref_stack = RangeMap::new(size, vec![]);
        Self { bytes, ref_stack }
    }

    pub fn size(&self) -> Size {
        Size::from_bytes(self.bytes.len())
    }

    pub fn add_borrow(
        &mut self,
        offset: Size,
        len: Size,
        borrow_type: BorrowType,
        edge: ProjectionIndex,
    ) {
        for (_, stack) in self.ref_stack.iter_mut(offset, len) {
            stack.push(Borrow { borrow_type, edge });
        }
    }

    pub fn remove_borrow(&mut self, offset: Size, len: Size, edge: ProjectionIndex) {
        for (_, stack) in self.ref_stack.iter_mut(offset, len) {
            if let Some(i) = stack.iter().position(|b| b.edge == edge) {
                stack.remove(i);
            }
        }
    }

    /// Gets all edges including and below edge (and therefore potentially borrowed from it)
    pub fn below(&self, offset: Size, len: Size, edge: ProjectionIndex) -> Vec<ProjectionIndex> {
        let mut edges = vec![];
        for (_, stack) in self.ref_stack.iter(offset, len) {
            let index = stack.iter().position(|borrow| borrow.edge == edge);
            if let Some(index) = index {
                edges.extend(stack[index..].iter().map(|borrow| borrow.edge));
            }
        }
        edges
    }

    pub fn below_first_shared(&self, offset: Size, len: Size) -> Vec<ProjectionIndex> {
        let mut edges = vec![];
        for (_, stack) in self.ref_stack.iter(offset, len) {
            let first_shared = stack
                .iter()
                .position(|borrow| borrow.borrow_type == BorrowType::Shared);
            if let Some(first_shared) = first_shared {
                edges.extend(stack[first_shared..].iter().map(|borrow| borrow.edge));
            }
        }
        edges
    }

    pub fn can_write_through(&self, offset: Size, len: Size, edge: ProjectionIndex) -> bool {
        //FIXME: performance
        !self.below_first_shared(offset, len).contains(&edge)
    }
}

define_index_type! {pub struct RunId = u32;}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RunAndOffset(RunId, Size);

impl RunAndOffset {
    pub fn same_run(&self, other: &Self) -> bool {
        self.0 == other.0
    }

    pub fn offset(&self, offset: isize) -> Self {
        Self(self.0, Size::from_bytes(self.1.bytes() as isize + offset))
    }
}

#[derive(Clone)]
struct Allocation {
    /// The data stored in this allocation.
    runs: IndexVec<RunId, Run>,
    /// The alignment that was requested for this allocation.
    // align: Align,
    /// Whether this allocation is still live.
    live: bool,
}

impl Allocation {
    fn runs_and_sizes(&self) -> impl Iterator<Item = (RunId, Size)> + '_ {
        self.runs
            .iter_enumerated()
            .map(|(run_id, run)| (run_id, run.size()))
    }

    fn run(&self, run_and_offset: RunAndOffset) -> &Run {
        &self.runs[run_and_offset.0]
    }
}

pub struct AllocationBuilder {
    alloc_id: AllocId,
    runs: IndexVec<RunId, Run>,
}

impl AllocationBuilder {
    pub fn new_run(&mut self, size: Size) -> RunAndOffset {
        let run = Run::new_uninit(size);
        let run_id = self.runs.push(run);
        RunAndOffset(run_id, Size::ZERO)
    }

    pub fn alloc_id(&self) -> AllocId {
        self.alloc_id
    }

    fn build(self) -> Allocation {
        Allocation {
            runs: self.runs,
            live: true,
        }
    }
}

define_index_type! {pub struct AllocId = u32;}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RunPointer {
    pub alloc_id: AllocId,
    pub run_and_offset: RunAndOffset,
    pub size: Size,
}

impl RunPointer {
    pub fn bytes_range(&self) -> Range<usize> {
        self.run_and_offset.1.bytes_usize()
            ..self.run_and_offset.1.bytes_usize() + self.size.bytes_usize()
    }
}

#[derive(Clone)]
pub struct BasicMemory {
    allocations: IndexVec<AllocId, Allocation>,

    // a lookup table to aid removal from borrow stacks
    // an edge may cover multiple runs, e.g. &(u32, u32),
    pointers: HashMap<ProjectionIndex, SmallVec<[RunPointer; 4]>>,
}

impl BasicMemory {
    const PTR_SIZE: Size = Size::from_bytes_const(mem::size_of::<*const ()>() as u64);

    pub fn new() -> Self {
        Self {
            allocations: IndexVec::new(),
            pointers: HashMap::new(),
        }
    }

    pub fn allocate_with_builder<F>(&mut self, build: F) -> AllocId
    where
        F: FnOnce(&mut AllocationBuilder),
    {
        let alloc_id = self.allocations.len_idx();
        let mut builder = AllocationBuilder {
            alloc_id,
            runs: IndexVec::new(),
        };
        build(&mut builder);
        self.allocations.push(builder.build())
    }

    pub fn deallocate(&mut self, alloc_id: AllocId) {
        self.allocations[alloc_id].live = false;
    }

    pub fn is_live(&self, alloc_id: AllocId) -> bool {
        self.allocations[alloc_id].live
    }

    pub fn bytes(&self, run_ptr: RunPointer) -> &[AbstractByte] {
        assert!(
            self.allocations[run_ptr.alloc_id].live,
            "can't access dead bytes"
        );
        &self.allocations[run_ptr.alloc_id].runs[run_ptr.run_and_offset.0].bytes
            [run_ptr.bytes_range()]
    }

    pub fn fill(&mut self, run_ptr: RunPointer, val: AbstractByte) {
        self.bytes_mut(run_ptr).fill(val);
    }

    pub fn bytes_mut(&mut self, run_ptr: RunPointer) -> &mut [AbstractByte] {
        assert!(
            self.allocations[run_ptr.alloc_id].live,
            "can't access dead bytes"
        );
        &mut self.allocations[run_ptr.alloc_id].runs[run_ptr.run_and_offset.0].bytes
            [run_ptr.bytes_range()]
    }

    pub fn copy(&mut self, dst: RunPointer, src: RunPointer) {
        assert_eq!(dst.size, src.size);
        let tmp = self.bytes(src).to_vec();
        self.bytes_mut(dst).copy_from_slice(&tmp)
    }

    /// Returns Size for types with guaranteed size.
    /// Composite types under the default layout has no guaranteed size,
    /// as the AM is free to insert arbitarily large paddings.
    pub fn ty_size(ty: TyId, tcx: &TyCtxt) -> Option<Size> {
        Some(match ty {
            TyCtxt::UNIT => Size::ZERO,
            TyCtxt::BOOL => Size::from_bytes(1),
            TyCtxt::CHAR => Size::from_bytes(4),
            TyCtxt::I8 | TyCtxt::U8 => Size::from_bits(8),
            TyCtxt::I16 | TyCtxt::U16 => Size::from_bits(16),
            TyCtxt::I32 | TyCtxt::U32 => Size::from_bits(32),
            TyCtxt::I64 | TyCtxt::U64 => Size::from_bits(64),
            TyCtxt::I128 | TyCtxt::U128 => Size::from_bits(128),
            TyCtxt::F32 => Size::from_bits(32),
            TyCtxt::F64 => Size::from_bits(64),
            TyCtxt::ISIZE | TyCtxt::USIZE => Self::PTR_SIZE,
            _ => match ty.kind(tcx) {
                TyKind::RawPtr(..) => Self::PTR_SIZE,
                TyKind::Ref(..) => Self::PTR_SIZE,
                TyKind::Array(ty, len) => {
                    return Self::ty_size(*ty, tcx)
                        .map(|elem| Size::from_bytes(elem.bytes_usize() * len))
                }
                _ => return None,
            },
        })
    }

    pub fn add_ref(&mut self, run_ptr: RunPointer, borrow_type: BorrowType, edge: ProjectionIndex) {
        self.allocations[run_ptr.alloc_id].runs[run_ptr.run_and_offset.0].add_borrow(
            run_ptr.run_and_offset.1,
            run_ptr.size,
            borrow_type,
            edge,
        );
        self.pointers
            .entry(edge)
            .and_modify(|ptrs| ptrs.push(run_ptr))
            .or_insert(SmallVec::from([run_ptr].as_slice()));
    }

    pub fn remove_ref(&mut self, edge: ProjectionIndex) {
        let run_ptrs = self.pointers.remove(&edge);
        if let Some(run_ptrs) = run_ptrs {
            for run_ptr in run_ptrs {
                self.allocations[run_ptr.alloc_id].runs[run_ptr.run_and_offset.0].remove_borrow(
                    run_ptr.run_and_offset.1,
                    run_ptr.size,
                    edge,
                );
            }
        }
    }

    pub fn below_first_shared(&self, run_ptr: RunPointer) -> Vec<ProjectionIndex> {
        self.allocations[run_ptr.alloc_id].runs[run_ptr.run_and_offset.0]
            .below_first_shared(run_ptr.run_and_offset.1, run_ptr.size)
    }

    pub fn can_write_through(&self, run_ptr: RunPointer, edge: ProjectionIndex) -> bool {
        self.allocations[run_ptr.alloc_id].runs[run_ptr.run_and_offset.0].can_write_through(
            run_ptr.run_and_offset.1,
            run_ptr.size,
            edge,
        )
    }
}
