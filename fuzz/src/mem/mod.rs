mod stacked_borrows;

use std::{alloc::GlobalAlloc, fmt, ops::Index};

use abi::size::Size;
use index_vec::{define_index_type, IndexVec};
use mir::syntax::Ty;
use rangemap::RangeMap;

use self::stacked_borrows::{
    item::{Item, Permission},
    stack::Stack,
    state::GlobalState,
    BorTag, Provenance, Stacks,
};

#[derive(Clone, Copy)]
pub enum AbstractByte<Provenance> {
    /// An uninitialized byte.
    Uninit,
    /// An initialized byte, optionally with some provenance (if it is encoding a pointer).
    Init(Option<Provenance>),
}

impl<Provenance> fmt::Debug for AbstractByte<Provenance> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Uninit => write!(f, "UU"),
            Self::Init(..) => write!(f, "II"),
        }
    }
}

impl<Provenance> AbstractByte<Provenance> {
    pub fn is_init(&self) -> bool {
        matches!(self, AbstractByte::Init(..))
    }

    pub fn provenance(&self) -> Option<&Provenance> {
        match self {
            AbstractByte::Uninit => None,
            AbstractByte::Init(provenance) => provenance.as_ref(),
        }
    }
}

/// A Run represents a contiguous region of memory free of padding
#[derive(Debug, Clone)]
pub struct Run<Provenance> {
    bytes: Box<[AbstractByte<Provenance>]>,
}

impl<Provenance: Copy + Clone> Run<Provenance> {
    pub fn new_uninit(size: Size) -> Self {
        let bytes = vec![AbstractByte::Uninit; size.bytes() as usize].into_boxed_slice();
        Self { bytes }
    }

    pub fn size(&self) -> Size {
        Size::from_bytes(self.bytes.len())
    }
}

define_index_type! {pub struct RunId = u32;}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RunAndOffset(RunId, usize);

impl RunAndOffset {
    pub fn same_run(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}
struct Allocation {
    /// The data stored in this allocation.
    runs: IndexVec<RunId, Run<Provenance>>,
    stacks: Stacks,
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
}

define_index_type! {pub struct AllocId = u32;}

pub struct BasicMemory {
    allocations: IndexVec<AllocId, Allocation>,
    sb_state: GlobalState,
}

impl BasicMemory {
    const PTR_SIZE: Size = Size::from_bytes_const(64);

    pub fn new() -> Self {
        Self {
            allocations: IndexVec::new(),
            sb_state: GlobalState::new(),
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
            stacks: IndexVec::new(),
            perm: Permission::Unique,
            tag: self.sb_state.base_ptr_tag(alloc_id),
        };
        build(&mut builder);
        self.allocations.push(builder.build())
    }

    pub fn deallocate(&mut self, alloc_id: AllocId) {
        self.allocations[alloc_id].live = false;
    }

    pub fn bytes(
        &self,
        alloc_id: AllocId,
        idx: RunAndOffset,
        size: Size,
    ) -> &[AbstractByte<Provenance>] {
        &self.allocations[alloc_id].runs[idx.0].bytes[idx.1..idx.1 + size.bytes() as usize]
    }

    pub fn bytes_mut(
        &mut self,
        alloc_id: AllocId,
        idx: RunAndOffset,
        size: Size,
    ) -> &mut [AbstractByte<Provenance>] {
        &mut self.allocations[alloc_id].runs[idx.0].bytes[idx.1..idx.1 + size.bytes() as usize]
    }

    /// Returns Size for types with guaranteed size.
    /// Composite types under the default layout has no guaranteed size,
    /// as the AM is free to insert arbitarily large paddings.
    pub fn ty_size(ty: &Ty) -> Option<Size> {
        Some(match *ty {
            Ty::Unit => Size::ZERO,
            Ty::Bool => Size::from_bytes(1),
            Ty::Char => Size::from_bytes(1),
            Ty::I8 | Ty::U8 => Size::from_bits(8),
            Ty::I16 | Ty::U16 => Size::from_bits(16),
            Ty::I32 | Ty::U32 => Size::from_bits(32),
            Ty::I64 | Ty::U64 => Size::from_bits(64),
            Ty::I128 | Ty::U128 => Size::from_bits(128),
            Ty::F32 => Size::from_bits(32),
            Ty::F64 => Size::from_bits(64),
            Ty::RawPtr(..) | Ty::ISIZE | Ty::USIZE => Self::PTR_SIZE,
            _ => return None,
        })
    }
}

pub struct AllocationBuilder {
    alloc_id: AllocId,
    runs: IndexVec<RunId, Run<Provenance>>,

    stacks: IndexVec<RunId, RangeMap<Stack>>,
    perm: Permission,
    tag: BorTag,
}

impl AllocationBuilder {
    pub fn new_run(&mut self, size: Size) -> RunAndOffset {
        let run = Run::new_uninit(size);
        let run_id = self.runs.push(run);
        let stacks = RangeMap::new(size, Stack::new(Item::new(self.tag, self.perm, false)));
        self.stacks.push(stacks);

        RunAndOffset(run_id, 0)
    }

    pub fn alloc_id(&self) -> AllocId {
        self.alloc_id
    }

    fn build(self) -> Allocation {
        Allocation {
            runs: self.runs,
            stacks: Stacks::from_stacks(self.stacks),
            live: true,
        }
    }
}
