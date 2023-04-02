pub mod align;
pub mod size;

use std::{fmt, ops::Index};

use index_vec::{define_index_type, IndexVec};
use mir::syntax::Ty;

use self::size::Size;

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
type Run<Provenance> = Box<[AbstractByte<Provenance>]>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AllocIndex(usize, usize);

impl AllocIndex {
    pub fn same_run(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

struct AllocationBytes<Provenance> {
    runs: Vec<Run<Provenance>>,
}

impl<Provenance: Copy + Clone> AllocationBytes<Provenance> {
    fn new() -> Self {
        Self { runs: vec![] }
    }

    fn new_run(&mut self, size: Size) -> AllocIndex {
        let run = vec![AbstractByte::Uninit; size.bytes() as usize].into_boxed_slice();
        self.runs.push(run);
        AllocIndex(self.runs.len() - 1, 0)
    }
}

impl<Provenance> Index<AllocIndex> for AllocationBytes<Provenance> {
    type Output = AbstractByte<Provenance>;

    fn index(&self, index: AllocIndex) -> &Self::Output {
        &self.runs[index.0][index.1]
    }
}

define_index_type! {pub struct AllocId = u32;}

struct Allocation {
    /// The data stored in this allocation.
    data: AllocationBytes<AllocId>,
    /// The alignment that was requested for this allocation.
    // align: Align,
    /// Whether this allocation is still live.
    live: bool,
}

pub struct BasicMemory {
    allocations: IndexVec<AllocId, Allocation>,
}

impl BasicMemory {
    const PTR_SIZE: Size = Size::from_bytes_const(64);

    pub fn new() -> Self {
        Self {
            allocations: IndexVec::new(),
        }
    }

    pub fn allocate(&mut self) -> AllocId {
        self.allocations.push(Allocation {
            data: AllocationBytes::new(),
            // align,
            live: true,
        })
    }

    pub fn deallocate(&mut self, alloc_id: AllocId) {
        self.allocations[alloc_id].live = false;
    }

    pub fn new_run(&mut self, alloc_id: AllocId, size: Size) -> AllocIndex {
        self.allocations[alloc_id].data.new_run(size)
    }

    pub fn bytes(
        &self,
        alloc_id: AllocId,
        idx: AllocIndex,
        size: Size,
    ) -> &[AbstractByte<AllocId>] {
        &self.allocations[alloc_id].data.runs[idx.0][idx.1..idx.1 + size.bytes() as usize]
    }

    pub fn bytes_mut(
        &mut self,
        alloc_id: AllocId,
        idx: AllocIndex,
        size: Size,
    ) -> &mut [AbstractByte<AllocId>] {
        &mut self.allocations[alloc_id].data.runs[idx.0][idx.1..idx.1 + size.bytes() as usize]
    }

    pub fn ty_size(&self, ty: &Ty) -> Option<Size> {
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
