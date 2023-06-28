use std::{fmt, mem, ops::Range};

use abi::size::Size;
use index_vec::{define_index_type, IndexVec};
use mir::{
    syntax::{TyId, TyKind},
    tyctxt::TyCtxt,
};

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

/// A Run represents a contiguous region of memory free of padding
#[derive(Debug, Clone)]
pub struct Run {
    bytes: Box<[AbstractByte]>,
}

impl Run {
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
pub struct RunAndOffset(RunId, Size);

impl RunAndOffset {
    pub fn same_run(&self, other: &Self) -> bool {
        self.0 == other.0
    }

    pub fn offset(&self, offset: isize) -> Self {
        Self(self.0, Size::from_bytes(self.1.bytes() as isize + offset))
    }
}

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

pub struct BasicMemory {
    allocations: IndexVec<AllocId, Allocation>,
}

impl BasicMemory {
    const PTR_SIZE: Size = Size::from_bytes_const(mem::size_of::<*const ()>() as u64);

    pub fn new() -> Self {
        Self {
            allocations: IndexVec::new(),
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
                TyKind::Array(ty, len) => {
                    return Self::ty_size(*ty, tcx)
                        .map(|elem| Size::from_bytes(elem.bytes_usize() * len))
                }
                _ => return None,
            },
        })
    }
}
