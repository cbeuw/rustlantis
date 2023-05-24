mod stacked_borrows;

use std::{fmt, ops::Range};

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

    fn run(&self, run_and_offset: RunAndOffset) -> &Run<Provenance> {
        &self.runs[run_and_offset.0]
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

        RunAndOffset(run_id, Size::ZERO)
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

    pub fn is_live(&self, alloc_id: AllocId) -> bool {
        self.allocations[alloc_id].live
    }

    pub fn bytes(&self, run_ptr: RunPointer) -> &[AbstractByte<Provenance>] {
        assert!(
            self.allocations[run_ptr.alloc_id].live,
            "can't access dead bytes"
        );
        &self.allocations[run_ptr.alloc_id].runs[run_ptr.run_and_offset.0].bytes
            [run_ptr.bytes_range()]
    }

    pub fn bytes_mut(&mut self, run_ptr: RunPointer) -> &mut [AbstractByte<Provenance>] {
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
            Ty::Array(ref ty, len) => {
                return Self::ty_size(ty).map(|elem| Size::from_bytes(elem.bytes_usize() * len))
            }
            _ => return None,
        })
    }

    // Reborrow
    // fn sb_reborrow(
    //     &mut self,
    //     alloc_id: AllocId,
    //     run_and_offset: RunAndOffset,
    //     size: Size,
    //     new_perm: NewPermission,
    //     new_tag: BorTag,
    // ) -> SBResult {
    //     if size == Size::ZERO {
    //         trace!(
    //             "reborrow of size 0: reference {:?} derived from {:?} (pointee {})",
    //             new_tag,
    //             place.ptr,
    //             place.layout.ty,
    //         );
    //         return Ok(());
    //     }

    //     let (alloc_id, base_offset, orig_tag) = this.ptr_get_alloc_id(place.ptr)?;

    //     // Ensure we bail out if the pointer goes out-of-bounds (see miri#1050).
    //     let run_size = self.allocations[alloc_id].run(run_and_offset).len();
    //     if run_and_offset.1 + size > run_size {
    //         return Err(SBViolation);
    //     }

    //     trace!(
    //         "reborrow: reference {:?} derived from {:?} (pointee {}): {:?}, size {}",
    //         new_tag,
    //         orig_tag,
    //         place.layout.ty,
    //         Pointer::new(alloc_id, base_offset),
    //         size.bytes()
    //     );

    //     if let Some(protect) = new_perm.protector() {
    //         // See comment in `Stack::item_invalidated` for why we store the tag twice.
    //         this.frame_mut()
    //             .extra
    //             .borrow_tracker
    //             .as_mut()
    //             .unwrap()
    //             .protected_tags
    //             .push(new_tag);
    //         this.machine
    //             .borrow_tracker
    //             .as_mut()
    //             .unwrap()
    //             .get_mut()
    //             .protected_tags
    //             .insert(new_tag, protect);
    //     }

    //     // Update the stacks, according to the new permission information we are given.
    //     match new_perm {
    //         NewPermission::Uniform {
    //             perm,
    //             access,
    //             protected
    //         } => {
    //             assert!(perm != Permission::SharedReadOnly);
    //             // Here we can avoid `borrow()` calls because we have mutable references.
    //             // Note that this asserts that the allocation is mutable -- but since we are creating a
    //             // mutable pointer, that seems reasonable.
    //             let allocation = self.allocations[alloc_id];
    //             stacked_borrows.for_each(range, |stack, dcx, exposed_tags| {
    //                 stack.grant(orig_tag, item, access, &global, exposed_tags)
    //             })?;
    //             drop(global);
    //             if let Some(access) = access {
    //                 assert_eq!(access, AccessKind::Write);
    //                 // Make sure the data race model also knows about this.
    //                 if let Some(data_race) = alloc_extra.data_race.as_mut() {
    //                     data_race.write(alloc_id, range, machine)?;
    //                 }
    //             }
    //         }
    //         NewPermission::FreezeSensitive {
    //             freeze_perm,
    //             freeze_access,
    //             freeze_protected,
    //             nonfreeze_perm,
    //             nonfreeze_access,
    //         } => {
    //             // The permission is not uniform across the entire range!
    //             // We need a frozen-sensitive reborrow.
    //             // We have to use shared references to alloc/memory_extra here since
    //             // `visit_freeze_sensitive` needs to access the global state.
    //             let alloc_extra = this.get_alloc_extra(alloc_id)?;
    //             let mut stacked_borrows = alloc_extra.borrow_tracker_sb().borrow_mut();
    //             this.visit_freeze_sensitive(place, size, |mut range, frozen| {
    //                 // Adjust range.
    //                 range.start += base_offset;
    //                 // We are only ever `SharedReadOnly` inside the frozen bits.
    //                 let (perm, access, protector) = if frozen {
    //                     (freeze_perm, freeze_access, freeze_protector)
    //                 } else {
    //                     (nonfreeze_perm, nonfreeze_access, None)
    //                 };
    //                 let item = Item::new(new_tag, perm, protector.is_some());
    //                 let global = this.machine.borrow_tracker.as_ref().unwrap().borrow();
    //                 stacked_borrows.for_each(range, |stack, dcx, exposed_tags| {
    //                     stack.grant(orig_tag, item, access, &global, dcx, exposed_tags)
    //                 })?;
    //                 drop(global);
    //                 if let Some(access) = access {
    //                     assert_eq!(access, AccessKind::Read);
    //                 }
    //                 Ok(())
    //             })?;
    //         }
    //     }

    //     Ok(Some(alloc_id))
    // }
}
