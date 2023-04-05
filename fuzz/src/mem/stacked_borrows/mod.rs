pub mod item;
pub mod stack;
pub mod state;

use std::{fmt, num::NonZeroU64};

use index_vec::IndexVec;
use rangemap::RangeMap;

use self::{
    item::{Item, Permission},
    stack::Stack,
    state::GlobalState,
};

use super::{AllocId, RunId};

/// Tracking pointer provenance
#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct BorTag(NonZeroU64);

impl BorTag {
    pub fn new(i: u64) -> Option<Self> {
        NonZeroU64::new(i).map(BorTag)
    }

    pub fn get(&self) -> u64 {
        self.0.get()
    }

    pub fn inner(&self) -> NonZeroU64 {
        self.0
    }

    pub fn succ(self) -> Option<Self> {
        self.0.checked_add(1).map(Self)
    }

    /// The minimum representable tag
    pub fn one() -> Self {
        Self::new(1).unwrap()
    }
}

impl std::default::Default for BorTag {
    /// The default to be used when borrow tracking is disabled
    fn default() -> Self {
        Self::one()
    }
}

impl fmt::Debug for BorTag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<{}>", self.0)
    }
}

#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Provenance {
    alloc_id: AllocId,
    /// Borrow Tracker tag.
    tag: BorTag,
}

/// Extra per-allocation state.
#[derive(Clone, Debug)]
pub struct Stacks {
    stacks: IndexVec<RunId, RangeMap<Stack>>,
}

impl Stacks {
    pub fn from_stacks(stacks: IndexVec<RunId, RangeMap<Stack>>) -> Self {
        Self { stacks }
    }
}
