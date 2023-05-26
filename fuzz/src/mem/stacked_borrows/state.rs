use std::collections::HashMap;

use log::trace;

use crate::mem::AllocId;

use super::BorTag;

pub struct GlobalState {
    /// Next unused pointer ID (tag).
    pub next_ptr_tag: BorTag,
    /// Table storing the "base" tag for each allocation.
    /// The base tag is the one used for the initial pointer.
    /// We need this in a separate table to handle cyclic statics.
    pub base_ptr_tags: HashMap<AllocId, BorTag>,
}

impl GlobalState {
    pub fn new() -> Self {
        GlobalState {
            next_ptr_tag: BorTag::one(),
            base_ptr_tags: HashMap::default(),
        }
    }

    /// Generates a new pointer tag. Remember to also check track_pointer_tags and log its creation!
    pub fn new_ptr(&mut self) -> BorTag {
        let id = self.next_ptr_tag;
        self.next_ptr_tag = id.succ().unwrap();
        id
    }
    pub fn base_ptr_tag(&mut self, id: AllocId) -> BorTag {
        self.base_ptr_tags.get(&id).copied().unwrap_or_else(|| {
            let tag = self.new_ptr();
            trace!("New allocation {:?} has base tag {:?}", id, tag);
            let exists = self.base_ptr_tags.insert(id, tag);
            assert!(exists.is_none());
            tag
        })
    }
}
