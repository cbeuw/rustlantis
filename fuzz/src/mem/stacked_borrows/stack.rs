use super::item::Item;

/// Extra per-location state.
#[derive(Clone, Debug)]
pub struct Stack {
    /// Used *mostly* as a stack; never empty.
    /// Invariants:
    /// * Above a `SharedReadOnly` there can only be more `SharedReadOnly`.
    /// * Except for `Untagged`, no tag occurs in the stack more than once.
    borrows: Vec<Item>,
}
impl Stack {
    /// Construct a new `Stack` using the passed `Item` as the base tag.
    pub fn new(item: Item) -> Self {
        Stack {
            borrows: vec![item],
        }
    }
}
