use std::{collections::HashMap, slice};

use index_vec::IndexVec;

use crate::syntax::{TyId, TyKind};

pub struct TyCtxt {
    tys: IndexVec<TyId, TyKind>,
    structural_kinds: HashMap<TyKind, TyId>,
}

impl TyCtxt {
    pub const UNIT: TyId = TyId::from_usize_unchecked(0);
    pub const BOOL: TyId = TyId::from_usize_unchecked(1);
    pub const CHAR: TyId = TyId::from_usize_unchecked(2);
    pub const ISIZE: TyId = TyId::from_usize_unchecked(3);
    pub const I8: TyId = TyId::from_usize_unchecked(4);
    pub const I16: TyId = TyId::from_usize_unchecked(5);
    pub const I32: TyId = TyId::from_usize_unchecked(6);
    pub const I64: TyId = TyId::from_usize_unchecked(7);
    pub const I128: TyId = TyId::from_usize_unchecked(8);
    pub const USIZE: TyId = TyId::from_usize_unchecked(9);
    pub const U8: TyId = TyId::from_usize_unchecked(10);
    pub const U16: TyId = TyId::from_usize_unchecked(11);
    pub const U32: TyId = TyId::from_usize_unchecked(12);
    pub const U64: TyId = TyId::from_usize_unchecked(13);
    pub const U128: TyId = TyId::from_usize_unchecked(14);
    pub const F32: TyId = TyId::from_usize_unchecked(15);
    pub const F64: TyId = TyId::from_usize_unchecked(16);

    pub fn from_primitives() -> Self {
        let primitives: [TyKind; 17] = [
            TyKind::Unit,
            TyKind::Bool,
            TyKind::Char,
            TyKind::ISIZE,
            TyKind::I8,
            TyKind::I16,
            TyKind::I32,
            TyKind::I64,
            TyKind::I128,
            TyKind::USIZE,
            TyKind::U8,
            TyKind::U16,
            TyKind::U32,
            TyKind::U64,
            TyKind::U128,
            TyKind::F32,
            TyKind::F64,
        ];
        let tys = IndexVec::from_iter(primitives);
        let kinds = HashMap::from_iter(tys.iter_enumerated().map(|(ty, kind)| (kind.clone(), ty)));
        Self {
            tys,
            structural_kinds: kinds,
        }
    }

    // FIXME: validate field types
    pub fn push(&mut self, kind: TyKind) -> TyId {
        // Structrual types are unique
        if kind.is_structural() {
            *self
                .structural_kinds
                .entry(kind.clone())
                .or_insert_with(|| self.tys.push(kind))
        } else {
            self.tys.push(kind)
        }
    }

    pub fn kind(&self, ty: TyId) -> &TyKind {
        &self.tys[ty]
    }

    pub fn ty(&self, kind: &TyKind) -> TyId {
        assert!(kind.is_structural());
        self.structural_kinds[kind]
    }

    pub fn indicies(&self) -> impl Iterator<Item = TyId> {
        self.tys.indices()
    }

    pub fn iter(&self) -> slice::Iter<'_, TyKind> {
        self.tys.iter()
    }

    pub fn iter_enumerated(&self) -> impl Iterator<Item = (TyId, &TyKind)> {
        self.tys.iter_enumerated()
    }

    pub fn len(&self) -> usize {
        self.tys.len()
    }
}
