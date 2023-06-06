use std::slice;

use index_vec::IndexVec;

use crate::syntax::{Ty, TyId};

pub struct TyCtxt {
    tys: IndexVec<TyId, Ty>,
}

impl TyCtxt {
    pub fn from_index_vec(tys: IndexVec<TyId, Ty>) -> Self {
        Self { tys }
    }

    pub fn iter(&self) -> slice::Iter<'_, Ty> {
        self.tys.iter()
    }

    pub fn iter_enumerated(&self) -> impl Iterator<Item = (TyId, &Ty)> {
        self.tys.iter_enumerated()
    }

    pub fn is_copy(&self, ty: &Ty) -> bool {
        // TODO: implement this
        true
    }

    pub fn len(&self) -> usize {
        self.tys.len()
    }
}
