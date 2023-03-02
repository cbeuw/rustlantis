use crate::{vec::IndexVec, syntax::{Ty, IntTy, UintTy, FloatTy, UDTy}};

pub struct TyCtxt {
    // Named (user-defined types)
    tys: IndexVec<UDTy, Ty>,
}

impl TyCtxt {
    pub fn new() -> Self {
        Self { tys: IndexVec::new() }
    }

    pub fn declare_new_ty(&mut self, def: Ty) -> UDTy {
        self.tys.push(def)
    }

    // pub fn tys(&self) -> impl Iterator<Item = Ty> + ExactSizeIterator {
    //     self.tys.
    // }
}