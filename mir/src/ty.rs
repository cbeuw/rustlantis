use crate::{vec::IndexVec, syntax::{Ty, TyKind, IntTy, UintTy, FloatTy}};

pub struct TyCtxt {
    tys: IndexVec<Ty, TyKind>,
}

impl TyCtxt {
    pub fn new() -> Self {
        // Important: the order here must match the const definitions in Ty
        let tys = IndexVec::from_iter([
            TyKind::Bool,
            TyKind::Char,
            TyKind::Int(IntTy::Isize),
            TyKind::Int(IntTy::I8),
            TyKind::Int(IntTy::I16),
            TyKind::Int(IntTy::I32),
            TyKind::Int(IntTy::I64),
            TyKind::Int(IntTy::I128),
            TyKind::Uint(UintTy::Usize),
            TyKind::Uint(UintTy::U8),
            TyKind::Uint(UintTy::U16),
            TyKind::Uint(UintTy::U32),
            TyKind::Uint(UintTy::U64),
            TyKind::Uint(UintTy::U128),
            TyKind::Float(FloatTy::F32),
            TyKind::Float(FloatTy::F64),
        ]);
        Self { tys }
    }

    pub fn declare_new_ty(&mut self, def: TyKind) -> Ty {
        self.tys.push(def)
    }

    pub fn tys(&self) -> impl Iterator<Item = Ty> + ExactSizeIterator {
        self.tys.indices()
    }

    pub fn tykind(&self, ty: Ty) -> &TyKind {
        &self.tys[ty]
    }
}