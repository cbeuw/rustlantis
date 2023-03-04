use core::slice;

use mir::{
    syntax::{Mutability, Ty, TyId},
    vec::IndexVec,
};
use rand::{seq::IteratorRandom, Rng};

pub struct TyCtxt {
    // Named (user-defined types)
    tys: IndexVec<TyId, Ty>,
}

impl TyCtxt {
    pub fn new(rng: &mut impl Rng) -> Self {
        // Seed with primitives
        let mut tys: IndexVec<TyId, Ty> = IndexVec::new();
        let primitives = [
            Ty::ISIZE,
            Ty::I8,
            Ty::I16,
            Ty::I32,
            Ty::I64,
            Ty::I128,
            Ty::USIZE,
            Ty::U8,
            Ty::U16,
            Ty::U32,
            Ty::U64,
            Ty::U128,
            Ty::F32,
            Ty::F64,
        ];
        primitives.iter().for_each(|ty| {
            tys.push(ty.clone());
        });
        let mut tcx = Self { tys };

        tcx.populate_tys(rng);

        tcx
    }

    pub fn choose_ty(&self, rng: &mut impl Rng) -> Ty {
        self.tys
            .iter()
            .choose(rng)
            .expect("tyctxt isn't empty")
            .clone()
    }

    fn populate_tys(&mut self, rng: &mut impl Rng) {
        // Generate composite types
        let count = rng.gen_range(0..=128);
        for _ in 0..count {
            let new_ty = match rng.gen_range(0..=1) {
                0 => Ty::RawPtr(
                    Box::new(self.choose_ty(rng)),
                    if rng.gen_bool(0.5) {
                        Mutability::Mut
                    } else {
                        Mutability::Not
                    },
                ),
                1 => Ty::Tuple({
                    let tuple_count = rng.gen_range(1..=16);
                    (0..tuple_count).map(|_| self.choose_ty(rng)).collect()
                }),
                2 => Ty::Adt(todo!()),
                _ => unreachable!(),
            };
            if !self.tys.iter().any(|ty| ty.clone() == new_ty) {
                self.tys.push(new_ty);
            }
        }
    }

    pub fn iter(&self) -> slice::Iter<'_, Ty> {
        self.tys.iter()
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use mir::syntax::Ty;
    use rand::SeedableRng;

    use super::TyCtxt;

    #[test]
    fn tys_unique() {
        let mut rng = rand::rngs::SmallRng::seed_from_u64(0);
        let tcx = TyCtxt::new(&mut rng);
        let set: HashSet<Ty> = tcx.iter().cloned().collect();
        assert!(set.len() == tcx.tys.len())
    }
}
