use core::slice;
use std::{collections::BTreeMap, fmt::Write};

use log::{debug, log_enabled};
use mir::{
    serialize::Serialize,
    syntax::{Mutability, Ty, TyId},
    vec::{Idx, IndexVec},
};
use rand::{seq::IteratorRandom, Rng};
use rand_distr::{Distribution, Exp, Poisson, WeightedIndex};

pub struct TyCtxt {
    tys: IndexVec<TyId, Ty>,
    weights: WeightedIndex<f32>,
}

impl TyCtxt {
    pub fn new(rng: &mut impl Rng) -> Self {
        let tys = Self::seed_tys(rng);
        let weights = Self::distribute_weights(&tys);
        Self { tys, weights }
    }

    fn distribute_weights(tys: &IndexVec<TyId, Ty>) -> WeightedIndex<f32> {
        let p_bool = 0.1;
        let p_char = 0.1;
        let p_floats = 0.1;
        let p_ints = 0.2;
        let p_checked_binop_tuples = 0.2;

        let checked_binary_op_lhs_count = tys
            .iter()
            .filter(|ty| ty.is_checked_binary_op_lhs())
            .count();

        // Types with special treatment as we want to increase their weighting
        let mut weights: BTreeMap<TyId, f32> = BTreeMap::new();
        let mut p_sum: f32 = weights.values().sum();

        // All the types without special weighting
        let mut residual: Vec<TyId> = Vec::new();

        for (idx, ty) in tys.iter_enumerated() {
            let p = match ty {
                Ty::Unit => Some(0.),
                Ty::Bool => Some(p_bool),
                Ty::Char => Some(p_char),
                Ty::Int(..) => Some(p_ints / Ty::INTS.len() as f32),
                Ty::Uint(..) => Some(p_ints / Ty::INTS.len() as f32),
                Ty::Float(..) => Some(p_floats / Ty::FLOATS.len() as f32),
                tup @ Ty::Tuple(..) if tup.is_checked_binary_op_lhs() => {
                    Some(p_checked_binop_tuples / checked_binary_op_lhs_count as f32)
                }
                _ => None,
            };
            if let Some(rate) = p {
                weights.insert(idx, rate);
                p_sum += rate;
            } else {
                residual.push(idx);
            }
        }
        assert!(p_sum < 1.);

        weights.extend(
            residual
                .iter()
                .map(|&tyid| (tyid, (1. - p_sum) / residual.len() as f32)),
        );

        if log_enabled!(log::Level::Debug) {
            let mut s = String::new();
            for (tyid, ty) in tys.iter_enumerated() {
                s.write_fmt(format_args!("{}: {}\n", ty.serialize(), weights[&tyid]))
                    .unwrap();
            }
            debug!("Typing context with weights:\n{s}");
        }

        WeightedIndex::new(weights.values()).expect("can produce weighted index")
    }

    fn seed_tys(rng: &mut impl Rng) -> IndexVec<TyId, Ty> {
        // Seed with primitives
        let mut tys: IndexVec<TyId, Ty> = IndexVec::new();
        let primitives = [
            Ty::Bool,
            Ty::Char,
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

        for ty in Vec::from_iter(Ty::INTS.into_iter().chain(Ty::UINTS).chain(Ty::FLOATS)) {
            tys.push(Ty::Tuple(vec![ty, Ty::Bool]));
        }

        // Generate composite types
        let count = rng.gen_range(0..=16);
        for _ in 0..count {
            let new_ty = match rng.gen_range(0..=0) {
                0 => Ty::Tuple({
                    let dist = Poisson::<f32>::new(2.7).unwrap();
                    let length = dist.sample(rng).clamp(1., 16.) as usize;
                    (0..length)
                        .map(|_| tys.iter().choose(rng).unwrap().clone())
                        .collect()
                }),
                // 1 => Ty::RawPtr(
                //     Box::new(self.choose_ty(rng)),
                //     if rng.gen_bool(0.5) {
                //         Mutability::Mut
                //     } else {
                //         Mutability::Not
                //     },
                // ),
                // 2 => Ty::Adt(todo!()),
                _ => unreachable!(),
            };
            if !tys.iter().any(|ty| *ty == new_ty) {
                tys.push(new_ty);
            }
        }
        tys
    }

    pub fn choose_ty(&self, rng: &mut impl Rng) -> Ty {
        self.tys
            .iter()
            .nth(self.weights.sample(rng))
            .expect("tyctxt isn't empty")
            .clone()
    }

    pub fn iter(&self) -> slice::Iter<'_, Ty> {
        self.tys.iter()
    }

    pub fn is_copy(&self, ty: &Ty) -> bool {
        // TODO: implement this
        true
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
