use std::{collections::HashMap, fmt::Write};

use index_vec::IndexVec;
use log::{debug, log_enabled};
use mir::{
    serialize::Serialize,
    syntax::{Adt, IntTy, Mutability, TyId, TyKind, VariantDef},
    tyctxt::{AdtMeta, TyCtxt},
};
use rand::{seq::IteratorRandom, Rng};
use rand_distr::{Distribution, Poisson, WeightedIndex};

const TUPLE_MAX_LEN: usize = 12;
pub const ARRAY_MAX_LEN: usize = 8;
const STRUCT_MAX_FIELDS: usize = 8;
const ADT_MAX_VARIANTS: usize = 4;

pub struct TySelect {
    weights: WeightedIndex<f32>,
}

impl TySelect {
    pub fn new(tcx: &TyCtxt) -> Self {
        Self {
            weights: Self::distribute_weights(tcx),
        }
    }
    fn distribute_weights(tcx: &TyCtxt) -> WeightedIndex<f32> {
        let p_bool = 0.05;
        let p_char = 0.05;
        let p_floats = 0.1;
        let p_ints = 0.1;
        let p_isize = 0.1;
        let p_pointers = 0.2;

        // Types with special treatment as we want to increase their weighting
        let mut weights: HashMap<TyId, f32> = HashMap::new();
        let mut p_sum: f32 = 0.;
        let num_ptrs = tcx
            .iter_enumerated()
            .filter(|(ty, _)| ty.contains(tcx, |tcx, ty| ty.is_any_ptr(tcx)))
            .count();

        // All the types without special weighting
        let mut residual: Vec<TyId> = Vec::new();

        for (idx, ty) in tcx.iter_enumerated() {
            let p = match ty {
                TyKind::Unit => Some(0.),
                TyKind::Bool => Some(p_bool),
                TyKind::Char => Some(p_char),
                TyKind::Int(IntTy::Isize) => Some(p_isize),
                TyKind::Int(..) => Some(p_ints / TyKind::INTS.len() as f32),
                TyKind::Uint(..) => Some(p_ints / TyKind::INTS.len() as f32),
                TyKind::Float(..) => Some(p_floats / TyKind::FLOATS.len() as f32),
                _ if idx.contains(tcx, |tcx, ty| ty.is_any_ptr(tcx)) => {
                    Some(p_pointers / num_ptrs as f32)
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
            for (tyid, _) in tcx.iter_enumerated() {
                s.write_fmt(format_args!(
                    "{}: {}\n",
                    tyid.serialize(tcx),
                    weights[&tyid]
                ))
                .unwrap();
            }
            debug!("Typing context with weights:\n{s}");
            debug!("{}", tcx.serialize());
        }

        WeightedIndex::new(tcx.iter_enumerated().map(|(tyid, _)| weights[&tyid]))
            .expect("can produce weighted index")
    }

    pub fn choose_ty(&self, rng: &mut impl Rng, tcx: &TyCtxt) -> TyId {
        tcx.indices()
            .nth(self.weights.sample(rng))
            .expect("tyctxt isn't empty")
    }
}
pub fn seed_tys<R: Rng>(rng: &mut R) -> TyCtxt {
    // Seed with primitives
    let mut tcx: TyCtxt = TyCtxt::from_primitives();

    // Generate composite structural types
    for _ in 0..=32 {
        let new_ty = match rng.gen_range(0..=2) {
            0 => TyKind::Tuple({
                let dist = Poisson::<f32>::new(2.7).unwrap();
                let length = dist.sample(rng).clamp(1., TUPLE_MAX_LEN as f32) as usize;
                (0..length)
                    .map(|_| {
                        tcx.indices()
                            .filter(|ty| *ty != TyCtxt::UNIT)
                            .choose(rng)
                            .unwrap()
                    })
                    .collect()
            }),
            1 => TyKind::RawPtr(
                tcx.indices()
                    .filter(|ty| *ty != TyCtxt::UNIT)
                    .choose(rng)
                    .unwrap(),
                if rng.gen_bool(0.5) {
                    Mutability::Mut
                } else {
                    Mutability::Not
                },
            ),
            2 => TyKind::Array(
                tcx.iter_enumerated()
                    .filter_map(|(ty, kind)| (ty != TyCtxt::UNIT && kind.is_scalar()).then_some(ty))
                    .choose(rng)
                    .unwrap(),
                rng.gen_range(1..=ARRAY_MAX_LEN),
            ),
            _ => unreachable!(),
        };
        if !tcx.iter().any(|ty| *ty == new_ty) {
            tcx.push(new_ty);
        }
    }

    // TODO: recursive types
    for _ in 0..=16 {
        let variant_count = rng.gen_range(1..=ADT_MAX_VARIANTS);

        let variants = (0..variant_count).map(|_| {
            let field_count = rng.gen_range(1..=STRUCT_MAX_FIELDS);
            let field_tys = tcx
                .indices()
                .filter(|ty| *ty != TyCtxt::UNIT)
                .choose_multiple(rng, field_count);
            VariantDef {
                fields: IndexVec::from_iter(field_tys.into_iter()),
            }
        });
        let adt = Adt {
            variants: IndexVec::from_iter(variants),
        };

        let copy = if adt.copy_derivable(&tcx) {
            rng.gen_bool(0.5)
        } else {
            false
        };

        let meta = AdtMeta { copy };

        tcx.push_adt(adt, meta);
    }
    tcx
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use mir::syntax::TyId;
    use rand::SeedableRng;

    use crate::ty::seed_tys;

    #[test]
    fn tys_unique() {
        let mut rng = rand::rngs::SmallRng::seed_from_u64(0);
        let tcx = seed_tys(&mut rng);
        let set: HashSet<TyId> = tcx.indices().collect();
        assert!(set.len() == tcx.len())
    }
}
