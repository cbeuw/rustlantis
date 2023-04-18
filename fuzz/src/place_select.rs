use std::default;

use mir::syntax::{Place, Ty};
use rand_distr::WeightedIndex;

use crate::ptable::{PlaceIndex, PlacePath, PlaceTable, ToPlaceIndex};

#[derive(Clone, Copy, Default)]
enum PlaceUsage {
    #[default]
    Operand,
    LHS,
    Pointee,
}

#[derive(Clone, Default)]
pub struct PlaceSelector {
    tys: Vec<Ty>,
    exclusions: Vec<Place>,
    allow_uninit: bool,
    usage: PlaceUsage,
}

pub type Weight = usize;

const LHS_WEIGH_FACTOR: Weight = 2;
const UNINIT_WEIGHT_FACTOR: Weight = 2;

impl PlaceSelector {
    pub fn for_pointee() -> Self {
        Self {
            usage: PlaceUsage::Pointee,
            allow_uninit: true,
            ..Default::default()
        }
    }

    pub fn for_operand() -> Self {
        Self::default()
    }

    pub fn for_lhs() -> Self {
        Self {
            usage: PlaceUsage::LHS,
            ..Self::default()
        }
    }

    pub fn maybe_uninit(mut self) -> Self {
        self.allow_uninit = true;
        self
    }

    pub fn of_ty(self, ty: Ty) -> Self {
        let mut tys = self.tys;
        tys.push(ty);
        Self { tys, ..self }
    }

    pub fn of_tys(self, types: &[Ty]) -> Self {
        let mut tys = self.tys;
        tys.extend(types.iter().cloned());
        Self { tys, ..self }
    }

    pub fn except(self, exclude: &Place) -> Self {
        let mut exclusions = self.exclusions;
        // TODO: More granular place discrimination
        exclusions.push(exclude.clone());
        Self { exclusions, ..self }
    }

    fn into_iter_path(self, pt: &PlaceTable) -> impl Iterator<Item = PlacePath> + Clone + '_ {
        let exclusion_indicies: Vec<PlaceIndex> = self
            .exclusions
            .iter()
            .map(|place| place.to_place_index(pt).expect("excluded place exists"))
            .collect();
        pt.reachable_nodes().filter(move |ppath| {
            let node = ppath.target_node(pt);
            let ty_allowed = if self.tys.is_empty() {
                true
            } else {
                self.tys.contains(&node.ty)
            };

            let not_excluded = !exclusion_indicies.contains(&ppath.target_index(pt));
            let initness_allowed = if self.allow_uninit {
                true
            } else {
                pt.is_place_init(ppath.target_index(pt))
            };
            ty_allowed && not_excluded && initness_allowed
        })
    }

    pub fn into_weighted(self, pt: &PlaceTable) -> Option<(Vec<Place>, WeightedIndex<Weight>)> {
        let (places, weights) = match self.usage {
            PlaceUsage::LHS => {
                let (places, weights): (Vec<Place>, Vec<Weight>) = self
                    .into_iter_path(pt)
                    .map(|ppath| {
                        let mut weight = if !pt.is_place_init(ppath.target_index(pt)) {
                            UNINIT_WEIGHT_FACTOR
                        } else {
                            1
                        };
                        let place = ppath.to_place(pt);
                        weight *= if place == Place::RETURN_SLOT {
                            LHS_WEIGH_FACTOR
                        } else {
                            1
                        };
                        (place, weight)
                    })
                    .unzip();
                (places, weights)
            }
            PlaceUsage::Operand => {
                let (places, weights): (Vec<Place>, Vec<Weight>) = self
                    .into_iter_path(pt)
                    .map(|ppath| (ppath.to_place(pt), ppath.target_node(pt).dataflow))
                    .unzip();
                (places, weights)
            }
            PlaceUsage::Pointee => {
                let (places, weights): (Vec<Place>, Vec<Weight>) = self
                    .into_iter_path(pt)
                    .map(|ppath| (ppath.to_place(pt), 1))
                    .unzip();
                (places, weights)
            }
        };
        if let Some(weighted_index) = WeightedIndex::new(weights).ok() {
            Some((places, weighted_index))
        } else {
            None
        }
    }

    pub fn into_iter_place(self, pt: &PlaceTable) -> impl Iterator<Item = Place> + Clone + '_ {
        self.into_iter_path(pt).map(|ppath| ppath.to_place(pt))
    }
}

#[cfg(test)]
mod tests {
    extern crate test;
    use mir::syntax::{Local, Place};
    use rand::{
        rngs::SmallRng,
        seq::{IteratorRandom, SliceRandom},
        Rng, SeedableRng,
    };
    use test::Bencher;

    use crate::{ptable::PlaceTable, ty::TyCtxt};

    use super::PlaceSelector;

    fn build_pt(rng: &mut impl Rng) -> PlaceTable {
        let mut pt = PlaceTable::new();
        let tcx = TyCtxt::new(rng);
        for i in 0..=32 {
            let pidx = pt.allocate_local(Local::new(i), tcx.choose_ty(rng));
            if i % 2 == 0 {
                pt.mark_place_init(pidx);
            }
        }
        pt
    }

    #[bench]
    fn bench_select(b: &mut Bencher) {
        let mut rng = SmallRng::seed_from_u64(0);
        let pt = build_pt(&mut rng);

        b.iter(|| {
            PlaceSelector::for_lhs()
                .except(&Place::RETURN_SLOT)
                .into_iter_place(&pt)
                .choose(&mut rng)
                .expect("places not empty");
        })
    }

    #[bench]
    fn bench_materialise_into_vec(b: &mut Bencher) {
        let mut rng = SmallRng::seed_from_u64(0);
        let pt = build_pt(&mut rng);

        b.iter(|| {
            let places: Vec<Place> = PlaceSelector::for_lhs()
                .except(&Place::RETURN_SLOT)
                .into_iter_place(&pt)
                .collect();

            // places.choose(&mut rng).expect("not empty");
            places
                .choose_weighted(&mut rng, |p| p.projection().len())
                .expect("places not empty");
        })
    }
}
