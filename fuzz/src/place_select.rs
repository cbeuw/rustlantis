use mir::{
    syntax::{Place, TyId},
    tyctxt::TyCtxt,
};
use rand_distr::WeightedIndex;

use crate::ptable::{PlaceIndex, PlacePath, PlaceTable, ToPlaceIndex};

#[derive(Clone, Copy, Default, PartialEq, Eq)]
enum PlaceUsage {
    #[default]
    Operand,
    LHS,
    Pointee,
    Argument,
    KnownVal,
    Offsetee,
}

#[derive(Clone, Default)]
pub struct PlaceSelector {
    tys: Vec<TyId>,
    exclusions: Vec<Place>,
    allow_uninit: bool,
    usage: PlaceUsage,
}

pub type Weight = usize;

const RET_LHS_WEIGH_FACTOR: Weight = 2;
const UNINIT_WEIGHT_FACTOR: Weight = 2;
const DEREF_WEIGHT_FACTOR: Weight = 2;
const LIT_ARG_WEIGHT_FACTOR: Weight = 2;
const PTR_ARG_WEIGHT_FACTOR: Weight = 2;
const OFFSETTED_PTR_WEIGHT_FACTOR: Weight = 10;
const ROUNDTRIPPED_PTR_WEIGHT_FACTOR: Weight = 100;

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

    pub fn for_argument() -> Self {
        Self {
            usage: PlaceUsage::Argument,
            ..Default::default()
        }
    }

    pub fn for_lhs() -> Self {
        Self {
            usage: PlaceUsage::LHS,
            allow_uninit: true,
            ..Self::default()
        }
    }

    pub fn for_known_val() -> Self {
        Self {
            usage: PlaceUsage::KnownVal,
            ..Self::default()
        }
    }

    pub fn for_offsetee() -> Self {
        Self {
            usage: PlaceUsage::Offsetee,
            ..Self::default()
        }
    }

    pub fn of_ty(self, ty: TyId) -> Self {
        let mut tys = self.tys;
        tys.push(ty);
        Self { tys, ..self }
    }

    pub fn of_tys(self, types: &[TyId]) -> Self {
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
            .chain(pt.return_dest_stack())
            .collect();
        pt.reachable_nodes().filter(move |ppath| {
            let index = ppath.target_index(pt);

            let live = pt.is_place_live(index);

            let ty_allowed = if self.tys.is_empty() {
                true
            } else {
                self.tys.contains(&pt.ty(index))
            };

            let not_excluded = !exclusion_indicies
                .iter()
                .any(|excl| pt.overlap(index, excl));
            let initness_allowed = if self.allow_uninit {
                true
            } else {
                pt.is_place_init(index)
            };

            let literalness = if self.usage == PlaceUsage::KnownVal {
                pt.known_val(index).is_some()
            } else {
                true
            };

            let not_ret_ptr = if self.usage == PlaceUsage::Pointee {
                !pt.overlap(index, Place::RETURN_SLOT)
            } else {
                true
            };

            // FIXME: are we allowed to use moved-from places?
            live && ty_allowed && not_excluded && initness_allowed && literalness && not_ret_ptr
        })
    }

    pub fn into_weighted(
        self,
        pt: &PlaceTable,
        tcx: &TyCtxt,
    ) -> Option<(Vec<PlacePath>, WeightedIndex<Weight>)> {
        let usage = self.usage;
        let (places, weights): (Vec<PlacePath>, Vec<Weight>) =
            self.into_iter_path(pt)
                .map(|ppath| {
                    let place = ppath.target_index(pt);
                    let mut weight = match usage {
                        PlaceUsage::Argument => {
                            // let mut weight = pt.get_dataflow(place);
                            let node = ppath.target_node(pt);
                            let index = ppath.target_index(pt);
                            let mut weight = 1;
                            if node.ty.contains(tcx, |tcx, ty| ty.is_any_ptr(tcx)) {
                                weight *= PTR_ARG_WEIGHT_FACTOR;
                            }
                            if pt.known_val(index).is_some() {
                                weight *= LIT_ARG_WEIGHT_FACTOR;
                            }
                            // Encourage isize for pointer offset
                            if node.ty.contains(tcx, |_, ty| ty == TyCtxt::ISIZE) {
                                weight *= LIT_ARG_WEIGHT_FACTOR;
                            }
                            if node.ty.is_any_ptr(tcx) && pt.offseted(index) {
                                weight *= OFFSETTED_PTR_WEIGHT_FACTOR;
                            }
                            weight
                        }
                        PlaceUsage::LHS => {
                            let mut weight = if !pt.is_place_init(place) {
                                UNINIT_WEIGHT_FACTOR
                            } else {
                                1
                            };
                            if ppath.is_return_proj(pt) {
                                weight *= RET_LHS_WEIGH_FACTOR;
                            }
                            let target = ppath.target_index(pt);
                            if pt.ty(target).is_any_ptr(tcx) && pt.get_offset(target).is_some() {
                                weight = 0;
                            }
                            weight
                        }
                        PlaceUsage::Operand => pt.get_dataflow(place),
                        PlaceUsage::Pointee => 1,
                        PlaceUsage::KnownVal => pt.get_dataflow(place),
                        PlaceUsage::Offsetee => 1,
                    };

                    if ppath.projections(pt).any(|proj| proj.is_deref()) {
                        weight *= DEREF_WEIGHT_FACTOR;
                    }

                    if ppath.nodes(pt).any(|place| {
                        pt.ty(place).is_any_ptr(tcx) && pt.has_offset_roundtripped(place)
                    }) {
                        weight *= ROUNDTRIPPED_PTR_WEIGHT_FACTOR;
                    }

                    (ppath, weight)
                })
                .unzip();
        if let Ok(weighted_index) = WeightedIndex::new(weights) {
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
    use std::rc::Rc;

    use mir::syntax::{Local, Place};
    use rand::{
        rngs::SmallRng,
        seq::{IteratorRandom, SliceRandom},
        Rng, SeedableRng,
    };
    use test::Bencher;

    use crate::{
        ptable::PlaceTable,
        ty::{seed_tys, TySelect},
    };

    use super::PlaceSelector;

    fn build_pt(rng: &mut impl Rng) -> PlaceTable {
        let tcx = Rc::new(seed_tys(rng));
        let mut pt = PlaceTable::new(tcx.clone());
        let ty_weights = TySelect::new(&tcx);
        for i in 0..=32 {
            let pidx = pt.allocate_local(Local::new(i), ty_weights.choose_ty(rng, &tcx));
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
