use mir::syntax::{Place, Ty};

use crate::ptable::{PlaceIndex, PlaceTable};

#[derive(Clone, Default)]
pub struct PlaceSelector {
    tys: Vec<Ty>,
    exclusions: Vec<Place>,
    allow_uninit: bool,
}

impl PlaceSelector {
    pub fn new() -> Self {
        Self::default()
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

    pub fn into_iter(self, pt: &PlaceTable) -> impl Iterator<Item = Place> + Clone + '_ {
        let exclusion_indicies: Vec<PlaceIndex> = self
            .exclusions
            .iter()
            .map(|place| pt.get_node(place).expect("excluded place exists"))
            .collect();
        pt.reachable_nodes().filter_map(move |ppath| {
            let node = ppath.target_node(pt);
            let ty_allowed = if self.tys.is_empty() {
                true
            } else {
                self.tys.contains(&node.ty)
            };

            let not_excluded = !exclusion_indicies.contains(&ppath.target_index(pt));
            let initness_allowed = if self.allow_uninit { true } else { node.init };
            if ty_allowed && not_excluded && initness_allowed {
                Some(ppath.to_place(pt))
            } else {
                None
            }
        })
    }
}
