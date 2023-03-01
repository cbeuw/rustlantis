use mir::syntax::{Local, LocalDecl, Mutability, Place, Ty, TyKind};
use rand::{seq::IteratorRandom, Rng};

use crate::generation::GenerationCtx;

pub struct PlaceSelector<'ctx> {
    ctx: &'ctx GenerationCtx,
    candidates: Box<dyn Iterator<Item = Local> + 'ctx>,
}

impl<'ctx> PlaceSelector<'ctx> {
    pub fn locals_and_args(ctx: &'ctx GenerationCtx) -> Self {
        Self {
            ctx,
            candidates: Box::new(ctx.current_fn().vars_and_args_iter()),
        }
    }
    pub fn locals(ctx: &'ctx GenerationCtx) -> Self {
        Self {
            ctx,
            candidates: Box::new(ctx.current_fn().vars_iter()),
        }
    }

    pub fn mutable(self) -> Self {
        let candidates = Box::new(self.candidates.filter(|&local| {
            self.ctx.current_decls()[local].mutability == Mutability::Mut
        }));
        Self { candidates, ..self }
    }

    pub fn of_ty(self, ty: Ty) -> Self {
        let candidates = Box::new(
            self.candidates
                .filter(move |&local| self.ctx.current_decls()[local].ty == ty),
        );
        Self { candidates, ..self }
    }

    pub fn of_tys(self, tys: &'ctx [Ty]) -> Self {
        let candidates = Box::new(
            self.candidates
                .filter(|&local| tys.contains(&self.ctx.current_decls()[local].ty)),
        );
        Self { candidates, ..self }
    }

    pub fn filter_by_ty<F>(self, predicate: F) -> Self
    where
        F: Fn(Ty) -> bool + 'ctx,
    {
        let candidates = Box::new(
            self.candidates.filter(move |&local| predicate(self.ctx.current_decls()[local].ty)));
        Self { candidates, ..self}
    }

    pub fn except(self, exclude: &'ctx Place) -> Self {
        // TODO: More granular place discrimination
        let candidates = Box::new(self.candidates.filter(|&local| local != exclude.local));
        Self { candidates, ..self }
    }

    pub fn select<R: Rng>(self, rng: &mut R) -> Option<Place> {
        self.candidates
            .choose(rng)
            .map(|local| Place::from_local(local))
    }
}
