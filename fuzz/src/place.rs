use mir::syntax::{Local, LocalDecl, Mutability, Place, Ty};
use rand::{seq::IteratorRandom, Rng};

use crate::generation::GenerationCtx;

pub struct PlaceSelector<'ctx> {
    ctx: &'ctx GenerationCtx,
    candidates: Box<dyn Iterator<Item = (Local, &'ctx LocalDecl)>>,
}

impl<'ctx> PlaceSelector<'ctx> {
    pub fn locals_and_args(ctx: &'ctx GenerationCtx) -> Self {
        Self {
            ctx,
            candidates: Box::new(ctx.current_body.vars_and_args_decl_iter()),
        }
    }
    pub fn locals(ctx: &'ctx GenerationCtx) -> Self {
        Self {
            ctx,
            candidates: Box::new(ctx.current_body.vars_decl_iter()),
        }
    }

    pub fn mutable(self) -> Self {
        self.candidates = Box::new(
            self.candidates
                .filter(|(local, decl)| decl.mutability == Mutability::Mut),
        );
        self
    }

    pub fn of_ty(self, ty: Ty) -> Self {
        self.candidates = Box::new(self.candidates.filter(|(local, decl)| decl.ty == ty));
        self
    }

    pub fn except(self, exclude: Local) -> Self {
        self.candidates = Box::new(self.candidates.filter(|(local, _)| *local != exclude));
        self

    }

    pub fn select<R: Rng>(&self, rng: &mut R) -> Option<Place> {
        self.candidates
            .choose(rng)
            .map(|(local, _)| Place { local })
    }
}
