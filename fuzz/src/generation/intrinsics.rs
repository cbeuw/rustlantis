use std::borrow::BorrowMut;

use mir::{
    syntax::{Callee, Mutability, Operand, Place, TyKind},
    tyctxt::TyCtxt,
};
use rand::{seq::IteratorRandom, Rng};

use crate::{literal::GenLiteral, place_select::PlaceSelector};

use super::{GenerationCtx, Result, SelectionError};

pub trait CoreIntrinsic {
    fn name(&self) -> &'static str;

    fn dest_type(&self, ty: &TyKind) -> bool;

    fn choose_operands(&self, ctx: &GenerationCtx, dest: &Place) -> Option<Vec<Operand>>;

    fn generate_terminator(
        &self,
        ctx: &GenerationCtx,
        dest: &Place,
    ) -> Result<(Callee, Vec<Operand>)> {
        if !self.dest_type(dest.ty(ctx.current_decls(), &ctx.tcx).kind(&ctx.tcx)) {
            return Err(SelectionError::Exhausted);
        }
        let args = self
            .choose_operands(ctx, dest)
            .ok_or(SelectionError::Exhausted)?;
        Ok((Callee::Intrinsic(self.name()), args))
    }
}

struct Fmaf64;
impl CoreIntrinsic for Fmaf64 {
    fn name(&self) -> &'static str {
        "fmaf64"
    }

    fn dest_type(&self, ty: &TyKind) -> bool {
        ty == &TyKind::F64
    }

    fn choose_operands(&self, ctx: &GenerationCtx, dest: &Place) -> Option<Vec<Operand>> {
        let a = ctx.choose_operand(&[TyCtxt::F64], dest).ok()?;
        let b = ctx.choose_operand(&[TyCtxt::F64], dest).ok()?;
        let c = ctx.choose_operand(&[TyCtxt::F64], dest).ok()?;
        Some(vec![a, b, c])
    }
}

pub(super) struct ArithOffset;
impl CoreIntrinsic for ArithOffset {
    fn name(&self) -> &'static str {
        "arith_offset"
    }

    fn dest_type(&self, ty: &TyKind) -> bool {
        matches!(ty, TyKind::RawPtr(.., Mutability::Not))
    }

    fn choose_operands(&self, ctx: &GenerationCtx, dest: &Place) -> Option<Vec<Operand>> {
        let (ptrs, weights) = PlaceSelector::for_offsetee(ctx.tcx.clone())
            .of_ty(dest.ty(ctx.current_decls(), &ctx.tcx))
            .except(dest)
            .into_weighted(&ctx.pt)?;
        let ptr = ctx
            .make_choice_weighted(ptrs.into_iter(), weights, |ppath| {
                Ok(ppath.to_place(&ctx.pt))
            })
            .ok()?;

        let offset = ctx.pt.get_offset(&ptr);

        let mut rng = ctx.rng.borrow_mut();
        let new_offset = match offset {
            // Don't break roundtripped pointer
            Some(0) => {
                return None;
            }
            Some(existing) if existing.checked_neg().is_some() && rng.gen_bool(0.5) => {
                Operand::Constant((-existing).try_into().unwrap())
            }
            _ => PlaceSelector::for_known_val(ctx.tcx.clone())
                .of_ty(TyCtxt::ISIZE)
                .into_iter_place(&ctx.pt)
                .choose(&mut *rng)
                .map(Operand::Copy)
                .unwrap_or_else(|| {
                    Operand::Constant(
                        rng.borrow_mut()
                            .gen_literal(TyCtxt::ISIZE, &ctx.tcx)
                            .expect("can generate a literal"),
                    )
                }),
        };

        Some(vec![Operand::Copy(ptr), new_offset])
    }
}

struct Bswap;
impl CoreIntrinsic for Bswap {
    fn name(&self) -> &'static str {
        "bswap"
    }

    fn dest_type(&self, ty: &TyKind) -> bool {
        matches!(ty, TyKind::Int(..) | TyKind::Uint(..))
    }

    fn choose_operands(&self, ctx: &GenerationCtx, dest: &Place) -> Option<Vec<Operand>> {
        let arg = ctx
            .choose_operand(&[dest.ty(ctx.current_decls(), &ctx.tcx)], dest)
            .ok()?;
        Some(vec![arg])
    }
}

impl GenerationCtx {
    pub fn choose_intrinsic(&self, dest: &Place) -> Result<(Callee, Vec<Operand>)> {
        let choices: [Box<dyn CoreIntrinsic>; 3] =
            [Box::new(Fmaf64), Box::new(ArithOffset), Box::new(Bswap)];

        let intrinsic = self.make_choice(choices.iter(), Result::Ok)?;
        intrinsic.generate_terminator(self, dest)
    }
}
