use mir::syntax::{Callee, Mutability, Operand, Place, Ty};

use super::{GenerationCtx, Result, SelectionError};

pub trait CoreIntrinsic {
    fn name(&self) -> &'static str;

    fn dest_type(&self, ty: Ty) -> bool;

    fn choose_operands(&self, ctx: &GenerationCtx, dest: &Place) -> Option<Vec<Operand>>;

    fn generate_terminator(
        &self,
        ctx: &GenerationCtx,
        dest: &Place,
    ) -> Result<(Callee, Vec<Operand>)> {
        if !self.dest_type(dest.ty(ctx.current_decls())) {
            return Err(SelectionError::Exhausted);
        }
        let args = self
            .choose_operands(ctx, &dest)
            .ok_or(SelectionError::Exhausted)?;
        Ok((Callee::Intrinsic(self.name()), args))
    }
}

struct Fmaf64;
impl CoreIntrinsic for Fmaf64 {
    fn name(&self) -> &'static str {
        "fmaf64"
    }

    fn dest_type(&self, ty: Ty) -> bool {
        ty == Ty::F64
    }

    fn choose_operands(&self, ctx: &GenerationCtx, dest: &Place) -> Option<Vec<Operand>> {
        let a = ctx.choose_operand(&[Ty::F64], dest).ok()?;
        let b = ctx.choose_operand(&[Ty::F64], dest).ok()?;
        let c = ctx.choose_operand(&[Ty::F64], dest).ok()?;
        Some(vec![a, b, c])
    }
}

struct ArithOffset;
impl CoreIntrinsic for ArithOffset {
    fn name(&self) -> &'static str {
        "arith_offset"
    }

    fn dest_type(&self, ty: Ty) -> bool {
        matches!(ty, Ty::RawPtr(.., Mutability::Not))
    }

    fn choose_operands(&self, ctx: &GenerationCtx, dest: &Place) -> Option<Vec<Operand>> {
        let ptr = ctx
            .choose_operand(&[dest.ty(ctx.current_decls())], dest)
            .ok()?;
        let offset = ctx.choose_operand(&[Ty::ISIZE], dest).ok()?;

        Some(vec![ptr, offset])
    }
}

struct Bswap;
impl CoreIntrinsic for Bswap {
    fn name(&self) -> &'static str {
        "bswap"
    }

    fn dest_type(&self, ty: Ty) -> bool {
        matches!(ty, Ty::Int(..) | Ty::Uint(..))
    }

    fn choose_operands(&self, ctx: &GenerationCtx, dest: &Place) -> Option<Vec<Operand>> {
        let arg = ctx
            .choose_operand(&[dest.ty(ctx.current_decls())], dest)
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
