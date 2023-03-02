use std::{borrow::BorrowMut, cell::RefCell, mem::variant_count};

use mir::syntax::{
    BasicBlock, BasicBlockData, BinOp, Body, FloatTy, Function, IntTy, Local, LocalDecls,
    Mutability, Operand, Place, Program, Rvalue, Statement, Ty, TyKind, UintTy, UnOp, Literal,
};
use rand::{
    seq::{IteratorRandom, SliceRandom},
    Rng, RngCore,
};

use crate::place::PlaceSelector;

#[derive(Debug)]
enum SelectionError {
    Exhausted,
    NoPossibleOp,
}

type Result<Node> = std::result::Result<Node, SelectionError>;

pub struct GenerationCtx {
    rng: RefCell<Box<dyn RngCore>>,
    program: Program,
    current_function: Function,
    current_bb: BasicBlock,
}

trait GenerateOperand {
    fn choose_operand(&self, cur_stmt: &mut Statement) -> Result<()>;
}

impl GenerateOperand for GenerationCtx {
    fn choose_operand(&self, cur_stmt: &mut Statement) -> Result<()> {
        let (lhs, rvalue) = match cur_stmt {
            Statement::Assign(lhs, rvalue) => (lhs, rvalue),
            _ => unreachable!("Operand does not appear in non-assign statements"),
        };

        let tcx = &self.program.tcx;
        let local_decls = self.current_decls();
        let mut rng = self.rng.borrow_mut();
        match rvalue {
            Rvalue::Use(hole) => {
                let place = PlaceSelector::locals_and_args(self)
                    .except(&lhs)
                    .of_ty(lhs.ty(tcx, local_decls))
                    .select(&mut *rng)
                    .ok_or(SelectionError::Exhausted)?;
                // TODO: non-copy operands
                *hole = Operand::Copy(place);
            }
            Rvalue::UnaryOp(op, hole) => {
                let place = PlaceSelector::locals_and_args(self)
                    .except(&lhs)
                    .of_ty(lhs.ty(tcx, local_decls))
                    .select(&mut *rng)
                    .ok_or(SelectionError::Exhausted)?;
                *hole = Operand::Copy(place);
            }
            Rvalue::BinaryOp(op, hole_a, hole_b) => {
                use BinOp::*;
                match op {
                    Add | Sub | Mul | Div | Rem | BitXor | BitAnd | BitOr => {
                        // Both operand same type as lhs
                        let place_a = PlaceSelector::locals_and_args(self)
                            .except(&lhs)
                            .of_ty(lhs.ty(tcx, local_decls))
                            .select(&mut *rng)
                            .ok_or(SelectionError::Exhausted)?;
                        let place_b = PlaceSelector::locals_and_args(self)
                            .except(&lhs)
                            .of_ty(lhs.ty(tcx, local_decls))
                            .select(&mut *rng)
                            .ok_or(SelectionError::Exhausted)?;
                        // As the types are all integers or floats which are Copy, Move/Copy
                        // probably doesn't make much difference
                        *hole_a = Operand::Copy(place_a);
                        *hole_b = Operand::Copy(place_b);
                    }
                    Shl | Shr => {
                        let place_a = PlaceSelector::locals_and_args(self)
                            .except(&lhs)
                            .of_ty(lhs.ty(tcx, local_decls))
                            .select(&mut *rng)
                            .ok_or(SelectionError::Exhausted)?;
                        let place_b = PlaceSelector::locals_and_args(self)
                            .except(&lhs)
                            .filter_by_ty(|ty| {
                                let tykind = tcx.tykind(ty);
                                matches!(tykind, TyKind::Uint(..) | TyKind::Int(..))
                            })
                            .select(&mut *rng)
                            .ok_or(SelectionError::Exhausted)?;
                        *hole_a = Operand::Copy(place_a);
                        *hole_b = Operand::Copy(place_b);
                    }
                    Eq | Lt | Le | Ne | Ge | Gt => {
                        let place_a = PlaceSelector::locals_and_args(self)
                            .except(&lhs)
                            .filter_by_ty(|ty| {
                                let tykind = tcx.tykind(ty);
                                matches!(
                                    tykind,
                                    TyKind::Bool
                                        | TyKind::Char
                                        | TyKind::Int(..)
                                        | TyKind::Uint(..)
                                        | TyKind::Float(..)
                                        | TyKind::RawPtr(..)
                                )
                            })
                            .select(&mut *rng)
                            .ok_or(SelectionError::Exhausted)?;
                        let place_b = PlaceSelector::locals_and_args(self)
                            .except(&lhs)
                            .of_ty(place_a.ty(tcx, local_decls))
                            .select(&mut *rng)
                            .ok_or(SelectionError::Exhausted)?;
                        *hole_a = Operand::Copy(place_a);
                        *hole_b = Operand::Copy(place_b);
                    }
                    Offset => {
                        let place_a = PlaceSelector::locals_and_args(self)
                            .except(&lhs)
                            .filter_by_ty(|ty| {
                                let tykind = tcx.tykind(ty);
                                matches!(tykind, TyKind::RawPtr(..))
                            })
                            .select(&mut *rng)
                            .ok_or(SelectionError::Exhausted)?;
                        let place_b = PlaceSelector::locals_and_args(self)
                            .except(&lhs)
                            .of_tys(&[Ty::USIZE, Ty::ISIZE][..])
                            .select(&mut *rng)
                            .ok_or(SelectionError::Exhausted)?;
                        *hole_a = Operand::Copy(place_a);
                        *hole_b = Operand::Copy(place_b);
                    }
                }
            }
            _ => todo!(),
        }
        Ok(())
    }
}

trait GenerateRvalue {
    fn generate_use(&self, cur_stmt: &mut Statement) -> Result<()>;
    fn generate_unary_op(&self, cur_stmt: &mut Statement) -> Result<()>;
    fn generate_binary_op(&self, cur_stmt: &mut Statement) -> Result<()>;
    fn generate_checked_binary_op(&self, cur_stmt: &mut Statement) -> Result<()>;
    fn generate_len(&self, cur_stmt: &mut Statement) -> Result<()>;
    fn generate_retag(&self, cur_stmt: &mut Statement) -> Result<()>;
    fn generate_discriminant(&self, cur_stmt: &mut Statement) -> Result<()>;
    fn generate_rvalue(&self, cur_stmt: &mut Statement) -> Result<()>;
}

impl GenerateRvalue for GenerationCtx {
    /*
    Rvalue constaints:
    - Type matches with lhs
    - LHS and RHS do not alias
     */
    fn generate_use(&self, cur_stmt: &mut Statement) -> Result<()> {
        let (lhs, hole) = match cur_stmt {
            Statement::Assign(lhs, hole) => (lhs, hole),
            _ => unreachable!("Rvalue only appears in Statement::Assign"),
        };
        *hole = Rvalue::Use(Operand::Hole);
        self.choose_operand(cur_stmt)?;
        Ok(())
    }

    fn generate_unary_op(&self, cur_stmt: &mut Statement) -> Result<()> {
        let (lhs, hole) = match cur_stmt {
            Statement::Assign(lhs, hole) => (lhs, hole),
            _ => unreachable!("Rvalue only appears in Statement::Assign"),
        };
        use TyKind::*;
        use UnOp::*;
        let lhs_kind = lhs.tykind(&self.program.tcx, self.current_decls());
        let unop = match lhs_kind {
            Int(_) => &[Neg, Not][..],
            Float(_) => &[Neg][..],
            Uint(_) | Bool => &[Not][..],
            _ => &[][..],
        }
        .choose(&mut *self.rng.borrow_mut())
        .ok_or(SelectionError::NoPossibleOp)?;
        *hole = Rvalue::UnaryOp(*unop, Operand::Hole);
        self.choose_operand(cur_stmt)?;
        Ok(())
    }

    fn generate_binary_op(&self, cur_stmt: &mut Statement) -> Result<()> {
        let (lhs, hole) = match cur_stmt {
            Statement::Assign(lhs, hole) => (lhs, hole),
            _ => unreachable!("Rvalue only appears in Statement::Assign"),
        };

        use BinOp::*;
        use TyKind::*;
        let lhs_kind = lhs.tykind(&self.program.tcx, self.current_decls());
        let binop = match lhs_kind {
            Bool => &[Eq, Lt, Le, Ne, Ge, Gt][..],
            Float(_) => &[BitAnd, BitOr, BitXor, Add, Sub, Mul, Div, Rem][..],
            Uint(_) | Int(_) => &[BitAnd, BitOr, BitXor, Add, Sub, Mul, Div, Rem, Shl, Shr][..],
            RawPtr(..) => &[Offset],
            _ => &[][..],
        }
        .choose(&mut *self.rng.borrow_mut())
        .ok_or(SelectionError::NoPossibleOp)?;
        *hole = Rvalue::BinaryOp(*binop, Operand::Hole, Operand::Hole);
        self.choose_operand(cur_stmt)?;
        Ok(())
    }

    fn generate_checked_binary_op(&self, cur_stmt: &mut Statement) -> Result<()> {
        let (lhs, hole) = match cur_stmt {
            Statement::Assign(lhs, hole) => (lhs, hole),
            _ => unreachable!("Rvalue only appears in Statement::Assign"),
        };

        use BinOp::*;
        use TyKind::*;
        let lhs_kind = lhs.tykind(&self.program.tcx, self.current_decls());
        if let Some((ret, Ty::BOOL)) = lhs_kind.try_unwrap_pair() {
            let ret_kind = self.program.tcx.tykind(ret);
            let bin_op = match ret_kind {
                Float(_) => &[Add, Sub, Mul][..],
                Uint(_) | Int(_) => &[Add, Sub, Mul, Shl, Shr][..],
                _ => &[][..],
            }
            .choose(&mut *self.rng.borrow_mut())
            .ok_or(SelectionError::NoPossibleOp)?;
            *hole = Rvalue::CheckedBinaryOp(*bin_op, Operand::Hole, Operand::Hole);

            self.choose_operand(cur_stmt)?;
            Ok(())
        } else {
            Err(SelectionError::NoPossibleOp)
        }
    }

    fn generate_len(&self, cur_stmt: &mut Statement) -> Result<()> {
        todo!()
    }

    fn generate_retag(&self, cur_stmt: &mut Statement) -> Result<()> {
        todo!()
    }

    fn generate_discriminant(&self, cur_stmt: &mut Statement) -> Result<()> {
        todo!()
    }

    fn generate_rvalue(&self, cur_stmt: &mut Statement) -> Result<()> {
        match self
            .rng
            .borrow_mut()
            .gen_range(0..variant_count::<Rvalue>())
        {
            0 => self.generate_use(cur_stmt)?, // TODO: try other variants if one doesn't work
            1 => self.generate_unary_op(cur_stmt)?,
            2 => self.generate_binary_op(cur_stmt)?,
            3 => self.generate_checked_binary_op(cur_stmt)?,
            _ => todo!(),
        };
        Ok(())
    }
}

trait GenerateStatement {
    fn generate_assign(&mut self) -> Result<Statement>;
    fn generate_storage_live(&self) -> Result<Statement>;
    fn generate_storage_dead(&self) -> Result<Statement>;
    fn generate_deinit(&self) -> Result<Statement>;
    fn generate_set_discriminant(&self) -> Result<Statement>;
    fn choose_statement(&mut self);
}

impl GenerateStatement for GenerationCtx {
    fn generate_assign(&mut self) -> Result<Statement> {
        let lhs = PlaceSelector::locals(self)
            .mutable()
            .select(&mut *self.rng.borrow_mut());
        let lhs = lhs.unwrap_or_else(|| {
            let ty = self.choose_ty();
            let local = self.current_fn_mut().declare_new_var(Mutability::Mut, ty);
            Place::from_local(local)
        });
        let mut statement = Statement::Assign(lhs, Rvalue::Hole);
        self.generate_rvalue(&mut statement)?;
        Ok(statement)
    }

    fn generate_storage_live(&self) -> Result<Statement> {
        todo!()
    }

    fn generate_storage_dead(&self) -> Result<Statement> {
        todo!()
    }

    fn generate_deinit(&self) -> Result<Statement> {
        todo!()
    }

    fn generate_set_discriminant(&self) -> Result<Statement> {
        todo!()
    }
    fn choose_statement(&mut self) {
        let statement = match self
            .rng
            .get_mut()
            .gen_range(0..variant_count::<Statement>())
        {
            0 => self.generate_assign(),
            1 => self.generate_storage_live(),
            2 => self.generate_storage_dead(),
            3 => self.generate_deinit(),
            4 => self.generate_set_discriminant(),
            _ => unreachable!("Statement does not have these many variants"),
        }
        .unwrap();
        // TODO: retry another statement
        self.current_bb_mut().insert_statement(statement);
    }
}

impl GenerationCtx {
    fn choose_ty(&self) -> Ty {
        let mut rng = self.rng.borrow_mut();
        self.program
            .tcx
            .tys()
            .choose(&mut *rng)
            .expect("tys cannot be empty")
    }

    pub fn current_fn(&self) -> &Body {
        &self.program.functions[self.current_function]
    }

    pub fn current_fn_mut(&mut self) -> &mut Body {
        &mut self.program.functions[self.current_function]
    }

    pub fn current_bb_mut(&mut self) -> &mut BasicBlockData {
        &mut self.program.functions[self.current_function].basic_blocks[self.current_bb]
    }

    pub fn current_decls(&self) -> &LocalDecls {
        &self.current_fn().local_decls
    }

    fn generate_literal(&self, ty: Ty) {
        let tykind = self.program.tcx.tykind(ty);
        let mut rng = self.rng.borrow_mut();
        let literal = match ty {
            Ty::BOOL => Literal::Bool(rng.gen_bool(0.5)),
            Ty::CHAR => Literal::Char(char::from_u32(rng.gen_range(0..=0xD7FF)).unwrap()),
            _ => todo!(),
        };
    }

    pub fn generate(&mut self) {
        let argc = self.rng.get_mut().gen_range(0..=16);
        let arg_tys: Vec<Ty> = (0..argc).map(|_| self.choose_ty()).collect();

        let mut body = Body::new(&arg_tys, self.choose_ty());
        let starting_bb = body.new_basic_block(BasicBlockData::new());
        let new_fn = self.program.push_fn(body);
        self.current_function = new_fn;
        self.current_bb = starting_bb;

        let statement_count = self.rng.get_mut().gen_range(0..=128);
        (0..statement_count).for_each(|_| self.choose_statement());
    }
}
