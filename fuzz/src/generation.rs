use std::{borrow::BorrowMut, cell::RefCell, fmt, mem::variant_count};

use mir::syntax::{
    BasicBlock, BasicBlockData, BinOp, Body, FloatTy, Function, IntTy, Literal, Local, LocalDecls,
    Mutability, Operand, Place, Program, Rvalue, Statement, Ty, UintTy, UnOp,
};
use mir::vec::Idx;
use rand::{
    seq::{IteratorRandom, SliceRandom},
    Rng, RngCore, SeedableRng,
};

use crate::place::PlaceSelector;
use crate::ty::TyCtxt;

enum SelectionError {
    Exhausted,

    GiveUp,
}

impl fmt::Debug for SelectionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

type Result<Node> = std::result::Result<Node, SelectionError>;

pub struct GenerationCtx {
    rng: RefCell<Box<dyn RngCore>>,
    program: Program,
    tcx: TyCtxt,
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

        let local_decls = self.current_decls();
        let lhs_ty = lhs.ty(local_decls);
        let mut rng = self.rng.borrow_mut();
        match rvalue {
            Rvalue::Use(hole) => {
                let place = PlaceSelector::locals_and_args(self)
                    .except(&lhs)
                    .of_ty(lhs_ty)
                    .select(&mut *rng)
                    .ok_or(SelectionError::Exhausted)?;
                // TODO: non-copy operands
                *hole = Operand::Copy(place);
            }
            Rvalue::UnaryOp(op, hole) => {
                if let Some(place) = PlaceSelector::locals_and_args(self)
                    .except(&lhs)
                    .of_ty(lhs_ty.clone())
                    .select(&mut *rng)
                {
                    *hole = Operand::Copy(place);
                } else {
                    let literal = self
                        .generate_literal(lhs_ty.clone())
                        .ok_or(SelectionError::GiveUp)?;
                    *hole = Operand::Constant(literal, lhs_ty.clone());
                }
            }
            Rvalue::BinaryOp(op, hole_a, hole_b) => {
                use BinOp::*;
                match op {
                    Add | Sub | Mul | Div | Rem | BitXor | BitAnd | BitOr => {
                        // Both operand same type as lhs
                        let place_a = PlaceSelector::locals_and_args(self)
                            .except(&lhs)
                            .of_ty(lhs.ty(local_decls))
                            .select(&mut *rng)
                            .ok_or(SelectionError::Exhausted)?;
                        let place_b = PlaceSelector::locals_and_args(self)
                            .except(&lhs)
                            .of_ty(lhs.ty(local_decls))
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
                            .of_ty(lhs.ty(local_decls))
                            .select(&mut *rng)
                            .ok_or(SelectionError::Exhausted)?;
                        let b_tys: Vec<Ty> = self
                            .tcx
                            .iter()
                            .filter(|ty| matches!(ty, Ty::Uint(..) | Ty::Int(..)))
                            .cloned()
                            .collect();
                        let place_b = PlaceSelector::locals_and_args(self)
                            .except(&lhs)
                            .of_tys(&b_tys)
                            .select(&mut *rng)
                            .ok_or(SelectionError::Exhausted)?;
                        *hole_a = Operand::Copy(place_a);
                        *hole_b = Operand::Copy(place_b);
                    }
                    Eq | Lt | Le | Ne | Ge | Gt => {
                        let tys: Vec<Ty> = self
                            .tcx
                            .iter()
                            .filter(|ty| {
                                matches!(
                                    ty,
                                    Ty::Bool
                                        | Ty::Char
                                        | Ty::Int(..)
                                        | Ty::Uint(..)
                                        | Ty::Float(..)
                                        | Ty::RawPtr(..)
                                )
                            })
                            .cloned()
                            .collect();
                        let place_a = PlaceSelector::locals_and_args(self)
                            .except(&lhs)
                            .of_tys(&tys)
                            .select(&mut *rng)
                            .ok_or(SelectionError::Exhausted)?;
                        let place_b = PlaceSelector::locals_and_args(self)
                            .except(&lhs)
                            .of_ty(place_a.ty(local_decls))
                            .select(&mut *rng)
                            .ok_or(SelectionError::Exhausted)?;
                        *hole_a = Operand::Copy(place_a);
                        *hole_b = Operand::Copy(place_b);
                    }
                    Offset => {
                        let tys: Vec<Ty> = self
                            .tcx
                            .iter()
                            .filter(|ty| matches!(ty, Ty::RawPtr(..)))
                            .cloned()
                            .collect();
                        let place_a = PlaceSelector::locals_and_args(self)
                            .except(&lhs)
                            .of_tys(&tys)
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
                    _ => unreachable!(),
                }
            }
            _ => todo!(),
        }
        Ok(())
    }
}

trait GenerateRvalue {
    fn generate_use(&mut self, cur_stmt: &mut Statement) -> Result<()>;
    fn generate_unary_op(&mut self, cur_stmt: &mut Statement) -> Result<()>;
    fn generate_binary_op(&mut self, cur_stmt: &mut Statement) -> Result<()>;
    fn generate_checked_binary_op(&mut self, cur_stmt: &mut Statement) -> Result<()>;
    // fn generate_len(&self, cur_stmt: &mut Statement) -> Result<()>;
    // fn generate_retag(&self, cur_stmt: &mut Statement) -> Result<()>;
    // fn generate_discriminant(&self, cur_stmt: &mut Statement) -> Result<()>;
    fn generate_rvalue(&mut self, cur_stmt: &mut Statement) -> Result<()>;
}

impl GenerateRvalue for GenerationCtx {
    /*
    Rvalue constaints:
    - Type matches with lhs
    - LHS and RHS do not alias
     */
    fn generate_use(&mut self, cur_stmt: &mut Statement) -> Result<()> {
        let (lhs, hole) = match cur_stmt {
            Statement::Assign(lhs, hole) => (lhs, hole),
            _ => unreachable!("Rvalue only appears in Statement::Assign"),
        };
        *hole = Rvalue::Use(Operand::Hole);
        self.choose_operand(cur_stmt)?;
        Ok(())
    }

    fn generate_unary_op(&mut self, cur_stmt: &mut Statement) -> Result<()> {
        let (lhs, hole) = match cur_stmt {
            Statement::Assign(lhs, hole) => (lhs, hole),
            _ => unreachable!("Rvalue only appears in Statement::Assign"),
        };
        use Ty::*;
        use UnOp::*;
        let lhs_ty = lhs.ty(self.current_decls());
        let unop = match lhs_ty {
            Int(_) => &[Neg, Not][..],
            Float(_) => &[Neg][..],
            Uint(_) | Bool => &[Not][..],
            _ => &[][..],
        }
        .choose(&mut *self.rng.borrow_mut())
        .ok_or(SelectionError::GiveUp)?;
        *hole = Rvalue::UnaryOp(*unop, Operand::Hole);
        self.choose_operand(cur_stmt)?;
        Ok(())
    }

    fn generate_binary_op(&mut self, cur_stmt: &mut Statement) -> Result<()> {
        let (lhs, hole) = match cur_stmt {
            Statement::Assign(lhs, hole) => (lhs, hole),
            _ => unreachable!("Rvalue only appears in Statement::Assign"),
        };

        use BinOp::*;
        use Ty::*;
        let lhs_ty = lhs.ty(self.current_decls());
        let binop = match lhs_ty {
            Bool => &[Eq, Lt, Le, Ne, Ge, Gt][..],
            Float(_) => &[BitAnd, BitOr, BitXor, Add, Sub, Mul, Div, Rem][..],
            Uint(_) | Int(_) => &[BitAnd, BitOr, BitXor, Add, Sub, Mul, Div, Rem, Shl, Shr][..],
            RawPtr(..) => &[Offset],
            _ => &[][..],
        }
        .choose(&mut *self.rng.borrow_mut())
        .ok_or(SelectionError::GiveUp)?;
        *hole = Rvalue::BinaryOp(*binop, Operand::Hole, Operand::Hole);
        self.choose_operand(cur_stmt)?;
        Ok(())
    }

    fn generate_checked_binary_op(&mut self, cur_stmt: &mut Statement) -> Result<()> {
        let (lhs, hole) = match cur_stmt {
            Statement::Assign(lhs, hole) => (lhs, hole),
            _ => unreachable!("Rvalue only appears in Statement::Assign"),
        };

        use BinOp::*;
        use Ty::*;
        let lhs_ty = lhs.ty(self.current_decls());

        if let Some((ret, Ty::BOOL)) = lhs_ty.try_unwrap_pair() {
            let bin_op = match ret {
                Float(_) => &[Add, Sub, Mul][..],
                Uint(_) | Int(_) => &[Add, Sub, Mul, Shl, Shr][..],
                _ => &[][..],
            }
            .choose(&mut *self.rng.borrow_mut())
            .ok_or(SelectionError::GiveUp)?;
            *hole = Rvalue::CheckedBinaryOp(*bin_op, Operand::Hole, Operand::Hole);

            self.choose_operand(cur_stmt)?;
            Ok(())
        } else {
            Err(SelectionError::GiveUp)
        }
    }

    // fn generate_len(&self, cur_stmt: &mut Statement) -> Result<()> {
    //     todo!()
    // }

    // fn generate_retag(&self, cur_stmt: &mut Statement) -> Result<()> {
    //     todo!()
    // }

    // fn generate_discriminant(&self, cur_stmt: &mut Statement) -> Result<()> {
    //     todo!()
    // }

    fn generate_rvalue(&mut self, cur_stmt: &mut Statement) -> Result<()> {
        let mut choices: Vec<fn(&mut GenerationCtx, &mut Statement) -> Result<()>> = vec![
            Self::generate_use,
            Self::generate_unary_op,
            Self::generate_binary_op,
            Self::generate_checked_binary_op,
            // Self::generate_len,
            // Self::generate_retag,
            // Self::generate_discriminant,
        ];

        loop {
            let (i, choice) = choices
                .iter()
                .enumerate()
                .choose(&mut *self.rng.borrow_mut())
                .ok_or(SelectionError::GiveUp)?;
            let res = choice(self, cur_stmt);
            match res {
                Ok(()) => return Ok(()),
                Err(SelectionError::GiveUp) => {
                    choices.remove(i);
                }
                _ => unreachable!(),
            }
        }
    }
}

trait GenerateStatement {
    fn generate_assign(&mut self) -> Result<Statement>;
    // fn generate_storage_live(&self) -> Result<Statement>;
    // fn generate_storage_dead(&self) -> Result<Statement>;
    // fn generate_deinit(&self) -> Result<Statement>;
    // fn generate_set_discriminant(&self) -> Result<Statement>;
    fn choose_statement(&mut self);
}

impl GenerateStatement for GenerationCtx {
    fn generate_assign(&mut self) -> Result<Statement> {
        let lhs = PlaceSelector::locals(self)
            .mutable()
            .select(&mut *self.rng.borrow_mut());
        let lhs = lhs.unwrap_or_else(|| {
            let ty = self.tcx.choose_ty(&mut *self.rng.borrow_mut());
            let local = self.current_fn_mut().declare_new_var(Mutability::Mut, ty);
            Place::from_local(local)
        });
        let mut statement = Statement::Assign(lhs, Rvalue::Hole);
        self.generate_rvalue(&mut statement)?;
        Ok(statement)
    }

    // fn generate_storage_live(&self) -> Result<Statement> {
    //     todo!()
    // }

    // fn generate_storage_dead(&self) -> Result<Statement> {
    //     todo!()
    // }

    // fn generate_deinit(&self) -> Result<Statement> {
    //     todo!()
    // }

    // fn generate_set_discriminant(&self) -> Result<Statement> {
    //     todo!()
    // }
    fn choose_statement(&mut self) {
        let mut choices: Vec<fn(&mut GenerationCtx) -> Result<Statement>> = vec![
            Self::generate_assign,
            // Self::generate_storage_live,
            // Self::generate_storage_dead,
            // Self::generate_deinit,
            // Self::generate_set_discriminant,
        ];
        let statement = loop {
            let (i, choice) = choices
                .iter()
                .enumerate()
                .choose(&mut *self.rng.borrow_mut())
                .unwrap(); // Deadend
            let res = choice(self);
            match res {
                Ok(stmt) => break stmt,
                Err(SelectionError::GiveUp) => {
                    choices.remove(i);
                }
                _ => unreachable!(),
            }
        };
        self.current_bb_mut().insert_statement(statement);
    }
}

impl GenerationCtx {
    pub fn new() -> Self {
        let rng = RefCell::new(Box::new(rand::rngs::SmallRng::seed_from_u64(0)));
        let tcx = TyCtxt::new(&mut *rng.borrow_mut());
        // TODO: don't zero-initialize current_function and current_bb
        Self {
            rng,
            tcx,
            program: Program::new(),
            current_function: Function::new(0),
            current_bb: BasicBlock::new(0),
        }
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

    fn generate_literal(&self, ty: Ty) -> Option<Literal> {
        let mut rng = self.rng.borrow_mut();
        let lit = match ty {
            Ty::BOOL => Literal::Bool(rng.gen_bool(0.5)),
            Ty::CHAR => Literal::Char(char::from_u32(rng.gen_range(0..=0xD7FF)).unwrap()),
            Ty::USIZE => Literal::Int(
                rng.gen_range(usize::MIN..=usize::MAX)
                    .try_into()
                    .expect("usize isn't greater than 128 bits"),
            ),
            Ty::U8 => Literal::Int(rng.gen_range(u8::MIN..=u8::MAX).into()),
            Ty::U16 => Literal::Int(rng.gen_range(u16::MIN..=u16::MAX).into()),
            Ty::U32 => Literal::Int(rng.gen_range(u32::MIN..=u32::MAX).into()),
            Ty::U64 => Literal::Int(rng.gen_range(u64::MIN..=u64::MAX).into()),
            Ty::U128 => Literal::Int(rng.gen_range(u128::MIN..=u128::MAX)),
            _ => return None,
        };
        Some(lit)
    }

    pub fn generate(&mut self) {
        let argc = self.rng.get_mut().gen_range(0..=16);
        let arg_tys: Vec<Ty> = (0..argc)
            .map(|_| self.tcx.choose_ty(&mut *self.rng.borrow_mut()))
            .collect();

        let mut body = Body::new(&arg_tys, self.tcx.choose_ty(&mut *self.rng.borrow_mut()));
        let starting_bb = body.new_basic_block(BasicBlockData::new());
        let new_fn = self.program.push_fn(body);
        self.current_function = new_fn;
        self.current_bb = starting_bb;

        let statement_count = self.rng.get_mut().gen_range(0..=128);
        (0..statement_count).for_each(|_| self.choose_statement());
    }
}
