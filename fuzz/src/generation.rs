use std::cell::RefCell;

use log::debug;
use mir::serialize::Serialize;
use mir::syntax::{
    BasicBlock, BasicBlockData, BinOp, Body, Function, Literal, Local, LocalDecls, Mutability,
    Operand, Place, Program, Rvalue, Statement, Terminator, Ty, UnOp,
};
use mir::vec::Idx;
use rand::{seq::IteratorRandom, Rng, RngCore, SeedableRng};

use crate::place::PlaceSelector;
use crate::ptable::PlaceTable;
use crate::ty::TyCtxt;

#[derive(Debug)]
enum SelectionError {
    Exhausted,
}

type Result<Node> = std::result::Result<Node, SelectionError>;

pub struct GenerationCtx {
    rng: RefCell<Box<dyn RngCore>>,
    program: Program,
    tcx: TyCtxt,
    pt: PlaceTable,
    exec_path: Vec<(Function, BasicBlock)>,
    current_function: Function,
    current_bb: BasicBlock,
}

trait GenerateOperand {
    fn choose_operand(&self, tys: &[Ty], excluded: &Place) -> Result<Operand>;
}

impl GenerateOperand for GenerationCtx {
    fn choose_operand(&self, tys: &[Ty], excluded: &Place) -> Result<Operand> {
        let places = PlaceSelector::new()
            .except(excluded)
            .of_tys(tys)
            .into_iter(&self.pt);
        self.make_choice(places, |place| {
            if self.tcx.is_copy(&place.ty(self.current_decls())) {
                Ok(Operand::Copy(place))
            } else {
                Ok(Operand::Move(place))
            }
        })
        .or_else(|_| {
            // TODO: allow array and tuple literals
            let literalble: Vec<Ty> = tys.iter().filter(|ty| ty.is_primitive()).cloned().collect();
            if literalble.is_empty() {
                Err(SelectionError::Exhausted)
            } else {
                let selected = literalble
                    .iter()
                    .choose(&mut *self.rng.borrow_mut())
                    .unwrap();
                let literal = self
                    .generate_literal(selected)
                    .expect("can always generate a literal of a literalble type");
                Ok(Operand::Constant(literal))
            }
        })
    }
}

trait GenerateRvalue {
    fn generate_use(&self, lhs: &Place) -> Result<Rvalue>;
    fn generate_unary_op(&self, lhs: &Place) -> Result<Rvalue>;
    fn generate_binary_op(&self, lhs: &Place) -> Result<Rvalue>;
    fn generate_checked_binary_op(&self, lhs: &Place) -> Result<Rvalue>;
    fn generate_cast(&self, lhs: &Place) -> Result<Rvalue>;
    // fn generate_len(&self, cur_stmt: &mut Statement) -> Result<()>;
    // fn generate_retag(&self, cur_stmt: &mut Statement) -> Result<()>;
    // fn generate_discriminant(&self, cur_stmt: &mut Statement) -> Result<()>;
    fn generate_rvalue(&self, lhs: &Place) -> Result<Rvalue>;
}

impl GenerateRvalue for GenerationCtx {
    /*
    Rvalue constaints:
    - Type matches with lhs
    - LHS and RHS do not alias
     */
    fn generate_use(&self, lhs: &Place) -> Result<Rvalue> {
        debug!("generating a use rvalue");
        let operand = self.choose_operand(&[lhs.ty(self.current_decls())], lhs)?;
        Ok(Rvalue::Use(operand))
    }

    fn generate_unary_op(&self, lhs: &Place) -> Result<Rvalue> {
        debug!("generating a unary op rvalue");
        use Ty::*;
        use UnOp::*;
        let lhs_ty = lhs.ty(self.current_decls());
        let unops = match lhs_ty {
            Int(_) => &[Neg, Not][..],
            Float(_) => &[Neg][..],
            Uint(_) | Bool => &[Not][..],
            _ => &[][..],
        };
        let rvalue = self.make_choice(unops.iter(), |unop| {
            let operand = self.choose_operand(&[lhs_ty.clone()], lhs)?;
            Ok(Rvalue::UnaryOp(*unop, operand))
        })?;
        Ok(rvalue)
    }

    fn generate_binary_op(&self, lhs: &Place) -> Result<Rvalue> {
        debug!("generating a binary op rvalue");

        use BinOp::*;
        use Ty::*;
        let lhs_ty = lhs.ty(self.current_decls());
        let binops = match lhs_ty {
            Bool => &[Eq, Lt, Le, Ne, Ge, Gt][..],
            Float(_) => &[BitAnd, BitOr, BitXor, Add, Sub, Mul, Div, Rem][..],
            Uint(_) | Int(_) => &[BitAnd, BitOr, BitXor, Add, Sub, Mul, Div, Rem, Shl, Shr][..],
            RawPtr(..) => &[Offset],
            _ => &[][..],
        };
        let rvalue = self.make_choice(binops.iter(), |binop| {
            let (l, r) = match *binop {
                Add | Sub | Mul | Div | Rem | BitXor | BitAnd | BitOr => {
                    // Both operand same type as lhs
                    let l = self.choose_operand(&[lhs_ty.clone()], lhs)?;
                    let r = self.choose_operand(&[lhs_ty.clone()], lhs)?;
                    // As the types are all integers or floats which are Copy, Move/Copy
                    // probably doesn't make much difference
                    (l, r)
                }
                Shl | Shr => {
                    // left operand same type as lhs, right can be uint or int
                    let l = self.choose_operand(&[lhs_ty.clone()], lhs)?;
                    // TODO: use a compile time concat
                    let r = self.choose_operand(
                        &[
                            Ty::ISIZE,
                            Ty::I8,
                            Ty::I16,
                            Ty::I32,
                            Ty::I64,
                            Ty::I128,
                            Ty::USIZE,
                            Ty::U8,
                            Ty::U16,
                            Ty::U32,
                            Ty::U64,
                            Ty::U128,
                        ],
                        lhs,
                    )?;
                    (l, r)
                }
                Eq | Lt | Le | Ne | Ge | Gt => {
                    // neither left or right operand needs to be the sme type as lhs
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
                    let l = self.choose_operand(&tys, lhs)?;
                    let r = self.choose_operand(&[l.ty(self.current_decls())], lhs)?;
                    (l, r)
                }
                Offset => {
                    let tys: Vec<Ty> = self
                        .tcx
                        .iter()
                        .filter(|ty| matches!(ty, Ty::RawPtr(..)))
                        .cloned()
                        .collect();
                    let l = self.choose_operand(&tys, lhs)?;
                    let r = self.choose_operand(&[Ty::USIZE, Ty::ISIZE], lhs)?;
                    (l, r)
                }
            };
            Ok(Rvalue::BinaryOp(*binop, l, r))
        })?;
        Ok(rvalue)
    }

    fn generate_checked_binary_op(&self, lhs: &Place) -> Result<Rvalue> {
        debug!("generating a checked binary op rvalue");

        use BinOp::*;
        use Ty::*;
        let lhs_ty = lhs.ty(self.current_decls());

        if let Some((ret, Ty::BOOL)) = lhs_ty.try_unwrap_pair() {
            let bin_ops = match ret {
                Float(_) => &[Add, Sub, Mul][..],
                Uint(_) | Int(_) => &[Add, Sub, Mul, Shl, Shr][..],
                _ => &[][..],
            };
            let rvalue = self.make_choice(bin_ops.iter(), |bin_op| {
                let (l, r) = match *bin_op {
                    Add | Sub | Mul => {
                        // Both operand same type as lhs
                        let l = self.choose_operand(&[lhs_ty.clone()], lhs)?;
                        let r = self.choose_operand(&[lhs_ty.clone()], lhs)?;
                        // As the types are all integers or floats which are Copy, Move/Copy
                        // probably doesn't make much difference
                        (l, r)
                    }
                    Shl | Shr => {
                        // left operand same type as lhs, right can be uint or int
                        let l = self.choose_operand(&[lhs_ty.clone()], lhs)?;
                        // TODO: use a compile time concat
                        let r = self.choose_operand(
                            &[
                                Ty::ISIZE,
                                Ty::I8,
                                Ty::I16,
                                Ty::I32,
                                Ty::I64,
                                Ty::I128,
                                Ty::USIZE,
                                Ty::U8,
                                Ty::U16,
                                Ty::U32,
                                Ty::U64,
                                Ty::U128,
                            ],
                            lhs,
                        )?;
                        (l, r)
                    }
                    _ => unreachable!(),
                };
                Ok(Rvalue::CheckedBinaryOp(*bin_op, l, r))
            })?;
            Ok(rvalue)
        } else {
            Err(SelectionError::Exhausted)
        }
    }

    fn generate_cast(&self, lhs: &Place) -> Result<Rvalue> {
        debug!("generating a cast rvalue");

        let target_ty = lhs.ty(self.current_decls());
        let source_tys = match target_ty {
            // TODO: no int to ptr cast for now
            Ty::Int(..) | Ty::Uint(..) => &[
                Ty::ISIZE,
                Ty::I8,
                Ty::I16,
                Ty::I32,
                Ty::I64,
                Ty::I128,
                Ty::USIZE,
                Ty::U8,
                Ty::U16,
                Ty::U32,
                Ty::U64,
                Ty::U128,
                Ty::F32,
                Ty::F64,
                Ty::Char,
                Ty::Bool,
            ][..],
            Ty::Float(..) => &[
                Ty::ISIZE,
                Ty::I8,
                Ty::I16,
                Ty::I32,
                Ty::I64,
                Ty::I128,
                Ty::USIZE,
                Ty::U8,
                Ty::U16,
                Ty::U32,
                Ty::U64,
                Ty::U128,
                Ty::F32,
                Ty::F64,
            ][..],
            _ => &[][..],
        };
        let rvalue = self.make_choice(source_tys.iter(), |source_ty| {
            let source = self.choose_operand(&[source_ty.clone()], lhs)?;
            Ok(Rvalue::Cast(source, target_ty.clone()))
        })?;
        Ok(rvalue)
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

    fn generate_rvalue(&self, lhs: &Place) -> Result<Rvalue> {
        let choices: Vec<fn(&GenerationCtx, &Place) -> Result<Rvalue>> = vec![
            Self::generate_use,
            Self::generate_unary_op,
            Self::generate_binary_op,
            Self::generate_checked_binary_op,
            Self::generate_cast,
            // Self::generate_len,
            // Self::generate_retag,
            // Self::generate_discriminant,
        ];

        self.make_choice(choices.into_iter(), |f| f(self, lhs))
    }
}

trait GenerateStatement {
    fn generate_assign(&mut self) -> Result<Statement>;
    fn generate_new_var(&mut self) -> Result<Statement>;
    // fn generate_storage_live(&self) -> Result<Statement>;
    // fn generate_storage_dead(&self) -> Result<Statement>;
    // fn generate_deinit(&self) -> Result<Statement>;
    // fn generate_set_discriminant(&self) -> Result<Statement>;
    fn choose_statement(&mut self);
}

impl GenerateStatement for GenerationCtx {
    fn generate_assign(&mut self) -> Result<Statement> {
        let lhs_choices = PlaceSelector::new().maybe_uninit().into_iter(&self.pt);

        self.make_choice(lhs_choices, |lhs| {
            debug!(
                "generating an assignment statement with lhs ty {}",
                lhs.ty(self.current_decls()).serialize()
            );
            let statement = Statement::Assign(lhs.clone(), self.generate_rvalue(&lhs)?);
            Ok(statement)
        })
    }

    fn generate_new_var(&mut self) -> Result<Statement> {
        let ty = self.tcx.choose_ty(&mut *self.rng.borrow_mut());
        self.declare_new_var(Mutability::Mut, ty);
        Ok(Statement::Nop)
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
        let choices: Vec<fn(&mut GenerationCtx) -> Result<Statement>> = vec![
            Self::generate_assign,
            Self::generate_new_var,
            // Self::generate_storage_live,
            // Self::generate_storage_dead,
            // Self::generate_deinit,
            // Self::generate_set_discriminant,
        ];

        let statement = self
            .make_choice_mut(choices.into_iter(), |ctx, f| f(ctx))
            .expect("deadend");
        self.post_generation(&statement);
        self.current_bb_mut().insert_statement(statement);
    }
}

trait GenerateTerminator {
    fn generate_return(&self) -> Result<Terminator>;

    fn choose_terminator(&mut self);
}

impl GenerateTerminator for GenerationCtx {
    fn generate_return(&self) -> Result<Terminator> {
        Ok(Terminator::Return)
    }

    fn choose_terminator(&mut self) {
        let choices: Vec<fn(&GenerationCtx) -> Result<Terminator>> = vec![Self::generate_return];
        let terminator = self
            .make_choice(choices.into_iter(), |f| f(self))
            .expect("deadend");
        self.current_bb_mut().terminator = Some(terminator);
    }
}

impl GenerationCtx {
    fn make_choice<T, F, R>(
        &self,
        choices: impl Iterator<Item = T> + Clone,
        mut use_choice: F,
    ) -> Result<R>
    where
        F: FnMut(T) -> Result<R>,
        T: Clone,
    {
        let mut failed: Vec<usize> = vec![];
        loop {
            let (i, choice) = choices
                .clone()
                .enumerate()
                .filter(|(i, _)| !failed.contains(i))
                .choose(&mut *self.rng.borrow_mut())
                .ok_or(SelectionError::Exhausted)?;
            let res = use_choice(choice.clone());
            match res {
                Ok(val) => return Ok(val),
                Err(_) => {
                    failed.push(i);
                }
            }
        }
    }

    fn make_choice_mut<T, F, R>(
        &mut self,
        choices: impl Iterator<Item = T>,
        mut use_choice: F,
    ) -> Result<R>
    where
        F: FnMut(&mut Self, T) -> Result<R>,
        T: Clone,
    {
        let mut choices: Vec<T> = choices.collect();
        loop {
            let (i, choice) = choices
                .iter()
                .enumerate()
                .choose(&mut *self.rng.borrow_mut())
                .ok_or(SelectionError::Exhausted)?;
            let res = use_choice(self, choice.clone());
            match res {
                Ok(val) => return Ok(val),
                Err(_) => {
                    choices.remove(i);
                }
            }
        }
    }

    pub fn new(seed: u64) -> Self {
        let rng = RefCell::new(Box::new(rand::rngs::SmallRng::seed_from_u64(seed)));
        let tcx = TyCtxt::new(&mut *rng.borrow_mut());
        // TODO: don't zero-initialize current_function and current_bb
        Self {
            rng,
            tcx,
            program: Program::new(),
            pt: PlaceTable::new(),
            exec_path: vec![],
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

    fn declare_new_var(&mut self, mutability: Mutability, ty: Ty) -> Local {
        let local = self
            .current_fn_mut()
            .declare_new_var(mutability, ty.clone());
        self.pt.add_local(local, ty);
        local
    }

    fn generate_literal(&self, ty: &Ty) -> Option<Literal> {
        let mut rng = self.rng.borrow_mut();
        let lit: Literal = match *ty {
            Ty::Bool => rng.gen_bool(0.5).into(),
            // TODO: another range
            Ty::Char => char::from_u32(rng.gen_range(0..=0xD7FF)).unwrap().into(),
            Ty::USIZE => rng
                .gen_range(usize::MIN..=usize::MAX)
                .try_into()
                .expect("usize isn't greater than 128 bits"),
            Ty::U8 => rng.gen_range(u8::MIN..=u8::MAX).into(),
            Ty::U16 => rng.gen_range(u16::MIN..=u16::MAX).into(),
            Ty::U32 => rng.gen_range(u32::MIN..=u32::MAX).into(),
            Ty::U64 => rng.gen_range(u64::MIN..=u64::MAX).into(),
            Ty::U128 => rng.gen_range(u128::MIN..=u128::MAX).into(),
            Ty::ISIZE => rng
                .gen_range(isize::MIN..=isize::MAX)
                .try_into()
                .expect("isize isn't greater than 128 bits"),
            Ty::I8 => rng.gen_range(i8::MIN..=i8::MAX).into(),
            Ty::I16 => rng.gen_range(i16::MIN..=i16::MAX).into(),
            Ty::I32 => rng.gen_range(i32::MIN..=i32::MAX).into(),
            Ty::I64 => rng.gen_range(i64::MIN..=i64::MAX).into(),
            Ty::I128 => rng.gen_range(i128::MIN..=i128::MAX).into(),
            _ => return None,
        };
        Some(lit)
    }

    // Move generation context to an executed function
    fn enter_new_fn(&mut self, args: &[Ty], return_ty: Ty) {
        let mut body = Body::new(args, return_ty);

        let starting_bb = body.new_basic_block(BasicBlockData::new());
        let new_fn = self.program.push_fn(body);
        self.current_function = new_fn;
        self.current_bb = starting_bb;

        self.exec_path.push((new_fn, starting_bb));

        self.pt
            .enter_fn(&self.program.functions[self.current_function]);
    }

    pub fn generate(mut self) -> Program {
        let arg_tys = vec![Ty::I32];

        self.enter_new_fn(&arg_tys, Ty::I32);

        let ret_node = self.pt.get_node(&Place::RETURN_SLOT).unwrap();
        while !self.pt.is_place_init(ret_node) {
            self.choose_statement();
        }

        self.choose_terminator();
        self.program
    }

    fn post_generation(&mut self, stmt: &Statement) {
        match stmt {
            Statement::Assign(lhs, _) => {
                let pidx = self.pt.get_node(lhs).expect("lhs is reachable");
                self.pt.mark_place_init(pidx);
            }
            Statement::StorageLive(_) => todo!(),
            Statement::StorageDead(_) => todo!(),
            Statement::Deinit(_) => todo!(),
            Statement::SetDiscriminant(_, _) => todo!(),
            Statement::Nop => {}
        }
    }
}
