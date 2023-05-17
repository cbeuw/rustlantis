mod intrinsics;

use std::cell::RefCell;
use std::{cmp, vec};

use log::{debug, trace};
use mir::serialize::Serialize;
use mir::syntax::{
    BasicBlock, BasicBlockData, BinOp, Body, Callee, Function, IntTy, Literal, Local, LocalDecls,
    Mutability, Operand, Place, Program, Rvalue, Statement, SwitchTargets, Terminator, Ty, UnOp,
};
use rand::{seq::IteratorRandom, Rng, RngCore, SeedableRng};
use rand_distr::{Distribution, WeightedError, WeightedIndex};

use crate::literal::GenLiteral;
use crate::place_select::{PlaceSelector, Weight};
use crate::ptable::{HasDataflow, PlaceTable};
use crate::ty::TyCtxt;

use self::intrinsics::ArithOffset;
use crate::generation::intrinsics::CoreIntrinsic;

/// Max. number of statements & declarations in a bb
const BB_MAX_LEN: usize = 32;
/// Max. number of switch targets in a SwitchInt terminator
const MAX_SWITCH_TARGETS: usize = 8;
const MAX_FN_COUNT: usize = 50;

#[derive(Debug)]
pub enum SelectionError {
    Exhausted,
}

type Result<Node> = std::result::Result<Node, SelectionError>;

pub struct GenerationCtx {
    rng: RefCell<Box<dyn RngCore>>,
    program: Program,
    tcx: TyCtxt,
    pt: PlaceTable,
    return_stack: Vec<(Function, BasicBlock)>,
    current_function: Function,
    current_bb: BasicBlock,
}

// Operand
impl GenerationCtx {
    fn choose_operand(&self, tys: &[Ty], excluded: &Place) -> Result<Operand> {
        let operand: Result<Operand> = try {
            let (ppath, weights) = PlaceSelector::for_operand()
                .except(excluded)
                .of_tys(tys)
                .into_weighted(&self.pt)
                .ok_or(SelectionError::Exhausted)?;
            self.make_choice_weighted(ppath.into_iter(), weights, |ppath| {
                if self.tcx.is_copy(&ppath.target_node(&self.pt).ty) {
                    Ok(Operand::Copy(ppath.to_place(&self.pt)))
                } else {
                    Ok(Operand::Move(ppath.to_place(&self.pt)))
                }
            })?
        };
        operand.or_else(|_| {
            // TODO: allow array and tuple literals
            let literalble: Vec<Ty> = tys
                .iter()
                .filter(|ty| <dyn RngCore>::is_literalble(*ty))
                .cloned()
                .collect();
            if literalble.is_empty() {
                Err(SelectionError::Exhausted)
            } else {
                let selected = literalble
                    .iter()
                    .choose(&mut *self.rng.borrow_mut())
                    .unwrap();
                let literal = self
                    .rng
                    .borrow_mut()
                    .gen_literal(selected)
                    .expect("can always generate a literal of a literalble type");
                Ok(Operand::Constant(literal))
            }
        })
    }
}

// Rvalue
impl GenerationCtx {
    /*
    Rvalue constaints:
    - Type matches with lhs
    - LHS and RHS do not alias
     */
    fn generate_use(&self, lhs: &Place) -> Result<Rvalue> {
        trace!(
            "generating use with {}: {}",
            lhs.serialize(),
            lhs.ty(self.current_decls()).serialize()
        );
        let operand = self.choose_operand(&[lhs.ty(self.current_decls())], lhs)?;
        Ok(Rvalue::Use(operand))
    }

    fn generate_unary_op(&self, lhs: &Place) -> Result<Rvalue> {
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
        use BinOp::*;
        use Ty::*;
        let lhs_ty = lhs.ty(self.current_decls());
        let binops = match lhs_ty {
            Bool => &[BitAnd, BitOr, BitXor, Eq, Lt, Le, Ne, Ge, Gt][..],
            // FIXME: Floating point rem https://github.com/rust-lang/rust/issues/109567
            Float(_) => &[Add, Sub, Mul, Div /*, Rem */][..],
            Int(_) => &[BitAnd, BitOr, BitXor, Add, Sub, Mul, Shl, Shr][..],
            Uint(_) => &[BitAnd, BitOr, BitXor, Add, Sub, Mul, Div, Rem, Shl, Shr][..],
            // RawPtr(..) => &[Offset],
            _ => &[][..],
        };
        let rvalue = self.make_choice(binops.iter(), |binop| {
            let (l, r) = match *binop {
                Div | Rem => {
                    // Avoid div/rem by zero
                    let l = self.choose_operand(&[lhs_ty.clone()], lhs)?;
                    let r = Operand::Constant(self.rng.borrow_mut().gen_literal_non_zero(&lhs_ty).expect("can generate literal"));
                    (l, r)
                }
                Add | Sub | Mul | BitXor | BitAnd | BitOr => {
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
                Eq | Ne => {
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
                Lt | Le | Ge | Gt => {
                    // neither left or right operand needs to be the sme type as lhs
                    let tys = [
                        Ty::Bool,
                        Ty::Char,
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
                    ];
                    let l = self.choose_operand(&tys, lhs)?;
                    let r = self.choose_operand(&[l.ty(self.current_decls())], lhs)?;
                    (l, r)
                }
                Offset => {
                    let Ty::RawPtr(_, lhs_mutability) = lhs_ty else {
                        unreachable!("lhs is a ptr");
                    };
                    let tys: Vec<Ty> = self
                        .tcx
                        .iter()
                        .filter(|ty| matches!(ty, Ty::RawPtr(_, mutability) if *mutability == lhs_mutability))
                        .cloned()
                        .collect();
                    let l = self.choose_operand(&tys, lhs)?;
                    let r = self.choose_operand(&[Ty::ISIZE], lhs)?;
                    (l, r)
                }
            };
            Ok(Rvalue::BinaryOp(*binop, l, r))
        })?;
        Ok(rvalue)
    }

    fn generate_checked_binary_op(&self, lhs: &Place) -> Result<Rvalue> {
        use BinOp::*;
        use Ty::*;
        let lhs_ty = lhs.ty(self.current_decls());

        if let Some([ret, Ty::BOOL]) = lhs_ty.tuple_elems() {
            let bin_ops = match ret {
                Uint(_) | Int(_) => &[Add, Sub, Mul][..],
                _ => &[][..],
            };
            let rvalue = self.make_choice(bin_ops.iter(), |bin_op| {
                let (l, r) = match *bin_op {
                    Add | Sub | Mul => {
                        // Both operand same type as lhs
                        let l = self.choose_operand(&[ret.clone()], lhs)?;
                        let r = self.choose_operand(&[ret.clone()], lhs)?;
                        // As the types are all integers or floats which are Copy, Move/Copy
                        // probably doesn't make much difference
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
        let rvalue = self.make_choice(
            // XXX: remove the filter once https://github.com/rust-lang/rust/pull/109160 is merged
            source_tys.iter().filter(|ty| **ty != target_ty),
            |source_ty| {
                let source = self.choose_operand(&[source_ty.clone()], lhs)?;
                Ok(Rvalue::Cast(source, target_ty.clone()))
            },
        )?;
        Ok(rvalue)
    }

    fn generate_address_of(&self, lhs: &Place) -> Result<Rvalue> {
        let target_ty = lhs.ty(self.current_decls());
        let (source_ty, mutability) = match target_ty {
            Ty::RawPtr(box ty, mutability) => (ty, mutability),
            _ => return Err(SelectionError::Exhausted),
        };
        let (candidates, weights) = PlaceSelector::for_pointee()
            .of_ty(source_ty)
            .except(lhs)
            .into_weighted(&self.pt)
            .ok_or(SelectionError::Exhausted)?;
        self.make_choice_weighted(candidates.into_iter(), weights, |ppath| {
            Ok(Rvalue::AddressOf(mutability, ppath.to_place(&self.pt)))
        })
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
        let choices_and_weights: Vec<(fn(&GenerationCtx, &Place) -> Result<Rvalue>, usize)> = vec![
            (Self::generate_use, 1),
            (Self::generate_unary_op, 1),
            (Self::generate_binary_op, 1),
            (Self::generate_checked_binary_op, 1),
            (Self::generate_cast, 1),
            (Self::generate_address_of, 2),
        ];

        let (choices, weights): (
            Vec<fn(&GenerationCtx, &Place) -> Result<Rvalue>>,
            Vec<usize>,
        ) = choices_and_weights.into_iter().unzip();

        self.make_choice_weighted(
            choices.into_iter(),
            WeightedIndex::new(weights).expect("weights are valid"),
            |f| f(self, lhs),
        )
    }
}

// Statement
impl GenerationCtx {
    fn generate_assign(&self) -> Result<Statement> {
        let (lhs_choices, weights) = PlaceSelector::for_lhs()
            .into_weighted(&self.pt)
            .ok_or(SelectionError::Exhausted)?;

        self.make_choice_weighted(lhs_choices.into_iter(), weights, |ppath| {
            let lhs = ppath.to_place(&self.pt);
            debug!(
                "generating an assignment statement with lhs {}: {}",
                lhs.serialize(),
                lhs.ty(self.current_decls()).serialize()
            );

            let statement = Statement::Assign(lhs.clone(), self.generate_rvalue(&lhs)?);
            Ok(statement)
        })
    }

    // Hack to take &self
    fn generate_new_var(&self) -> Result<Statement> {
        Ok(Statement::Nop)
    }

    fn declare_new_var(&mut self, mutability: Mutability, ty: Ty) -> Local {
        let local = self
            .current_fn_mut()
            .declare_new_var(mutability, ty.clone());
        trace!(
            "generated new var {}: {}",
            local.identifier(),
            ty.serialize()
        );
        self.pt.allocate_local(local, ty);
        local
    }

    fn generate_storage_live(&self) -> Result<Statement> {
        let local = self
            .current_decls()
            .indices()
            .filter(|local| !self.pt.is_place_live(local))
            .choose(&mut *self.rng.borrow_mut())
            .ok_or(SelectionError::Exhausted)?;
        Ok(Statement::StorageLive(local))
    }

    fn generate_storage_dead(&self) -> Result<Statement> {
        let local = self
            .current_decls()
            .indices()
            .filter(|local| self.pt.is_place_live(local))
            .choose(&mut *self.rng.borrow_mut())
            .ok_or(SelectionError::Exhausted)?;
        Ok(Statement::StorageDead(local))
    }

    fn generate_deinit(&self) -> Result<Statement> {
        let place = PlaceSelector::for_operand()
            .into_iter_place(&self.pt)
            .choose(&mut *self.rng.borrow_mut())
            .ok_or(SelectionError::Exhausted)?;
        Ok(Statement::Deinit(place))
    }

    // fn generate_set_discriminant(&self) -> Result<Statement> {
    //     todo!()
    // }
    fn choose_statement(&mut self) {
        let choices_and_weights: Vec<(fn(&GenerationCtx) -> Result<Statement>, usize)> = vec![
            (Self::generate_assign, 5),
            (Self::generate_new_var, 1),
            // (Self::generate_deinit, 1),
            // (Self::generate_storage_live, 5),
            // (Self::generate_storage_dead, 2),
        ];

        let (choices, weights): (Vec<fn(&GenerationCtx) -> Result<Statement>>, Vec<usize>) =
            choices_and_weights.into_iter().unzip();

        let statement = self
            .make_choice_weighted(
                choices.into_iter(),
                WeightedIndex::new(weights).expect("weights are valid"),
                |f| f(self),
            )
            .expect("deadend");

        // We're generating a new var
        if matches!(statement, Statement::Nop) {
            let ty = self.tcx.choose_ty(&mut *self.rng.borrow_mut());
            self.declare_new_var(Mutability::Mut, ty);
        }

        self.post_generation(&statement);
        if !matches!(statement, Statement::Nop) {
            trace!("generated {}", statement.serialize());
        }
        self.current_bb_mut().insert_statement(statement);
    }
}

// Terminator
impl GenerationCtx {
    fn enter_bb(&mut self, bb: BasicBlock) {
        self.current_bb = bb;
    }

    fn generate_goto(&mut self) -> Result<()> {
        let bb = self.add_new_bb();

        self.current_bb_mut()
            .set_terminator(Terminator::Goto { target: bb });
        self.enter_bb(bb);
        Ok(())
    }

    // Produce count number of "decoy" BasicBlocks that will never be
    // actually taken. Return value will contain a mix of existing and new BBs
    // filled with random statements.
    fn decoy_bbs(&mut self, count: usize) -> Vec<BasicBlock> {
        debug!("picking {count} decoy bbs");
        // FIXME: -1 because we can't name the first BB, but custom_mir
        // should allow it
        // -1 to avoid the current bb
        let available = self.current_fn().basic_blocks.len().saturating_sub(2);

        let pick_from_existing = self.rng.get_mut().gen_range(0..=cmp::min(available, count));
        let new = count - pick_from_existing;
        debug!("picking {pick_from_existing} bbs and creating {new} new bbs");

        let mut picked = self
            .current_fn()
            .basic_blocks
            .indices()
            .skip(1) // avoid the unnamable first bb
            .filter(|&bb| bb != self.current_bb)
            .choose_multiple(self.rng.get_mut(), pick_from_existing);
        assert_eq!(picked.len(), pick_from_existing);

        let copies = self
            .current_fn()
            .basic_blocks
            .indices()
            .skip(1) // avoid the unnamable first bb
            .rev()
            .skip(1) // avoid the current bb
            .choose_multiple(self.rng.get_mut(), new);

        for i in 0..new {
            let new_bb = self.add_new_bb();
            if let Some(copied_bb) = copies.get(i) {
                assert!(!matches!(
                    self.current_fn().basic_blocks[*copied_bb].terminator(),
                    Terminator::Hole
                ));
                self.current_fn_mut().basic_blocks[new_bb] =
                    self.current_fn().basic_blocks[*copied_bb].clone();
            } else {
                self.current_fn_mut().basic_blocks[new_bb].set_terminator(Terminator::Return);
            }
            picked.push(new_bb);
        }

        picked
    }

    fn generate_switch_int(&mut self) -> Result<()> {
        debug!("generating a SwitchInt terminator");
        let (places, weights) = PlaceSelector::for_known_val()
            .of_tys(&[
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
                // Ty::Char,
                // Ty::Bool,
            ])
            .into_weighted(&self.pt)
            .ok_or(SelectionError::Exhausted)?;

        let (place, place_val) =
            self.make_choice_weighted(places.into_iter(), weights, |ppath| {
                let val = self
                    .pt
                    .known_val(ppath.target_index(&self.pt))
                    .expect("has_value");
                Ok((ppath.to_place(&self.pt), val.clone()))
            })?;

        let decoy_count = self.rng.get_mut().gen_range(1..=MAX_SWITCH_TARGETS);
        let mut targets = self.decoy_bbs(decoy_count);
        let otherwise = targets.pop().unwrap();

        let target_bb = self.add_new_bb();
        targets.push(target_bb);
        let target_discr = match place_val {
            Literal::Uint(i, _) => i,
            Literal::Int(i, _) => i as u128,
            // Literal::Bool(b) => b as u128,
            // Literal::Char(c) => c as u128,
            _ => unreachable!("invalid switchint discriminant"),
        };

        let branches: Vec<(u128, BasicBlock)> = targets
            .iter()
            .enumerate()
            .filter_map(|(i, &bb)| {
                if bb == target_bb {
                    Some((target_discr, bb))
                } else if i as u128 == target_discr {
                    // Prevent duplicate
                    None
                } else {
                    Some((i as u128, bb))
                }
            })
            .collect();

        let term = Terminator::SwitchInt {
            discr: Operand::Copy(place),
            targets: SwitchTargets {
                branches,
                otherwise,
            },
        };

        self.current_bb_mut().set_terminator(term);
        self.enter_bb(target_bb);

        Ok(())
    }

    fn generate_call(&mut self) -> Result<()> {
        debug!(
            "generating a Call terminator to {} {}",
            self.current_function.identifier(),
            self.current_bb.identifier()
        );
        let (return_places, weights) = PlaceSelector::for_lhs()
            .into_weighted(&self.pt)
            .ok_or(SelectionError::Exhausted)?;

        let return_place =
            self.make_choice_weighted(return_places.into_iter(), weights, |ppath| {
                Result::Ok(ppath.to_place(&self.pt))
            })?;

        let args_count: i32 = self.rng.get_mut().gen_range(2..=16);
        let args: Vec<Operand> = (0..args_count)
            .map(|_| {
                let (places, weights) = PlaceSelector::for_argument()
                    .except(&return_place)
                    .into_weighted(&self.pt)
                    .ok_or(SelectionError::Exhausted)?;
                self.make_choice_weighted(places.into_iter(), weights, |ppath| {
                    let ty = &ppath.target_node(&self.pt).ty;
                    if self.tcx.is_copy(&ty) {
                        Ok(Operand::Copy(ppath.to_place(&self.pt)))
                    } else {
                        Ok(Operand::Move(ppath.to_place(&self.pt)))
                    }
                })
            })
            .collect::<Result<Vec<Operand>>>()?;

        let target_bb = self.add_new_bb();
        self.return_stack.push((self.current_function, target_bb));

        let public = self.rng.get_mut().gen_bool(0.5);

        // We don't know the name of the new function here, so we save the current cursor and write the terminator after frame switch
        let (caller_fn, caller_bb) = (self.current_function, self.current_bb);
        // TODO: randomise privacy
        let new_fn = self.enter_new_fn(&args, &return_place, public);
        self.program.functions[caller_fn].basic_blocks[caller_bb].set_terminator(
            Terminator::Call {
                callee: Callee::Generated(new_fn),
                destination: return_place,
                target: target_bb,
                args,
            },
        );

        debug!("generated a Call terminator");
        Ok(())
    }

    fn generate_intrinsic_call(&mut self) -> Result<()> {
        let (return_places, weights) = PlaceSelector::for_lhs()
            .into_weighted(&self.pt)
            .ok_or(SelectionError::Exhausted)?;

        let return_place =
            self.make_choice_weighted(return_places.into_iter(), weights, |ppath| {
                Result::Ok(ppath.to_place(&self.pt))
            })?;

        let (callee, args) = self.choose_intrinsic(&return_place)?;

        self.pt.assign_literal(&return_place, None);

        if let Callee::Intrinsic(n) = callee && n == ArithOffset.name() {
            let Operand::Copy(ptr) = &args[0] else {
                unreachable!("first operand is pointer");
            };

            let lit = match &args[1] {
                Operand::Copy(p) | Operand::Move(p) =>  self.pt.known_val(p).expect("has known value"),
                Operand::Constant(lit) => lit,
            };

            let Literal::Int(offset, IntTy::Isize) = lit else {
                panic!("incorrect offset type");
            };
            let offset = *offset as isize;

            self.pt.copy_place(&return_place, ptr);
            self.pt.offset_ptr(&return_place, offset);
        }

        let bb = self.add_new_bb();
        self.current_bb_mut().set_terminator(Terminator::Call {
            callee,
            destination: return_place,
            target: bb,
            args,
        });
        self.enter_bb(bb);
        Ok(())
    }

    fn generate_return(&mut self) -> Result<bool> {
        debug!(
            "generating a Return terminator to {} {}",
            self.current_function.identifier(),
            self.current_bb.identifier()
        );
        if !self.pt.is_place_init(Place::RETURN_SLOT) {
            return Err(SelectionError::Exhausted);
        }

        self.current_bb_mut().set_terminator(Terminator::Return);
        Ok(self.exit_fn())
    }

    /// Terminates the current BB, and moves the generation context to the new BB
    fn choose_terminator(&mut self) -> bool {
        assert!(matches!(self.current_bb().terminator(), Terminator::Hole));
        if self.pt.is_place_init(Place::RETURN_SLOT) {
            if Place::RETURN_SLOT.dataflow(&self.pt) > 10
                || self.current_fn().basic_blocks.len() >= 32
            {
                return self.generate_return().unwrap();
            }
        }

        let choices_and_weights: Vec<(fn(&mut GenerationCtx) -> Result<()>, usize)> = vec![
            (Self::generate_goto, 50),
            (Self::generate_switch_int, 50),
            (Self::generate_intrinsic_call, 50),
            (
                Self::generate_call,
                MAX_FN_COUNT.saturating_sub(self.program.functions.len()),
            ),
        ];
        let (choices, weights): (Vec<fn(&mut GenerationCtx) -> Result<()>>, Vec<usize>) =
            choices_and_weights.into_iter().unzip();

        let weights = WeightedIndex::new(weights).expect("weights are valid");
        self.make_choice_weighted_mut(choices.into_iter(), weights, |ctx, f| f(ctx))
            .expect("deadend");
        true
    }
}

// Frame controls
impl GenerationCtx {
    // Move generation context to an executed function
    fn enter_new_fn(&mut self, args: &[Operand], return_dest: &Place, public: bool) -> Function {
        let args_ty: Vec<Ty> = args
            .iter()
            .map(|arg| arg.ty(self.current_decls()))
            .collect::<Vec<_>>();
        let return_ty = return_dest.ty(self.current_decls());
        let mut body = Body::new(&args_ty, return_ty.clone(), public);

        let starting_bb = body.new_basic_block(BasicBlockData::new());
        let new_fn = self.program.push_fn(body);

        debug!(
            "entering {}({}) -> {}",
            new_fn.identifier(),
            args_ty.as_slice().serialize(),
            return_ty.serialize(),
        );

        self.current_function = new_fn;
        self.current_bb = starting_bb;

        self.pt.enter_fn(
            &self.program.functions[self.current_function],
            args,
            return_dest,
        );
        new_fn
    }

    fn enter_fn0(&mut self, args_ty: &[Ty], return_ty: Ty, args: &[Literal]) {
        self.program.set_entry_args(&args);
        let mut body = Body::new(args_ty, return_ty, true);

        let starting_bb = body.new_basic_block(BasicBlockData::new());
        let new_fn = self.program.push_fn(body);
        self.current_function = new_fn;
        self.current_bb = starting_bb;

        self.pt
            .enter_fn0(&self.program.functions[self.current_function]);
    }

    fn exit_fn(&mut self) -> bool {
        let callee = self.current_function;
        if let Some((func, target)) = self.return_stack.pop() {
            debug!("leaving {} to {}", callee.identifier(), func.identifier());

            // Move cursor to the target bb in the call terminator
            self.current_function = func;
            self.current_bb = target;
            self.pt.exit_fn();
            true
        } else {
            // Returning back to main from fn0, stop generation
            false
        }
    }
}

impl GenerationCtx {
    pub fn make_choice_weighted<T, F, R>(
        &self,
        choices: impl Iterator<Item = T> + Clone,
        mut weights: WeightedIndex<Weight>,
        mut use_choice: F,
    ) -> Result<R>
    where
        F: FnMut(T) -> Result<R>,
        T: Clone,
    {
        loop {
            let i = weights.sample(&mut *self.rng.borrow_mut());
            let choice = choices.clone().nth(i).expect("choices not empty");
            let res = use_choice(choice.clone());
            match res {
                Ok(val) => return Ok(val),
                Err(_) => {
                    weights.update_weights(&[(i, &0)]).map_err(|err| {
                        assert_eq!(err, WeightedError::AllWeightsZero);
                        SelectionError::Exhausted
                    })?;
                }
            }
        }
    }

    fn make_choice_weighted_mut<T, F, R>(
        &mut self,
        choices: impl Iterator<Item = T> + Clone,
        mut weights: WeightedIndex<Weight>,
        mut use_choice: F,
    ) -> Result<R>
    where
        F: FnMut(&mut Self, T) -> Result<R>,
        T: Clone,
    {
        loop {
            let i = weights.sample(&mut *self.rng.borrow_mut());
            let choice = choices.clone().nth(i).expect("choices not empty");
            let res = use_choice(self, choice.clone());
            match res {
                Ok(val) => return Ok(val),
                Err(_) => {
                    weights.update_weights(&[(i, &0)]).map_err(|err| {
                        assert_eq!(err, WeightedError::AllWeightsZero);
                        SelectionError::Exhausted
                    })?;
                }
            }
        }
    }

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
        choices: impl Iterator<Item = T> + Clone,
        mut use_choice: F,
    ) -> Result<R>
    where
        F: FnMut(&mut Self, T) -> Result<R>,
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
            let res = use_choice(self, choice.clone());
            match res {
                Ok(val) => return Ok(val),
                Err(_) => {
                    failed.push(i);
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
            return_stack: vec![],
            current_function: Function::new(0),
            current_bb: BasicBlock::new(0),
        }
    }

    fn add_new_bb(&mut self) -> BasicBlock {
        let new_bb = self.current_fn_mut().new_basic_block(BasicBlockData::new());
        debug!(
            "adding {} to {}",
            new_bb.identifier(),
            self.current_function.identifier()
        );
        if self.current_function.index() == 1 && new_bb.index() == 5 {
            debug!("what");
        }
        new_bb
    }

    pub fn current_fn(&self) -> &Body {
        &self.program.functions[self.current_function]
    }

    pub fn current_fn_mut(&mut self) -> &mut Body {
        &mut self.program.functions[self.current_function]
    }

    pub fn current_bb(&mut self) -> &BasicBlockData {
        &self.program.functions[self.current_function].basic_blocks[self.current_bb]
    }

    pub fn current_bb_mut(&mut self) -> &mut BasicBlockData {
        &mut self.program.functions[self.current_function].basic_blocks[self.current_bb]
    }

    pub fn current_decls(&self) -> &LocalDecls {
        &self.current_fn().local_decls
    }

    pub fn generate(mut self) -> Program {
        let args_count = self.rng.get_mut().gen_range(2..=16);
        let arg_tys: Vec<Ty> = self
            .tcx
            .iter()
            .filter(|ty| <dyn RngCore>::is_literalble(*ty))
            .cloned()
            .choose_multiple(&mut *self.rng.borrow_mut(), args_count);
        let arg_literals: Vec<Literal> = arg_tys
            .iter()
            .map(|ty| {
                self.rng
                    .borrow_mut()
                    .gen_literal(ty)
                    .expect("ty is literable")
            })
            .collect();

        let return_ty = self
            .tcx
            .choose_ty_filtered(&mut *self.rng.borrow_mut(), |ty| {
                !ty.contains(|ty| matches!(ty, Ty::RawPtr(..)))
            });
        self.enter_fn0(&arg_tys, return_ty, &arg_literals);

        loop {
            let statement_count = self.rng.get_mut().gen_range(1..=BB_MAX_LEN);
            debug!("Generating a bb with {statement_count} statements");
            for _ in 0..statement_count {
                self.choose_statement();
            }
            if !self.choose_terminator() {
                break;
            }
        }

        self.program
    }

    fn post_generation(&mut self, stmt: &Statement) {
        match stmt {
            Statement::Assign(lhs, rvalue) => {
                self.pt.mark_place_init(lhs);
                match rvalue {
                    Rvalue::Use(Operand::Copy(rhs) | Operand::Move(rhs)) => {
                        self.pt.copy_place(lhs, rhs)
                    }
                    Rvalue::Use(Operand::Constant(lit)) => {
                        self.pt.assign_literal(lhs, Some(lit.clone()))
                    }
                    Rvalue::BinaryOp(BinOp::Offset, _, _) => todo!(),
                    Rvalue::AddressOf(_, referent) => self.pt.set_ref(lhs, referent),
                    _ => {
                        self.pt.combine_dataflow(lhs, rvalue);
                        self.pt.assign_literal(lhs, None)
                    }
                }
                // FIXME: move logic
            }
            Statement::StorageLive(local) => {
                self.pt
                    .allocate_local(*local, self.current_decls()[*local].ty.clone());
            }
            Statement::StorageDead(local) => self.pt.deallocate_local(*local),
            Statement::Deinit(place) => self.pt.mark_place_uninit(place),
            Statement::SetDiscriminant(_, _) => todo!(),
            Statement::Nop => {}
            Statement::Retag(_) => todo!(),
        }
    }
}
