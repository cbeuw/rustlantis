mod intrinsics;

use std::cell::RefCell;
use std::rc::Rc;
use std::{cmp, fmt, vec};

use index_vec::IndexVec;
use log::trace;
use mir::serialize::Serialize;
use mir::syntax::{
    AggregateKind, BasicBlock, BasicBlockData, BinOp, Body, Callee, Function, IntTy, Literal,
    Local, LocalDecls, Mutability, Operand, Place, Program, ProjectionElem, Rvalue, Statement,
    SwitchTargets, Terminator, TyId, TyKind, UnOp, VariantIdx,
};
use mir::tyctxt::TyCtxt;
use rand::seq::SliceRandom;
use rand::{seq::IteratorRandom, Rng, RngCore, SeedableRng};
use rand_distr::{Distribution, WeightedError, WeightedIndex};

use crate::literal::GenLiteral;
use crate::place_select::{PlaceSelector, Weight};
use crate::ptable::{HasDataflow, PlaceIndex, PlaceOperand, PlaceTable, ToPlaceIndex};
use crate::ty::{seed_tys, TySelect};

use self::intrinsics::{ArithOffset, Transmute};
use crate::generation::intrinsics::CoreIntrinsic;

/// Max. number of statements & declarations in a bb
const BB_MAX_LEN: usize = 32;
/// Max. number of switch targets in a SwitchInt terminator
const MAX_SWITCH_TARGETS: usize = 8;
const MAX_BB_COUNT: usize = 15;
const MAX_FN_COUNT: usize = 20;
const VAR_DUMP_CHANCE: f32 = 0.5;

#[derive(Debug)]
pub enum SelectionError {
    Exhausted,
}

type Result<Node> = std::result::Result<Node, SelectionError>;

#[derive(Clone, Copy)]
struct Cursor {
    function: Function,
    basic_block: BasicBlock,
}

impl fmt::Debug for Cursor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!(
            "{}:{}",
            self.function.identifier(),
            self.basic_block.identifier(),
        ))
    }
}

pub struct GenerationCtx {
    rng: RefCell<Box<dyn RngCore>>,
    program: Program,
    tcx: Rc<TyCtxt>,
    ty_weights: TySelect,
    pt: PlaceTable,
    return_stack: Vec<Cursor>,
    cursor: Cursor,
}

// Operand
impl GenerationCtx {
    fn choose_operand(&self, tys: &[TyId], excluded: &Place) -> Result<Operand> {
        let operand: Result<Operand> = try {
            let (ppath, weights) = PlaceSelector::for_operand(self.tcx.clone())
                .except(excluded)
                .of_tys(tys)
                .into_weighted(&self.pt)
                .ok_or(SelectionError::Exhausted)?;
            self.make_choice_weighted(ppath.into_iter(), weights, |ppath| {
                if ppath.target_node(&self.pt).ty.is_copy(&self.tcx) {
                    Ok(Operand::Copy(ppath.to_place(&self.pt)))
                } else {
                    Ok(Operand::Move(ppath.to_place(&self.pt)))
                }
            })?
        };
        operand.or_else(|_| {
            let literalble: Vec<TyId> = tys
                .iter()
                .filter(|ty| <dyn RngCore>::is_literalble(**ty, &self.tcx))
                .copied()
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
                    .gen_literal(*selected, &self.tcx)
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
            lhs.serialize(&self.tcx),
            lhs.ty(self.current_decls(), &self.tcx).serialize(&self.tcx)
        );
        let operand = self.choose_operand(&[lhs.ty(self.current_decls(), &self.tcx)], lhs)?;
        Ok(Rvalue::Use(operand))
    }

    fn generate_unary_op(&self, lhs: &Place) -> Result<Rvalue> {
        use TyKind::*;
        use UnOp::*;
        let lhs_ty = lhs.ty(self.current_decls(), &self.tcx);
        let unops = match lhs_ty.kind(&self.tcx) {
            Int(_) => &[Neg, Not][..],
            Float(_) => &[Neg][..],
            Uint(_) | Bool => &[Not][..],
            _ => &[][..],
        };
        let rvalue = self.make_choice(unops.iter(), |unop| {
            let operand = self.choose_operand(&[lhs_ty], lhs)?;
            Ok(Rvalue::UnaryOp(*unop, operand))
        })?;
        Ok(rvalue)
    }

    fn generate_binary_op(&self, lhs: &Place) -> Result<Rvalue> {
        use BinOp::*;
        use TyKind::*;
        let lhs_ty = lhs.ty(self.current_decls(), &self.tcx);
        let binops = match lhs_ty.kind(&self.tcx) {
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
                    let l = self.choose_operand(&[lhs_ty], lhs)?;
                    let r = Operand::Constant(self.rng.borrow_mut().gen_literal_non_zero(lhs_ty, &self.tcx).expect("can generate literal"));
                    (l, r)
                }
                Add | Sub | Mul | BitXor | BitAnd | BitOr => {
                    // Both operand same type as lhs
                    let l = self.choose_operand(&[lhs_ty], lhs)?;
                    let r = self.choose_operand(&[lhs_ty], lhs)?;
                    // As the types are all integers or floats which are Copy, Move/Copy
                    // probably doesn't make much difference
                    (l, r)
                }
                Shl | Shr => {
                    // left operand same type as lhs, right can be uint or int
                    let l = self.choose_operand(&[lhs_ty], lhs)?;
                    // TODO: use a compile time concat
                    let r = self.choose_operand(
                        &[
                            TyCtxt::ISIZE,
                            TyCtxt::I8,
                            TyCtxt::I16,
                            TyCtxt::I32,
                            TyCtxt::I64,
                            TyCtxt::I128,
                            TyCtxt::USIZE,
                            TyCtxt::U8,
                            TyCtxt::U16,
                            TyCtxt::U32,
                            TyCtxt::U64,
                            TyCtxt::U128,
                        ],
                        lhs,
                    )?;
                    (l, r)
                }
                Eq | Ne | Lt | Le | Ge | Gt => {
                    // neither left or right operand needs to be the sme type as lhs
                    let tys = [
                        TyCtxt::BOOL,
                        TyCtxt::CHAR,
                        TyCtxt::ISIZE,
                        TyCtxt::I8,
                        TyCtxt::I16,
                        TyCtxt::I32,
                        TyCtxt::I64,
                        TyCtxt::I128,
                        TyCtxt::USIZE,
                        TyCtxt::U8,
                        TyCtxt::U16,
                        TyCtxt::U32,
                        TyCtxt::U64,
                        TyCtxt::U128,
                        TyCtxt::F32,
                        TyCtxt::F64,
                    ];
                    let l = self.choose_operand(&tys, lhs)?;
                    let r = self.choose_operand(&[l.ty(self.current_decls(), &self.tcx)], lhs)?;
                    (l, r)
                }
                Offset => {
                    let TyKind::RawPtr(_, lhs_mutability) = lhs_ty.kind(&self.tcx) else {
                        unreachable!("lhs is a ptr");
                    };
                    let tys: Vec<TyId> = self
                        .tcx
                        .iter_enumerated()
                        .filter_map(|(ty, kind)| matches!(kind, TyKind::RawPtr(_, mutability) if *mutability == *lhs_mutability).then_some(ty))
                        .collect();
                    let l = self.choose_operand(&tys, lhs)?;
                    let r = self.choose_operand(&[TyCtxt::ISIZE], lhs)?;
                    (l, r)
                }
            };
            Ok(Rvalue::BinaryOp(*binop, l, r))
        })?;
        Ok(rvalue)
    }

    fn generate_checked_binary_op(&self, lhs: &Place) -> Result<Rvalue> {
        use BinOp::*;
        use TyKind::*;
        let lhs_ty = lhs.ty(self.current_decls(), &self.tcx);

        if let Some([ret, TyCtxt::BOOL]) = lhs_ty.tuple_elems(&self.tcx) {
            let bin_ops = match ret.kind(&self.tcx) {
                Uint(_) | Int(_) => &[Add, Sub, Mul][..],
                _ => &[][..],
            };
            let rvalue = self.make_choice(bin_ops.iter(), |bin_op| {
                let (l, r) = match *bin_op {
                    Add | Sub | Mul => {
                        // Both operand same type as lhs
                        let l = self.choose_operand(&[*ret], lhs)?;
                        let r = self.choose_operand(&[*ret], lhs)?;
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
        let target_ty = lhs.ty(self.current_decls(), &self.tcx);
        let source_tys = match target_ty.kind(&self.tcx) {
            // TODO: no int to ptr cast for now
            TyKind::Int(..) | TyKind::Uint(..) => &[
                TyCtxt::ISIZE,
                TyCtxt::I8,
                TyCtxt::I16,
                TyCtxt::I32,
                TyCtxt::I64,
                TyCtxt::I128,
                TyCtxt::USIZE,
                TyCtxt::U8,
                TyCtxt::U16,
                TyCtxt::U32,
                TyCtxt::U64,
                TyCtxt::U128,
                TyCtxt::F32,
                TyCtxt::F64,
                TyCtxt::CHAR,
                TyCtxt::BOOL,
            ][..],
            TyKind::Float(..) => &[
                TyCtxt::ISIZE,
                TyCtxt::I8,
                TyCtxt::I16,
                TyCtxt::I32,
                TyCtxt::I64,
                TyCtxt::I128,
                TyCtxt::USIZE,
                TyCtxt::U8,
                TyCtxt::U16,
                TyCtxt::U32,
                TyCtxt::U64,
                TyCtxt::U128,
                TyCtxt::F32,
                TyCtxt::F64,
            ][..],
            _ => &[][..],
        };
        let rvalue = self.make_choice(
            // XXX: remove the filter once https://github.com/rust-lang/rust/pull/109160 is merged
            source_tys.iter().filter(|ty| **ty != target_ty),
            |source_ty| {
                let source = self.choose_operand(&[*source_ty], lhs)?;
                Ok(Rvalue::Cast(source, target_ty))
            },
        )?;
        Ok(rvalue)
    }

    fn generate_address_of(&self, lhs: &Place) -> Result<Rvalue> {
        let target_ty = lhs.ty(self.current_decls(), &self.tcx);
        let (source_ty, mutability) = match target_ty.kind(&self.tcx) {
            TyKind::RawPtr(ty, mutability) => (ty, mutability),
            _ => return Err(SelectionError::Exhausted),
        };
        let (candidates, weights) = PlaceSelector::for_pointee(self.tcx.clone())
            .of_ty(*source_ty)
            .except(lhs)
            .into_weighted(&self.pt)
            .ok_or(SelectionError::Exhausted)?;
        self.make_choice_weighted(candidates.into_iter(), weights, |ppath| {
            Ok(Rvalue::AddressOf(*mutability, ppath.to_place(&self.pt)))
        })
    }

    fn generate_aggregate(&self, lhs: &Place) -> Result<Rvalue> {
        let target_ty = lhs.ty(self.current_decls(), &self.tcx);
        let agg = match target_ty.kind(&self.tcx) {
            TyKind::Tuple(tys) => {
                let ops: Vec<Operand> = tys
                    .iter()
                    .map(|ty| self.choose_operand(&[*ty], lhs))
                    .collect::<Result<Vec<Operand>>>()?;
                Rvalue::Aggregate(AggregateKind::Tuple, IndexVec::from_vec(ops))
            }
            TyKind::Array(ty, len) => {
                let ops: Vec<Operand> = (0..*len)
                    .map(|_| self.choose_operand(&[*ty], lhs))
                    .collect::<Result<Vec<Operand>>>()?;
                Rvalue::Aggregate(AggregateKind::Array(*ty), IndexVec::from_vec(ops))
            }
            TyKind::Adt(adt) => {
                if adt.is_enum() {
                    todo!()
                } else {
                    let fields = &adt.variants.first().unwrap().fields;
                    let mut agg = IndexVec::new();
                    for (fid, ty) in fields.iter_enumerated() {
                        let op = self.choose_operand(&[*ty], lhs)?;
                        let new_fid = agg.push(op);
                        assert_eq!(fid, new_fid);
                    }
                    Rvalue::Aggregate(AggregateKind::Adt(target_ty, VariantIdx::new(0)), agg)
                }
            }
            TyKind::Unit => Rvalue::Aggregate(AggregateKind::Tuple, IndexVec::new()),
            _ => return Err(SelectionError::Exhausted),
        };
        Ok(agg)
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
            (Self::generate_aggregate, 2),
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
        let (lhs_choices, weights) = PlaceSelector::for_lhs(self.tcx.clone())
            .into_weighted(&self.pt)
            .ok_or(SelectionError::Exhausted)?;

        self.make_choice_weighted(lhs_choices.into_iter(), weights, |ppath| {
            let lhs = ppath.to_place(&self.pt);
            trace!(
                "generating an assignment statement with lhs {}: {}",
                lhs.serialize(&self.tcx),
                lhs.ty(self.current_decls(), &self.tcx).serialize(&self.tcx)
            );

            let statement = Statement::Assign(lhs.clone(), self.generate_rvalue(&lhs)?);
            Ok(statement)
        })
    }

    // Hack to take &self
    fn generate_new_var(&self) -> Result<Statement> {
        Ok(Statement::Nop)
    }

    fn declare_new_var(&mut self, mutability: Mutability, ty: TyId) -> Local {
        let local = self.current_fn_mut().declare_new_var(mutability, ty);
        trace!(
            "generated new var {}: {}",
            local.identifier(),
            ty.serialize(&self.tcx)
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
        let place = PlaceSelector::for_operand(self.tcx.clone())
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
            let ty = self
                .ty_weights
                .choose_ty(&mut *self.rng.borrow_mut(), &self.tcx);
            self.declare_new_var(Mutability::Mut, ty);
        }

        self.post_generation(&statement);
        if !matches!(statement, Statement::Nop) {
            trace!("generated {}", statement.serialize(&self.tcx));
        }
        self.current_bb_mut().insert_statement(statement);
    }
}

// Terminator
impl GenerationCtx {
    fn enter_bb(&mut self, bb: BasicBlock) {
        self.cursor.basic_block = bb;
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
        // FIXME: -1 because we can't name the first BB, but custom_mir
        // should allow it
        // -1 to avoid the current bb
        let available = self.current_fn().basic_blocks.len().saturating_sub(2);

        let pick_from_existing = self.rng.get_mut().gen_range(0..=cmp::min(available, count));
        let new = count - pick_from_existing;

        let mut picked = self
            .current_fn()
            .basic_blocks
            .indices()
            .skip(1) // avoid the unnamable first bb
            .filter(|&bb| bb != self.cursor.basic_block)
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
        trace!("generating a SwitchInt terminator");
        let (places, weights) = PlaceSelector::for_known_val(self.tcx.clone())
            .of_tys(&[
                TyCtxt::ISIZE,
                TyCtxt::I8,
                TyCtxt::I16,
                TyCtxt::I32,
                TyCtxt::I64,
                TyCtxt::I128,
                TyCtxt::USIZE,
                TyCtxt::U8,
                TyCtxt::U16,
                TyCtxt::U32,
                TyCtxt::U64,
                TyCtxt::U128,
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
                Ok((ppath.to_place(&self.pt), *val))
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
        trace!("generating a Call terminator to {:?}", self.cursor);
        let (return_places, weights) = PlaceSelector::for_lhs(self.tcx.clone())
            .into_weighted(&self.pt)
            .ok_or(SelectionError::Exhausted)?;

        let return_place =
            self.make_choice_weighted(return_places.into_iter(), weights, |ppath| {
                Result::Ok(ppath.to_place(&self.pt))
            })?;

        let args_count: i32 = self.rng.get_mut().gen_range(2..=16);
        let mut selector = PlaceSelector::for_argument(self.tcx.clone()).except(&return_place);
        let mut args = vec![];
        for _ in 0..args_count {
            let (places, weights) = selector
                .clone()
                .into_weighted(&self.pt)
                .ok_or(SelectionError::Exhausted)?;
            let arg = self.make_choice_weighted(places.into_iter(), weights, |ppath| {
                let ty = &ppath.target_node(&self.pt).ty;
                let place = ppath.to_place(&self.pt);
                if ty.is_copy(&self.tcx) {
                    Ok(Operand::Copy(place))
                } else {
                    selector = selector.clone().except(&place);
                    Ok(Operand::Move(place))
                }
            })?;
            args.push(arg);
        }

        let target_bb = self.add_new_bb();
        self.return_stack.push(Cursor {
            function: self.cursor.function,
            basic_block: target_bb,
        });

        let public = self.rng.get_mut().gen_bool(0.5);

        // We don't know the name of the new function here, so we save the current cursor and write the terminator after frame switch
        let caller_cursor = self.cursor;
        let new_fn = self.enter_new_fn(&args, &return_place, public);
        self.program.functions[caller_cursor.function].basic_blocks[caller_cursor.basic_block]
            .set_terminator(Terminator::Call {
                callee: Callee::Generated(new_fn),
                destination: return_place,
                target: target_bb,
                args,
            });

        trace!("generated a Call terminator");
        Ok(())
    }

    fn generate_intrinsic_call(&mut self) -> Result<()> {
        let (return_places, weights) = PlaceSelector::for_lhs(self.tcx.clone())
            .into_weighted(&self.pt)
            .ok_or(SelectionError::Exhausted)?;

        let return_place =
            self.make_choice_weighted(return_places.into_iter(), weights, |ppath| {
                Result::Ok(ppath.to_place(&self.pt))
            })?;

        let (callee, args) = self.choose_intrinsic(&return_place)?;

        // Post generation value manipulation
        let ret = return_place.to_place_index(&self.pt).expect("place exists");
        let arg_places: Vec<PlaceOperand> = args
            .iter()
            .map(|op| PlaceOperand::from_operand(op, &self.pt))
            .collect();

        self.pt.mark_place_init(ret);
        let Callee::Intrinsic(intrinsic_name) = callee else {
            panic!("callee is intrinsic");
        };

        if intrinsic_name == ArithOffset.name() {
            let PlaceOperand::Copy(ptr) = arg_places[0] else {
                unreachable!("first operand is pointer");
            };

            let lit = match arg_places[1] {
                PlaceOperand::Copy(p) | PlaceOperand::Move(p) => {
                    *self.pt.known_val(p).expect("has known value")
                }
                PlaceOperand::Constant(lit) => lit,
            };

            let Literal::Int(offset, IntTy::Isize) = lit else {
                panic!("incorrect offset type");
            };
            let offset = offset as isize;

            self.pt.copy_place(ret, ptr);
            self.pt.offset_ptr(ret, offset);
        } else if intrinsic_name == Transmute.name() {
            if let PlaceOperand::Copy(src) | PlaceOperand::Move(src) = arg_places[0] {
                self.pt.transmute_place(ret, src)
            }
        }

        for op in arg_places {
            if let PlaceOperand::Move(p) = op {
                self.pt.mark_place_moved(p);
            }
        }

        self.pt.assign_literal(ret, None);
        // Finish post generation manipulation

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
        trace!("generating a Return terminator to {:?}", self.cursor);
        if !self.pt.is_place_init(Place::RETURN_SLOT) {
            return Err(SelectionError::Exhausted);
        }

        self.insert_dump_var_gadget();

        self.current_bb_mut().set_terminator(Terminator::Return);
        Ok(self.exit_fn())
    }

    /// Terminates the current BB, and moves the generation context to the new BB
    fn choose_terminator(&mut self) -> bool {
        assert!(matches!(self.current_bb().terminator(), Terminator::Hole));
        if self.pt.is_place_init(Place::RETURN_SLOT) {
            if Place::RETURN_SLOT.dataflow(&self.pt) > 10
                || self.current_fn().basic_blocks.len() >= MAX_BB_COUNT
            {
                return self.generate_return().unwrap();
            }
        }

        let choices_and_weights: Vec<(fn(&mut GenerationCtx) -> Result<()>, usize)> = vec![
            (Self::generate_goto, 20),
            (Self::generate_switch_int, 20),
            (Self::generate_intrinsic_call, 20),
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

    fn insert_dump_var_gadget(&mut self) {
        let unit = self.declare_new_var(Mutability::Not, TyCtxt::UNIT);
        let unit2 = self.declare_new_var(Mutability::Not, TyCtxt::UNIT);

        let dumpable: Vec<Local> = self
            .current_fn()
            .args_decl_iter()
            .chain(self.current_fn().vars_decl_iter())
            .filter_map(|(local, decl)| {
                (decl.ty.hashable(&self.tcx) && self.pt.is_place_init(local)).then_some(local)
            })
            .collect();
        let dump_count = (dumpable.len() as f32 * VAR_DUMP_CHANCE) as usize;
        // TODO: weight this?
        let dumpped: Vec<Local> = dumpable
            .choose_multiple(self.rng.get_mut(), dump_count)
            .copied()
            .collect();

        let new_bb = self.add_new_bb();
        self.current_bb_mut()
            .set_terminator(Terminator::Goto { target: new_bb });
        self.enter_bb(new_bb);

        for vars in dumpped.chunks(Program::DUMPER_ARITY) {
            let new_bb = self.add_new_bb();

            let args = if self.program.use_debug_dumper {
                let mut args = Vec::with_capacity(1 + Program::DUMPER_ARITY * 2);
                args.push(Operand::Constant(
                    self.cursor.function.index().try_into().unwrap(),
                ));
                for var in vars {
                    args.push(Operand::Constant(var.index().try_into().unwrap()));
                    args.push(Operand::Move(Place::from_local(*var)));
                }

                while args.len() < 1 + Program::DUMPER_ARITY * 2 {
                    args.push(Operand::Constant(unit2.index().try_into().unwrap()));
                    args.push(Operand::Copy(Place::from_local(unit2)));
                }
                args
            } else {
                let mut args = Vec::with_capacity(Program::DUMPER_ARITY);
                for var in vars {
                    args.push(Operand::Move(Place::from_local(*var)));
                }

                while args.len() < Program::DUMPER_ARITY {
                    args.push(Operand::Copy(Place::from_local(unit2)));
                }
                args
            };
            self.current_bb_mut().set_terminator(Terminator::Call {
                callee: Program::DUMPER_CALL,
                destination: Place::from_local(unit),
                target: new_bb,
                args,
            });
            self.enter_bb(new_bb);
        }
    }
}

// Frame controls
impl GenerationCtx {
    // Move generation context to an executed function
    fn enter_new_fn(&mut self, args: &[Operand], return_dest: &Place, public: bool) -> Function {
        let args_ty: Vec<TyId> = args
            .iter()
            .map(|arg| arg.ty(self.current_decls(), &self.tcx))
            .collect::<Vec<_>>();
        let return_ty = return_dest.ty(self.current_decls(), &self.tcx);
        let mut body = Body::new(&args_ty, return_ty, public);

        let starting_bb = body.new_basic_block(BasicBlockData::new());
        let new_fn = self.program.push_fn(body);

        trace!(
            "entering {}({}) -> {}",
            new_fn.identifier(),
            args_ty.as_slice().serialize(&self.tcx),
            return_ty.serialize(&self.tcx),
        );

        self.cursor = Cursor {
            function: new_fn,
            basic_block: starting_bb,
        };

        self.pt.enter_fn(
            &self.program.functions[self.cursor.function],
            args,
            return_dest,
        );
        new_fn
    }

    fn enter_fn0(&mut self, args_ty: &[TyId], return_ty: TyId, args: &[Literal]) {
        self.program.set_entry_args(args);
        let mut body = Body::new(args_ty, return_ty, true);

        let starting_bb = body.new_basic_block(BasicBlockData::new());
        let new_fn = self.program.push_fn(body);

        trace!(
            "entering {}({}) -> {}",
            new_fn.identifier(),
            args_ty.serialize(&self.tcx),
            return_ty.serialize(&self.tcx),
        );

        self.cursor = Cursor {
            function: new_fn,
            basic_block: starting_bb,
        };

        self.pt
            .enter_fn0(&self.program.functions[self.cursor.function]);
    }

    fn exit_fn(&mut self) -> bool {
        let callee = self.cursor;
        if let Some(return_dest) = self.return_stack.pop() {
            trace!("leaving {:?} to {:?}", callee, return_dest);

            // Move cursor to the target bb in the call terminator
            self.cursor = return_dest;
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

    pub fn new(seed: u64, debug_dump: bool) -> Self {
        let rng = RefCell::new(Box::new(rand::rngs::SmallRng::seed_from_u64(seed)));
        let tcx = Rc::new(seed_tys(&mut *rng.borrow_mut()));
        let ty_weights = TySelect::new(&tcx);
        // TODO: don't zero-initialize current_function and current_bb
        Self {
            rng,
            tcx: tcx.clone(),
            ty_weights,
            program: Program::new(debug_dump),
            pt: PlaceTable::new(tcx),
            return_stack: vec![],
            cursor: Cursor {
                function: Function::new(0),
                basic_block: BasicBlock::new(0),
            },
        }
    }

    fn add_new_bb(&mut self) -> BasicBlock {
        let new_bb = self.current_fn_mut().new_basic_block(BasicBlockData::new());
        trace!(
            "adding {} to {}",
            new_bb.identifier(),
            self.cursor.function.identifier()
        );
        new_bb
    }

    pub fn current_fn(&self) -> &Body {
        &self.program.functions[self.cursor.function]
    }

    pub fn current_fn_mut(&mut self) -> &mut Body {
        &mut self.program.functions[self.cursor.function]
    }

    pub fn current_bb(&mut self) -> &BasicBlockData {
        &self.program.functions[self.cursor.function].basic_blocks[self.cursor.basic_block]
    }

    pub fn current_bb_mut(&mut self) -> &mut BasicBlockData {
        &mut self.program.functions[self.cursor.function].basic_blocks[self.cursor.basic_block]
    }

    pub fn current_decls(&self) -> &LocalDecls {
        &self.current_fn().local_decls
    }

    pub fn generate(mut self) -> (Program, TyCtxt) {
        let args_count = self.rng.get_mut().gen_range(2..=16);
        let arg_tys: Vec<TyId> = self
            .tcx
            .indices()
            .filter(|ty| <dyn RngCore>::is_literalble(*ty, &self.tcx))
            .choose_multiple(&mut *self.rng.borrow_mut(), args_count);
        let arg_literals: Vec<Literal> = arg_tys
            .iter()
            .map(|ty| {
                self.rng
                    .borrow_mut()
                    .gen_literal(*ty, &self.tcx)
                    .expect("ty is literable")
            })
            .collect();

        let return_ty = self.ty_weights.choose_ty(&mut *self.rng.borrow_mut(), &self.tcx);
        self.enter_fn0(&arg_tys, return_ty, &arg_literals);

        loop {
            let statement_count = self.rng.get_mut().gen_range(1..=BB_MAX_LEN);
            trace!("Generating a bb with {statement_count} statements");
            for _ in 0..statement_count {
                self.choose_statement();
            }
            if !self.choose_terminator() {
                break;
            }
        }

        drop(self.pt);

        (self.program, Rc::into_inner(self.tcx).unwrap())
    }

    fn post_generation(&mut self, stmt: &Statement) {
        // We must evaluate the places first before updating any PlaceTable state,
        // as the updates may affect projections
        let mut actions: Vec<Box<dyn FnOnce(&mut PlaceTable)>> = vec![];
        {
            match stmt {
                Statement::Assign(lhs, rvalue) => {
                    let lhs = lhs.to_place_index(&self.pt).unwrap();
                    actions.push(Box::new(move |pt| {
                        pt.mark_place_init(lhs);
                    }));
                    match rvalue {
                        Rvalue::AddressOf(_, referent) => {
                            let referent = referent.to_place_index(&self.pt).unwrap();
                            actions.push(Box::new(move |pt| {
                                pt.set_ref(lhs, referent);
                            }));
                        }
                        _ => {
                            let new_df = rvalue.dataflow(&self.pt);
                            actions.push(Box::new(move |pt| {
                                pt.update_dataflow(lhs, new_df);
                            }));
                        }
                    }
                }
                Statement::StorageLive(local) => {
                    let local = *local;
                    let ty = self.current_decls()[local].ty;
                    actions.push(Box::new(move |pt| {
                        pt.allocate_local(local, ty);
                    }));
                }
                Statement::StorageDead(local) => {
                    let local = *local;
                    actions.push(Box::new(move |pt| pt.deallocate_local(local)));
                }
                Statement::Deinit(place) => {
                    let place = place.to_place_index(&self.pt).unwrap();
                    actions.push(Box::new(move |pt| pt.mark_place_uninit(place)));
                }
                Statement::SetDiscriminant(_, _) => todo!(),
                Statement::Nop => {}
                Statement::Retag(_) => todo!(),
            }
        }
        // Copies & literals
        // One of copy, literal assignment or literal deletion must happen
        if let Statement::Assign(lhs, rvalue) = stmt {
            let lhs = lhs.to_place_index(&self.pt).unwrap();
            match rvalue {
                Rvalue::Use(op) => match op {
                    Operand::Copy(rhs) | Operand::Move(rhs) => {
                        let rhs = rhs.to_place_index(&self.pt).unwrap();
                        actions.push(Box::new(move |pt| {
                            pt.copy_place(lhs, rhs);
                        }));
                    }
                    Operand::Constant(lit) => {
                        actions.push(Box::new(move |pt| {
                            pt.assign_literal(lhs, Some(*lit));
                        }));
                    }
                },
                agg @ Rvalue::Aggregate(..) => {
                    for (target, op) in self.aggregate_places(lhs, agg) {
                        match op {
                            Operand::Copy(rhs) | Operand::Move(rhs) => {
                                let rhs = rhs.to_place_index(&self.pt).unwrap();
                                actions.push(Box::new(move |pt| {
                                    pt.copy_place(target, rhs);
                                }));
                            }
                            Operand::Constant(lit) => {
                                actions.push(Box::new(move |pt| {
                                    pt.assign_literal(target, Some(*lit));
                                }));
                            }
                        }
                    }
                }
                _ => actions.push(Box::new(move |pt| {
                    pt.assign_literal(lhs, None);
                })),
            }
        }
        // Moves
        if let Statement::Assign(lhs, rvalue) = stmt {
            match rvalue {
                Rvalue::Use(Operand::Move(o))
                | Rvalue::UnaryOp(_, Operand::Move(o))
                | Rvalue::BinaryOp(_, Operand::Move(o), _)
                | Rvalue::BinaryOp(_, _, Operand::Move(o))
                | Rvalue::Cast(Operand::Move(o), _)
                | Rvalue::CheckedBinaryOp(_, Operand::Move(o), _)
                | Rvalue::CheckedBinaryOp(_, _, Operand::Move(o)) => {
                    let pidx = o.to_place_index(&self.pt).unwrap();
                    actions.push(Box::new(move |pt| {
                        pt.mark_place_moved(pidx);
                    }));
                }
                agg @ Rvalue::Aggregate(..) => {
                    // FIXME: we don't actually need projections from lhs here
                    let lhs = lhs.to_place_index(&self.pt).unwrap();
                    for (_, op) in self.aggregate_places(lhs, agg) {
                        if let Operand::Move(o) = op {
                            let pidx = o.to_place_index(&self.pt).unwrap();
                            actions.push(Box::new(move |pt| {
                                pt.mark_place_moved(pidx);
                            }));
                        }
                    }
                }
                _ => {}
            }
        }
        for action in actions {
            action(&mut self.pt);
        }
    }

    fn aggregate_places<'a>(
        &self,
        root: PlaceIndex,
        agg: &'a Rvalue,
    ) -> Vec<(PlaceIndex, &'a Operand)> {
        let Rvalue::Aggregate(kind, vals) = agg else {
            panic!("not an aggregate")
        };

        vals.iter_enumerated()
            .map(|(fid, operand)| {
                let proj_elem = match kind {
                    AggregateKind::Array(..) => ProjectionElem::ConstantIndex {
                        offset: fid.index() as u64,
                    },
                    AggregateKind::Tuple => ProjectionElem::TupleField(fid),
                    AggregateKind::Adt(ty, _) => {
                        let TyKind::Adt(adt) = ty.kind(&self.tcx) else {
                        panic!("not an adt")
                    };
                        if adt.is_enum() {
                            todo!()
                        } else {
                            ProjectionElem::Field(fid)
                        }
                    }
                };
                let projected = self.pt.project_from_node(root, proj_elem).unwrap();

                (projected, operand)
            })
            .collect()
    }
}
