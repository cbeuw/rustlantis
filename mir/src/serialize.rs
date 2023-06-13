use crate::{syntax::*, tyctxt::TyCtxt};

pub trait Serialize {
    fn serialize(&self, tcx: &TyCtxt) -> String;
}

impl Serialize for TyId {
    fn serialize(&self, tcx: &TyCtxt) -> String {
        match self.kind(tcx) {
            &TyKind::Unit => "()".to_owned(),
            &TyKind::Bool => "bool".to_owned(),
            &TyKind::Char => "char".to_owned(),
            &TyKind::ISIZE => "isize".to_owned(),
            &TyKind::I8 => "i8".to_owned(),
            &TyKind::I16 => "i16".to_owned(),
            &TyKind::I32 => "i32".to_owned(),
            &TyKind::I64 => "i64".to_owned(),
            &TyKind::I128 => "i128".to_owned(),
            &TyKind::USIZE => "usize".to_owned(),
            &TyKind::U8 => "u8".to_owned(),
            &TyKind::U16 => "u16".to_owned(),
            &TyKind::U32 => "u32".to_owned(),
            &TyKind::U64 => "u64".to_owned(),
            &TyKind::U128 => "u128".to_owned(),
            &TyKind::F32 => "f32".to_owned(),
            &TyKind::F64 => "f64".to_owned(),
            // Pointer types
            TyKind::RawPtr(ty, mutability) => {
                format!("{}{}", mutability.ptr_prefix_str(), ty.serialize(tcx))
            }
            // Sequence types
            TyKind::Tuple(elems) => {
                if elems.len() == 1 {
                    format!("({},)", elems[0].serialize(tcx))
                } else {
                    format!("({})", elems.as_slice().serialize(tcx))
                }
            }
            TyKind::Array(ty, len) => {
                format!("[{}; {len}]", ty.serialize(tcx))
            }
            // User-defined type
            TyKind::Adt(_) => {
                self.type_name()
            },
        }
    }
}

impl Serialize for &[TyId] {
    fn serialize(&self, tcx: &TyCtxt) -> String {
        self.iter()
            .map(|ty| ty.serialize(tcx))
            .intersperse(", ".to_string())
            .collect()
    }
}

impl Serialize for Place {
    fn serialize(&self, _: &TyCtxt) -> String {
        let str = self.local().identifier();
        self.projection().iter().fold(str, |acc, proj| match proj {
            ProjectionElem::Deref => format!("(*{acc})"),
            ProjectionElem::TupleField(id) => format!("{acc}.{}", id.index()),
            ProjectionElem::Field(id) => format!("{acc}.{}", id.identifier()),
            ProjectionElem::Index(local) => format!("{acc}[{}]", local.identifier()),
            ProjectionElem::Downcast(..) => todo!(),
            ProjectionElem::ConstantIndex { offset } => format!("{acc}[{offset}]"),
        })
    }
}

impl Serialize for Literal {
    fn serialize(&self, tcx: &TyCtxt) -> String {
        match self {
            Literal::Uint(i, _) => format!("{i}_{}", self.ty(tcx).serialize(tcx)),
            Literal::Int(i, _) if *i < 0 => format!("({i}_{})", self.ty(tcx).serialize(tcx)),
            Literal::Int(i, _) => format!("{i}_{}", self.ty(tcx).serialize(tcx)),
            Literal::Float(f, _) => {
                if f.is_nan() {
                    format!("{}::NAN", self.ty(tcx).serialize(tcx))
                } else if f.is_infinite() {
                    if f.is_sign_positive() {
                        format!("{}::INFINITY", self.ty(tcx).serialize(tcx))
                    } else {
                        format!("{}::NEG_INFINITY", self.ty(tcx).serialize(tcx))
                    }
                } else if *f < 0. {
                    format!("({f}_{})", self.ty(tcx).serialize(tcx))
                } else {
                    format!("{f}_{}", self.ty(tcx).serialize(tcx))
                }
            }
            Literal::Bool(b) => b.to_string(),
            Literal::Char(c) => format!("'\\u{{{:x}}}'", u32::from(*c)),
            Literal::Tuple(elems) => match elems.len() {
                0 => "()".to_owned(),
                1 => format!("({},)", elems[0].serialize(tcx)),
                _ => format!(
                    "({})",
                    elems
                        .iter()
                        .map(|l| l.serialize(tcx))
                        .intersperse(", ".to_owned())
                        .collect::<String>()
                ),
            },
            Literal::Array(lit, len) => format!("[{}; {len}]", lit.serialize(tcx)),
        }
    }
}

impl Serialize for Operand {
    fn serialize(&self, tcx: &TyCtxt) -> String {
        match self {
            Operand::Copy(place) => place.serialize(tcx),
            Operand::Move(place) => format!("Move({})", place.serialize(tcx)),
            Operand::Constant(lit) => lit.serialize(tcx),
        }
    }
}

impl Serialize for Rvalue {
    fn serialize(&self, tcx: &TyCtxt) -> String {
        match self {
            Rvalue::Use(a) => a.serialize(tcx),
            Rvalue::UnaryOp(op, a) => format!("{}{}", op.symbol(), a.serialize(tcx)),
            Rvalue::BinaryOp(BinOp::Offset, a, b) => {
                format!("Offset({}, {})", a.serialize(tcx), b.serialize(tcx))
            }
            Rvalue::BinaryOp(op, a, b) => {
                format!("{} {} {}", a.serialize(tcx), op.symbol(), b.serialize(tcx))
            }
            Rvalue::CheckedBinaryOp(op, a, b) => format!(
                "Checked({} {} {})",
                a.serialize(tcx),
                op.symbol(),
                b.serialize(tcx)
            ),

            Rvalue::Cast(a, target) => format!("{} as {}", a.serialize(tcx), target.serialize(tcx)),
            Rvalue::Len(place) => format!("Len({})", place.serialize(tcx)),
            Rvalue::Discriminant(place) => format!("Discriminant({})", place.serialize(tcx)),
            Rvalue::AddressOf(Mutability::Not, place) => {
                format!("core::ptr::addr_of!({})", place.serialize(tcx))
            }
            Rvalue::AddressOf(Mutability::Mut, place) => {
                format!("core::ptr::addr_of_mut!({})", place.serialize(tcx))
            }
        }
    }
}

impl Serialize for Statement {
    fn serialize(&self, tcx: &TyCtxt) -> String {
        match self {
            Statement::Assign(place, rvalue) => {
                format!("{} = {}", place.serialize(tcx), rvalue.serialize(tcx))
            }
            Statement::StorageLive(local) => format!("StorageLive({})", local.identifier()),
            Statement::StorageDead(local) => format!("StorageDead({})", local.identifier()),
            Statement::Deinit(local) => format!("Deinit({})", local.serialize(tcx)),
            Statement::SetDiscriminant(place, discr) => {
                format!("SetDiscriminant({}, {discr})", place.serialize(tcx))
            }
            Statement::Retag(place) => format!("Retag({})", place.serialize(tcx)),
            Statement::Nop => String::default(),
        }
    }
}

impl Serialize for Terminator {
    fn serialize(&self, tcx: &TyCtxt) -> String {
        match self {
            Terminator::Return => "Return()".to_owned(),
            Terminator::Goto { target } => format!("Goto({})", target.identifier()),
            Terminator::Unreachable => "Unreachable()".to_owned(),
            Terminator::Drop { place, target } => {
                format!("Drop({}, {})", place.serialize(tcx), target.identifier())
            }
            Terminator::Call {
                destination,
                target,
                callee,
                args,
            } => {
                let args_list: String = args
                    .iter()
                    .map(|arg| arg.serialize(tcx))
                    .intersperse(", ".to_owned())
                    .collect();
                let fn_name = match callee {
                    Callee::Generated(func) => func.identifier(),
                    Callee::Named(func) => func.to_string(),
                    Callee::Intrinsic(func) => format!("core::intrinsics::{func}"),
                };
                format!(
                    "Call({}, {}, {fn_name}({args_list}))",
                    destination.serialize(tcx),
                    target.identifier(),
                )
            }
            Terminator::SwitchInt { discr, targets } => {
                let arms = targets.match_arms();
                format!("match {} {{\n{}\n}}", discr.serialize(tcx), arms)
            }
            Terminator::Hole => unreachable!("hole"),
        }
    }
}

impl Serialize for BasicBlockData {
    fn serialize(&self, tcx: &TyCtxt) -> String {
        let mut stmts: String = self
            .statements
            .iter()
            .filter(|stmt| !matches!(stmt, Statement::Nop))
            .map(|stmt| format!("{};\n", stmt.serialize(tcx)))
            .collect();
        stmts.push_str(&self.terminator.serialize(tcx));
        stmts
    }
}

impl Serialize for VariantDef {
    fn serialize(&self, tcx: &TyCtxt) -> String {
        self.fields
            .iter_enumerated()
            .map(|(id, ty)| format!("{}: {},\n", id.identifier(), ty.serialize(tcx)))
            .collect()
    }
}

impl Serialize for Body {
    fn serialize(&self, tcx: &TyCtxt) -> String {
        // Return type annotation
        let mut body: String = format!("type RET = {};\n", self.return_ty().serialize(tcx));
        // Declarations
        body.extend(self.vars_iter().map(|idx| {
            let decl = &self.local_decls[idx];
            format!("let {}: {};\n", idx.identifier(), decl.ty.serialize(tcx))
        }));
        let mut bbs = self.basic_blocks.iter_enumerated();
        // First bb
        body.push_str(&format!(
            "{{\n{}\n}}\n",
            bbs.next()
                .expect("body contains at least one bb")
                .1
                .serialize(tcx)
        ));
        // Other bbs
        body.extend(
            bbs.map(|(idx, bb)| format!("{} = {{\n{}\n}}\n", idx.identifier(), bb.serialize(tcx))),
        );
        format!("mir! {{\n{body}\n}}")
    }
}

impl Serialize for Program {
    fn serialize(&self, tcx: &TyCtxt) -> String {
        let mut program = Program::HEADER.to_string();
        if self.use_debug_dumper {
            program += Program::DEBUG_DUMPER;
        } else {
            program += Program::DUMPER;
        }
        program.extend(self.functions.iter_enumerated().map(|(idx, body)| {
            let args_list: String = body
                .args_iter()
                .map(|arg| {
                    let decl = &body.local_decls[arg];
                    format!(
                        "{}{}: {}",
                        decl.mutability.prefix_str(),
                        arg.identifier(),
                        decl.ty.serialize(tcx)
                    )
                })
                .intersperse(",".to_string())
                .collect();
            format!(
                "{}\n{}fn {}({}) -> {} {{\n{}\n}}\n",
                Program::FUNCTION_ATTRIBUTE,
                if body.public { "pub " } else { "" },
                idx.identifier(),
                args_list,
                body.return_ty().serialize(tcx),
                body.serialize(tcx)
            )
        }));
        let arg_list: String = self
            .entry_args
            .iter()
            .map(|arg| format!("std::hint::black_box({})", arg.serialize(tcx)))
            .intersperse(", ".to_string())
            .collect();

        let first_fn: String = self
            .functions
            .indices()
            .next()
            .expect("program has functions")
            .identifier();

        let hash_printer = if self.use_debug_dumper {
            ""
        } else {
            r#"
                unsafe {
                    println!("hash: {}", H.finish());
                }
            "#
        };

        program.push_str(&format!(
            "pub fn main() {{
                println!(\"{{:?}}\", {first_fn}({arg_list}));
                {hash_printer}
            }}"
        ));
        program
    }
}

#[cfg(test)]
mod tests {
    use crate::{syntax::*, tyctxt::TyCtxt};

    use super::Serialize;

    #[test]
    fn serialize_body() {
        let mut body = Body::new(&[TyCtxt::BOOL], TyCtxt::BOOL, true);
        let statements = vec![Statement::Assign(
            Place::RETURN_SLOT,
            Rvalue::UnaryOp(UnOp::Not, Operand::Copy(Place::from_local(Local::new(1)))),
        )];
        body.new_basic_block(BasicBlockData {
            statements,
            terminator: Terminator::Return,
        });
    }

    #[test]
    fn serialize_literal() {
        let tcx = TyCtxt::from_primitives();
        let nan = Literal::Float(f32::NAN as f64, FloatTy::F32);
        assert_eq!(nan.serialize(&tcx), "f32::NAN");

        let inf = Literal::Float(f32::INFINITY as f64, FloatTy::F32);
        assert_eq!(inf.serialize(&tcx), "f32::INFINITY");
    }
}
