use crate::syntax::*;

pub trait Serialize {
    fn serialize(&self) -> String;
}

impl Serialize for Ty {
    fn serialize(&self) -> String {
        match self {
            &Self::Unit => "()".to_owned(),
            &Self::BOOL => "bool".to_owned(),
            &Self::CHAR => "char".to_owned(),
            &Self::ISIZE => "isize".to_owned(),
            &Self::I8 => "i8".to_owned(),
            &Self::I16 => "i16".to_owned(),
            &Self::I32 => "i32".to_owned(),
            &Self::I64 => "i64".to_owned(),
            &Self::I128 => "i128".to_owned(),
            &Self::USIZE => "usize".to_owned(),
            &Self::U8 => "u8".to_owned(),
            &Self::U16 => "u16".to_owned(),
            &Self::U32 => "u32".to_owned(),
            &Self::U64 => "u64".to_owned(),
            &Self::U128 => "u128".to_owned(),
            &Self::F32 => "f32".to_owned(),
            &Self::F64 => "f64".to_owned(),
            // User-defined type
            Self::Adt(_) => todo!(),
            // Pointer types
            Self::RawPtr(ty, mutability) => {
                format!("{}{}", mutability.ptr_prefix_str(), ty.serialize())
            }
            // Sequence types
            Self::Tuple(elems) => {
                if elems.len() == 1 {
                    format!("({},)", elems[0].serialize())
                } else {
                    format!("({})", elems.as_slice().serialize())
                }
            }
            Self::Array(ty, len) => {
                format!("[{}; {len}]", ty.serialize())
            }
        }
    }
}

impl Serialize for Place {
    fn serialize(&self) -> String {
        let str = self.local().identifier();
        self.projection().iter().fold(str, |acc, proj| match proj {
            ProjectionElem::Deref => format!("(*{acc})"),
            ProjectionElem::TupleField(id) => format!("{acc}.{}", id.index()),
            ProjectionElem::Field(_) => todo!(),
            ProjectionElem::Index(local) => format!("{acc}[{}]", local.identifier()),
            ProjectionElem::Downcast(_) => todo!(),
            ProjectionElem::ConstantIndex { offset } => format!("{acc}[{offset}]"),
        })
    }
}

impl Serialize for Literal {
    fn serialize(&self) -> String {
        match self {
            Literal::Uint(i, _) => format!("{i}_{}", self.ty().serialize()),
            Literal::Int(i, _) if *i < 0 => format!("({i}_{})", self.ty().serialize()),
            Literal::Int(i, _) => format!("{i}_{}", self.ty().serialize()),
            Literal::Float(f, _) => {
                if f.is_nan() {
                    format!("{}::NAN", self.ty().serialize())
                } else if f.is_infinite() {
                    if f.is_sign_positive() {
                        format!("{}::INFINITY", self.ty().serialize())
                    } else {
                        format!("{}::NEG_INFINITY", self.ty().serialize())
                    }
                } else if *f < 0. {
                    format!("({f}_{})", self.ty().serialize())
                } else {
                    format!("{f}_{}", self.ty().serialize())
                }
            }
            Literal::Bool(b) => b.to_string(),
            Literal::Char(c) => format!("'\\u{{{:x}}}'", u32::from(*c)),
            Literal::Tuple(elems) => match elems.len() {
                0 => "()".to_owned(),
                1 => format!("({},)", elems[0].serialize()),
                _ => format!(
                    "({})",
                    elems
                        .iter()
                        .map(|l| l.serialize())
                        .intersperse(", ".to_owned())
                        .collect::<String>()
                ),
            },
            Literal::Array(lit, len) => format!("[{}; {len}]", lit.serialize()),
        }
    }
}

impl Serialize for Operand {
    fn serialize(&self) -> String {
        match self {
            Operand::Copy(place) => place.serialize(),
            Operand::Move(place) => format!("Move({})", place.serialize()),
            Operand::Constant(lit) => lit.serialize(),
        }
    }
}

impl Serialize for Rvalue {
    fn serialize(&self) -> String {
        match self {
            Rvalue::Use(a) => a.serialize(),
            Rvalue::UnaryOp(op, a) => format!("{}{}", op.symbol(), a.serialize()),
            Rvalue::BinaryOp(BinOp::Offset, a, b) => {
                format!("Offset({}, {})", a.serialize(), b.serialize())
            }
            Rvalue::BinaryOp(op, a, b) => {
                format!("{} {} {}", a.serialize(), op.symbol(), b.serialize())
            }
            Rvalue::CheckedBinaryOp(op, a, b) => format!(
                "Checked({} {} {})",
                a.serialize(),
                op.symbol(),
                b.serialize()
            ),

            Rvalue::Cast(a, target) => format!("{} as {}", a.serialize(), target.serialize()),
            Rvalue::Len(place) => format!("Len({})", place.serialize()),
            Rvalue::Discriminant(place) => format!("Discriminant({})", place.serialize()),
            Rvalue::AddressOf(Mutability::Not, place) => {
                format!("core::ptr::addr_of!({})", place.serialize())
            }
            Rvalue::AddressOf(Mutability::Mut, place) => {
                format!("core::ptr::addr_of_mut!({})", place.serialize())
            }
        }
    }
}

impl Serialize for Statement {
    fn serialize(&self) -> String {
        match self {
            Statement::Assign(place, rvalue) => {
                format!("{} = {}", place.serialize(), rvalue.serialize())
            }
            Statement::StorageLive(local) => format!("StorageLive({})", local.identifier()),
            Statement::StorageDead(local) => format!("StorageDead({})", local.identifier()),
            Statement::Deinit(local) => format!("Deinit({})", local.serialize()),
            Statement::SetDiscriminant(place, discr) => {
                format!("SetDiscriminant({}, {discr})", place.serialize())
            }
            Statement::Retag(place) => format!("Retag({})", place.serialize()),
            Statement::Nop => String::default(),
        }
    }
}

impl Serialize for Terminator {
    fn serialize(&self) -> String {
        match self {
            Terminator::Return => "Return()".to_owned(),
            Terminator::Goto { target } => format!("Goto({})", target.identifier()),
            Terminator::Unreachable => "Unreachable()".to_owned(),
            Terminator::Drop { place, target } => {
                format!("Drop({}, {})", place.serialize(), target.identifier())
            }
            Terminator::Call {
                destination,
                target,
                callee,
                args,
            } => {
                let args_list: String = args
                    .iter()
                    .map(|arg| arg.serialize())
                    .intersperse(", ".to_owned())
                    .collect();
                let fn_name = match callee {
                    Callee::Generated(func) => func.identifier(),
                    Callee::Named(func) => func.to_string(),
                    Callee::Intrinsic(func) => format!("core::intrinsics::{func}"),
                };
                format!(
                    "Call({}, {}, {fn_name}({args_list}))",
                    destination.serialize(),
                    target.identifier(),
                )
            }
            Terminator::SwitchInt { discr, targets } => {
                let arms = targets.match_arms();
                format!("match {} {{\n{}\n}}", discr.serialize(), arms)
            }
            Terminator::Hole => unreachable!("hole"),
        }
    }
}

impl Serialize for BasicBlockData {
    fn serialize(&self) -> String {
        let mut stmts: String = self
            .statements
            .iter()
            .filter(|stmt| !matches!(stmt, Statement::Nop))
            .map(|stmt| format!("{};\n", stmt.serialize()))
            .collect();
        stmts.push_str(&self.terminator.serialize());
        stmts
    }
}

impl Serialize for Body {
    fn serialize(&self) -> String {
        // Return type annotation
        let mut body: String = format!("type RET = {};\n", self.return_ty().serialize());
        // Declarations
        body.extend(self.vars_iter().map(|idx| {
            let decl = &self.local_decls[idx];
            format!("let {}: {};\n", idx.identifier(), decl.ty.serialize())
        }));
        let mut bbs = self.basic_blocks.iter_enumerated();
        // First bb
        body.push_str(&format!(
            "{{\n{}\n}}\n",
            bbs.next()
                .expect("body contains at least one bb")
                .1
                .serialize()
        ));
        // Other bbs
        body.extend(
            bbs.map(|(idx, bb)| format!("{} = {{\n{}\n}}\n", idx.identifier(), bb.serialize())),
        );
        format!("mir! {{\n{body}\n}}")
    }
}

impl Serialize for Program {
    fn serialize(&self) -> String {
        let mut program = Program::HEADER.to_string();
        if self.use_debug_dumper {
            program += Program::DEBUG_DUMPER;
        } else {
            program += Program::DUMPER;
        }
        program.extend(self.functions.iter_enumerated().map(|(idx, body)| {
            format!(
                "{}\n{}fn {}({}) -> {} {{\n{}\n}}\n",
                Program::FUNCTION_ATTRIBUTE,
                if body.public { "pub " } else { "" },
                idx.identifier(),
                body.args_list(),
                body.return_ty().serialize(),
                body.serialize()
            )
        }));
        let arg_list: String = self
            .entry_args
            .iter()
            .map(|arg| format!("std::hint::black_box({})", arg.serialize()))
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

impl Serialize for &[Ty] {
    fn serialize(&self) -> String {
        self.iter()
            .map(|ty| ty.serialize())
            .intersperse(", ".to_string())
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use crate::syntax::*;

    use super::Serialize;

    #[test]
    fn serialize_body() {
        let mut body = Body::new(&vec![Ty::BOOL], Ty::BOOL, true);
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
        let nan = Literal::Float(f32::NAN as f64, FloatTy::F32);
        assert_eq!(nan.serialize(), "f32::NAN");

        let inf = Literal::Float(f32::INFINITY as f64, FloatTy::F32);
        assert_eq!(inf.serialize(), "f32::INFINITY");
    }
}
