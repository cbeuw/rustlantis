use crate::{syntax::*, vec::Idx};

pub trait Serialize {
    fn serialize(&self) -> String;
}

impl Serialize for Place {
    fn serialize(&self) -> String {
        self.local.identifier()
    }
}

impl Serialize for Operand {
    fn serialize(&self) -> String {
        match self {
            Operand::Copy(place) => place.serialize(),
            Operand::Move(place) => format!("Move({})", place.serialize()),
        }
    }
}

impl Serialize for Rvalue {
    fn serialize(&self) -> String {
        match self {
            Rvalue::UnaryOp(op, a) => format!("{}{}", op.symbol(), a.serialize()),
            Rvalue::BinaryOp(op, a, b) => match op {
                BinOp::Offset => format!("{}.offset({})", a.serialize(), b.serialize()),
                _ => format!("{} {} {}", a.serialize(), op.symbol(), b.serialize()),
            },
            Rvalue::CheckedBinaryOp(op, a, b) => match op {
                BinOp::Offset => format!("Checked({}.offset({}))", a.serialize(), b.serialize()),
                _ => format!(
                    "Checked({} {} {})",
                    a.serialize(),
                    op.symbol(),
                    b.serialize()
                ),
            },
            Rvalue::Len(place) => format!("Len({})", place.serialize()),
            Rvalue::Retag(place) => format!("Retag({})", place.serialize()),
            Rvalue::Discriminant(place) => format!("Discriminant({})", place.serialize()),
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
            Terminator::DropAndReplace {
                place,
                value,
                target,
            } => format!(
                "DropAndReplace({}, {}, {})",
                place.serialize(),
                value.serialize(),
                target.identifier()
            ),
            // Terminator::Call {
            //     destination,
            //     target,
            //     func,
            //     args,
            // } => {
            //     let args_list: String = args
            //         .iter()
            //         .map(|arg| arg.serialize())
            //         .intersperse(", ".to_owned())
            //         .collect();
            //     format!(
            //         "Call({}, {}, {}({})",
            //         destination.serialize(),
            //         target.identifier(),
            //         func.serialize(),
            //         args_list
            //     )
            // }
            Terminator::SwitchInt { discr, targets } => {
                let arms = targets.match_arms();
                format!("match {} {{\n{}\n}}", discr.serialize(), arms)
            }
        }
    }
}

impl Serialize for BasicBlockData {
    fn serialize(&self) -> String {
        let mut stmts: String = self
            .statements
            .iter()
            .map(|stmt| format!("{};\n", stmt.serialize()))
            .collect();
        if let Some(term) = &self.terminator {
            stmts.push_str(&term.serialize());
        }
        stmts
    }
}

impl Serialize for Body {
    fn serialize(&self) -> String {
        let mut body: String = self
            .vars_iter()
            .map(|idx| {
                let decl = &self.local_decls[idx];
                format!(
                    "let {}_{}: {};\n",
                    &decl.mutability.prefix_str(),
                    idx.index(),
                    decl.ty.name()
                )
            })
            .collect();
        let mut bbs = self.basic_blocks.iter_enumerated();
        body.push_str(&format!(
            "{{\n{}\n}}",
            bbs.next()
                .expect("body contains at least one bb")
                .1
                .serialize()
        ));
        let rest =
            bbs.map(|(idx, bb)| format!("{} = {{\n{}\n}}", idx.identifier(), bb.serialize()));
        body.extend(rest);
        format!("mir! {{\n{body}\n}}")
    }
}

impl Serialize for Program {
    fn serialize(&self) -> String {
        let mut program = Program::HEADER.to_string();
        program.extend(self.functions.iter_enumerated().map(|(idx, body)| {
            format!("{}\nfn {}({}) -> {} {{\n{}\n}}\n", Program::FUNCTION_ATTRIBUTE, idx.identifier(), body.args_list(), body.return_ty().name(), body.serialize())
        }));
        program.push_str(Program::MAIN);
        program
    }
}

#[cfg(test)]
mod tests {
    use crate::{syntax::*, vec::Idx};

    #[test]
    fn serialize_body() {
        let mut body = Body::new(&vec![Ty::Bool], Ty::Bool);
        let statements = vec![Statement::Assign(
            Place::RETURN_SLOT,
            Rvalue::UnaryOp(
                UnOp::Not,
                Operand::Copy(Place {
                    local: Local::new(1),
                }),
            ),
        )];
        let terminator = Some(Terminator::Return);
        body.new_basic_block(BasicBlockData {
            statements,
            terminator,
        });
    }
}
