use mir::{syntax::*, serialize::Serialize};

fn main() {
    let mut body = Body::new(&vec![Ty::Bool], Ty::Bool);
    let statements = vec![Statement::Assign(
        Place::RETURN_SLOT,
        Rvalue::UnaryOp(
            UnOp::Not,
            Operand::Copy(Place {
                local: body.args_iter().next().unwrap(),
            }),
        ),
    )];
    let terminator = Some(Terminator::Return);
    body.new_basic_block(BasicBlockData {
        statements,
        terminator,
    });
    let mut program = Program::new();
    program.push_fn(body);

    println!("{}", program.serialize());
}
