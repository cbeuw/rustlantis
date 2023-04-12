#![feature(is_sorted)]
#![feature(exact_size_is_empty)]
#![feature(iter_advance_by)]
#![feature(variant_count)]
#![feature(test)]
#![feature(let_chains)]
#![feature(try_blocks)]
#![feature(box_patterns)]

mod generation;
mod literal;
mod place_select;
mod ptable;
mod ty;
mod mem;

use std::env::args;

use crate::generation::GenerationCtx;
use log::info;
use mir::serialize::Serialize;

fn main() {
    env_logger::init();

    // let mut body = Body::new(&vec![Ty::Bool], Ty::Bool);
    // let statements = vec![Statement::Assign(
    //     Place::RETURN_SLOT,
    //     Rvalue::UnaryOp(
    //         UnOp::Not,
    //         Operand::Copy(Place {
    //             local: body.args_iter().next().unwrap(),
    //         }),
    //     ),
    // )];
    // let terminator = Some(Terminator::Return);
    // body.new_basic_block(BasicBlockData {
    //     statements,
    //     terminator,
    // });
    // let mut program = Program::new();
    // program.push_fn(body);

    // println!("{}", program.serialize());

    // let mut rng = SmallRng::seed_from_u64(0);
    // let skeleton = build_skeleton(&mut rng);
    // let dot = Dot::new(&skeleton);
    // println!("{dot:?}");

    let seed: u64 = args().nth(1).unwrap().parse().unwrap();
    info!("Generating a program with seed {seed}");
    let genctxt = GenerationCtx::new(seed);
    let program = genctxt.generate();
    println!("{}", program.serialize());
}
