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
mod mem;
mod place_select;
mod ptable;
mod ty;

use std::env::args;

use log::info;
use mir::serialize::Serialize;

use crate::generation::GenerationCtx;

fn main() {
    env_logger::init();

    let seed: u64 = args().nth(1).unwrap().parse().unwrap();
    info!("Generating a program with seed {seed}");
    let genctxt = GenerationCtx::new(seed);
    let program = genctxt.generate();
    println!("{}", program.serialize());
}
