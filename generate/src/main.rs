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

use std::time::Instant;

use clap::{arg, command, value_parser};
use log::{debug, info};
use mir::{serialize::Serialize, VarDumper};

use crate::generation::GenerationCtx;

fn main() {
    env_logger::init();
    let matches = command!()
        .args(&[
            arg!(-d --debug "generate a program where values are printed instead of hashed (slow)"),
            arg!(-p --printf_debug "generate a program where values are printed using the C 'printf' function instead of hashed (slow)"),
            arg!(<seed> "generation seed").value_parser(value_parser!(u64)),
        ])
        .get_matches();

    let seed: u64 = *matches
        .get_one::<u64>("seed")
        .expect("need an integer as seed");
    let debug_dump = matches.get_one::<bool>("debug").copied().unwrap_or(false);
    let printf_dump = matches.get_one::<bool>("printf_debug").copied().unwrap_or(false);
    let dumper = match (debug_dump,printf_dump){
        (false,false)=>VarDumper::HashDumper,
        (true,false)=>VarDumper::StdVarDumper,
        (false,true)=>VarDumper::PrintfVarDumper,
        (true,true)=>panic!("You can only choose either the `debug` dumper or `printf_debug` dumper, but both of them have been selected."),
    };
    info!("Generating a program with seed {seed}");
    let genctxt = GenerationCtx::new(seed, dumper);
    let time = Instant::now();
    let (program, tcx) = genctxt.generate();
    println!("{}", program.serialize(&tcx));
    println!("{}", tcx.serialize(dumper));
    let dur = time.elapsed();
    debug!("took {}s to generate", dur.as_secs_f32());
}
