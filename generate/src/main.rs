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
mod pgraph;
mod place_select;
mod ty;
use mir::VarDumper;
use std::time::Instant;

use clap::{arg, command, value_parser, Arg};
use log::{debug, info};

use crate::generation::GenerationCtx;

fn main() {
    env_logger::init();
    let matches = command!()
        .args(&[
            arg!(-d --debug "generate a program where values are printed instead of hashed (slow)"),

            arg!(-p --printf_debug "generate a program where values are printed using the C 'printf' function instead of hashed (slow)"),
            arg!(--rust_gpu "generate a program where values are printed using the C 'printf' function instead of hashed (slow)"),
            arg!(--no_enums "generate a program without enums"),
            arg!(--no_128_bit_ints "generate a program without 128 bit ints"),
            
            Arg::new("call-syntax")
                .long("call-syntax")
                .value_parser(["v1", "v2", "v3", "v4"])
                .default_value("v4")
                .help("switch between different versions of Call syntaxes"),

            arg!(<seed> "generation seed").value_parser(value_parser!(u64)),
        ])
        .get_matches();

    let seed: u64 = *matches
        .get_one::<u64>("seed")
        .expect("need an integer as seed");
    let debug_dump = matches.get_one::<bool>("debug").copied().unwrap_or(false);
    let rust_gpu = matches
        .get_one::<bool>("rust_gpu")
        .copied()
        .unwrap_or(false);
    let no_enums = matches
        .get_one::<bool>("no_enums")
        .copied()
        .unwrap_or(false);
    let no_128_bit_ints  = matches
    .get_one::<bool>("no_128_bit_ints")
    .copied()
    .unwrap_or(false);
    let printf_dump = matches
        .get_one::<bool>("printf_debug")
        .copied()
        .unwrap_or(false)
        | rust_gpu;
    let dumper = match (debug_dump,printf_dump){
        (false,false)=>VarDumper::HashDumper,
        (true,false)=>VarDumper::StdVarDumper,
        (false,true)=>VarDumper::PrintfVarDumper{rust_gpu},
        (true,true)=>panic!("You can only choose either the `debug` dumper or `printf_debug` dumper, but both of them have been selected."),
    };
    info!("Generating a program with seed {seed}");

    let call_syntax = matches.get_one::<String>("call-syntax").unwrap();
    let genctxt = GenerationCtx::new(seed, dumper, no_enums,no_128_bit_ints);
    let time = Instant::now();
    let (program, tcx) = genctxt.generate();
    println!("{}", program.serialize(&tcx, call_syntax.as_str().into()));
    println!("{}", tcx.serialize(dumper));

    let dur = time.elapsed();
    debug!("took {}s to generate", dur.as_secs_f32());
}
