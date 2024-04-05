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
mod pgraph;
mod ty;

use std::time::Instant;

use clap::{arg, command, value_parser, Arg};
use log::{debug, info};

use crate::generation::GenerationCtx;

fn main() {
    env_logger::init();
    let matches = command!()
        .args(&[
            arg!(-d --debug "generate a program where values are printed instead of hashed (slow)"),
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
    info!("Generating a program with seed {seed}");
    let call_syntax = matches.get_one::<String>("call-syntax").unwrap();
    let genctxt = GenerationCtx::new(seed, debug_dump);
    let time = Instant::now();
    let (program, tcx) = genctxt.generate();
    println!("{}", program.serialize(&tcx, call_syntax.as_str().into()));
    println!("{}", tcx.serialize());
    let dur = time.elapsed();
    debug!("took {}s to generate", dur.as_secs_f32());
}
