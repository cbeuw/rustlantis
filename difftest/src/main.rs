#![feature(iter_intersperse)]

use core::panic;
use std::{
    collections::HashMap,
    io::{self, Read},
    path::PathBuf,
    process::ExitCode,
    str::FromStr,
};

use clap::{Arg, Command};
use config::Config;
use difftest::{
    backends::{Backend, Cranelift, Miri, OptLevel, GCC, LLVM},
    run_diff_test, BackendName, Source,
};
use log::{debug, error, info};

fn main() -> ExitCode {
    env_logger::init();

    let matches = Command::new("difftest")
        .arg(Arg::new("file").required(true))
        .get_matches();
    let source = matches.get_one::<String>("file").expect("required");

    // Initialise backends
    // TODO: extract this out into a function
    let settings = Config::builder()
        .add_source(config::File::with_name("config.toml").required(false))
        .add_source(config::Environment::default())
        .build()
        .unwrap();

    let mut backends: HashMap<BackendName, Box<dyn Backend>> = HashMap::default();
    if let Ok(clif_dir) = settings.get_string("cranelift_dir") {
        let clif = Cranelift::from_repo(clif_dir, OptLevel::Optimised, OptLevel::Unoptimised)
            .expect("cranelift init failed");
        backends.insert("cranelift-opt-only", Box::new(clif));
    } else if let Ok(clif_toolchain) = settings.get_string("cranelift_toolchain") {
        let clif =
            Cranelift::from_rustup(&clif_toolchain, OptLevel::Optimised, OptLevel::Unoptimised)
                .expect("cranelift init failed");
        backends.insert("cranelift-opt-only", Box::new(clif));
    }

    let check_ub = settings
        .get_string("miri_check_ub")
        .map(|config| config == "true" || config == "1")
        .unwrap_or(true);
    if let Ok(miri_dir) = settings.get_string("miri_dir") {
        let miri = Miri::from_repo(miri_dir, check_ub).expect("miri init failed");
        if check_ub {
            backends.insert("miri-checked", Box::new(miri));
        } else {
            backends.insert("miri-unchecked", Box::new(miri));
        }
    } else if let Ok(miri_toolchain) = settings.get_string("miri_toolchain") {
        let miri = Miri::from_rustup(&miri_toolchain, check_ub).expect("miri init failed");
        if check_ub {
            backends.insert("miri-checked", Box::new(miri));
        } else {
            backends.insert("miri-unchecked", Box::new(miri));
        }
    }

    if let Ok(cg_gcc) = settings.get_string("cg_gcc_dir") {
        let cg_gcc = GCC::from_built_repo(cg_gcc, OptLevel::Optimised, OptLevel::Optimised);
        match cg_gcc {
            Ok(cg_gcc) => backends.insert("cg_gcc", Box::new(cg_gcc)),
            Err(e) => panic!("rustc_codegen_gcc init failed\n{}", e.0),
        };
    }

    let llvm_toolchain = settings.get_string("llvm_toolchain").ok();
    backends.insert(
        "llvm-opt",
        Box::new(LLVM::new(
            llvm_toolchain.clone(),
            OptLevel::Optimised,
            OptLevel::Optimised,
        )),
    );

    backends.insert(
        "llvm-opt-only",
        Box::new(LLVM::new(
            llvm_toolchain,
            OptLevel::Optimised,
            OptLevel::Unoptimised,
        )),
    );

    let source = if source == "-" {
        let mut code = String::new();
        io::stdin()
            .read_to_string(&mut code)
            .expect("can read source code from stdin");
        Source::Stdin(code)
    } else {
        Source::File(PathBuf::from_str(source).expect("is valid path"))
    };

    info!(
        "Difftesting {} with {}",
        source,
        backends
            .keys()
            .copied()
            .intersperse(", ")
            .collect::<String>()
    );

    let results = run_diff_test(&source, backends);
    if results.all_same() && results.all_success() {
        info!("{} is all the same", source);
        debug!("{}", results);
        ExitCode::SUCCESS
    } else {
        let results = results.to_string();
        error!("{} didn't pass:\n{results}", source,);
        ExitCode::FAILURE
    }
}
