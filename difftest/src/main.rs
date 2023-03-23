#![feature(iter_intersperse)]

use core::panic;
use std::{collections::HashMap, path::PathBuf, str::FromStr};

use clap::{Arg, Command};
use config::Config;
use difftest::{
    backend::{Backend, Cranelift, Miri, OptLevel, LLVM},
    run_diff_test, BackendName,
};
use log::{debug, error, info};

fn main() {
    env_logger::init();

    let matches = Command::new("difftest")
        .arg(Arg::new("file").required(true))
        .get_matches();
    let source = matches.get_one::<String>("file").expect("required");
    let source = PathBuf::from_str(source).expect("source is a valid path");

    // Initialise backends
    // TODO: extract this out into a function
    let settings = Config::builder()
        .add_source(config::File::with_name("config.toml"))
        .add_source(config::Environment::default())
        .build()
        .unwrap();

    let mut backends: HashMap<BackendName, Box<dyn Backend>> = HashMap::default();
    if let Ok(clif_dir) = settings.get_string("cranelift_dir") {
        let clif = Cranelift::from_repo(clif_dir, OptLevel::Optimised);
        match clif {
            Ok(clif) => backends.insert("cranelift", Box::new(clif)),
            Err(e) => panic!("cranelift init failed\n{}", e.0),
        };
    }

    if let Ok(miri_dir) = settings.get_string("miri_dir") {
        let miri = Miri::from_repo(miri_dir);
        match miri {
            Ok(miri) => backends.insert("miri", Box::new(miri)),
            Err(e) => panic!("miri init failed\n{}", e.0),
        };
    }

    let llvm_toolchain = settings.get_string("llvm_toolchain").ok();
    backends.insert("llvm", Box::new(LLVM::new(OptLevel::Optimised, llvm_toolchain)));

    info!(
        "Difftesting {} with {}",
        source.as_os_str().to_string_lossy(),
        backends
            .keys()
            .copied()
            .intersperse(", ")
            .collect::<String>()
    );
    let results = run_diff_test(&source, backends);
    if results.all_same() && results.all_success() {
        info!("{} is all the same", source.as_os_str().to_string_lossy());
        debug!("{}", results);
    } else {
        error!(
            "{} didn't pass:\n{}",
            source.as_os_str().to_string_lossy(),
            results
        );
    }
}
