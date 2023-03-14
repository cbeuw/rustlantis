#![feature(byte_slice_trim_ascii)]
#![feature(iter_intersperse)]

use core::panic;
use std::{collections::HashMap, path::PathBuf, str::FromStr};

use clap::{Arg, Command};
use config::Config;
use difftest::{
    backend::{Backend, Cranelift, Miri, LLVM},
    run_diff_test,
};
use log::{info, error};

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

    let mut backends: HashMap<&'static str, Box<dyn Backend>> = HashMap::default();
    if let Ok(clif_dir) = settings.get_string("cranelift_dir") {
        let clif = Cranelift::from_repo(clif_dir);
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

    backends.insert("llvm", Box::new(LLVM {}));

    info!(
        "Difftesting {} with {}",
        source.as_os_str().to_string_lossy(),
        backends
            .keys()
            .copied()
            .intersperse(", ")
            .collect::<String>()
    );
    let results = run_diff_test(&source, &backends);
    if results.len() == 1 {
        info!("{} is all the same", source.as_os_str().to_string_lossy());
    } else {
        error!("{} didn't pass: {:?}", source.as_os_str().to_string_lossy(), results);
    }
}
