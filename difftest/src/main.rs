#![feature(byte_slice_trim_ascii)]

mod backend;

use core::panic;
use std::{collections::HashMap, path::PathBuf, str::FromStr, vec};

use backend::{Backend, Cranelift, ExecResult, Miri, LLVM};
use clap::{Arg, Command};
use config::Config;
use log::info;

fn compare_exec_results(results: &HashMap<&'static str, ExecResult>) {
    //TODO: optimisation here to check if all results are equal directly, since most should be

    // Split execution results into equivalent classes
    let mut eq_classes: Vec<(ExecResult, Vec<&str>)> = vec![];

    'outer: for (name, result) in results {
        for (class_result, names) in &mut eq_classes {
            // Put into an existing equivalence class
            if result == class_result {
                names.push(name);
                continue 'outer;
            }
        }

        // No equal execution result, make a new class
        eq_classes.push((result.clone(), vec![name]));
    }

    if eq_classes.len() == 1 {
        info!("all agree");
    }

    for (class_result, names) in eq_classes {
        println!("{}: {:?}", names.join(", "), class_result);
    }
}

fn main() {
    env_logger::init();

    let matches = Command::new("difftest")
        .arg(Arg::new("file").required(true))
        .get_matches();
    let source = matches.get_one::<String>("file").expect("required");
    let source = PathBuf::from_str(source).expect("source is a valid path");

    let settings = Config::builder()
        .add_source(config::File::with_name("config.toml"))
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

    let mut exec_results: HashMap<&'static str, ExecResult> = HashMap::default();

    for (name, b) in backends {
        let result = b.execute(&source);
        exec_results.insert(name, result);
    }

    compare_exec_results(&exec_results);
}
