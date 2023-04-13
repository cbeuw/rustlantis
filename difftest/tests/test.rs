#![feature(is_some_and)]

use std::{
    collections::HashMap, path::PathBuf, str::FromStr,
};

use config::Config;
use difftest::{
    backends::{Backend, Cranelift, Miri, OptLevel, LLVM},
    run_diff_test,
};

#[test]
fn correct_mir() {
    let settings = Config::builder()
        .add_source(config::File::with_name("config.toml"))
        .add_source(config::Environment::default())
        .build()
        .unwrap();

    let mut backends: HashMap<&'static str, Box<dyn Backend>> = HashMap::default();

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

    backends.insert("llvm", Box::new(LLVM::new(OptLevel::Optimised, None)));

    let results = run_diff_test(
        &PathBuf::from_str("tests/inputs/simple.rs").unwrap(),
        backends,
    );
    assert!(results.all_same());
    assert!(results["llvm"]
        .as_ref()
        .is_ok_and(|output| output.status.success() && output.stdout == "5\n"))
}
