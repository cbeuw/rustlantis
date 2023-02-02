#![feature(is_some_and)]

use std::{collections::HashMap, path::PathBuf, str::FromStr, ffi::OsStr, os::unix::prelude::OsStrExt};

use config::Config;
use difftest::{run_diff_test, backend::{Backend, LLVM, Miri, Cranelift}};

#[test]
fn correct_mir() {
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

    let results = run_diff_test(&PathBuf::from_str("tests/inputs/simple.rs").unwrap(), &backends);
    for (class, names) in &results {
        println!("{}: {class:?}", names.join(", "));
    }
    assert!(results.len() == 1);
    assert!(results[0].0.as_ref().is_ok_and(|output| output.status.success() && OsStr::from_bytes(output.stdout.as_slice()) == "5\n"))
}