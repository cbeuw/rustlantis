#![feature(byte_slice_trim_ascii)]
pub mod backend;

// pub use backend;
use std::{collections::HashMap, path::Path};

use backend::{Backend, ExecResult};

fn compare_exec_results<'a>(
    results: &HashMap<&'a str, backend::ExecResult>,
) -> Vec<(ExecResult, Vec<&'a str>)> {
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

    eq_classes
}

pub fn run_diff_test<'a>(
    source_file: &Path,
    backends: &HashMap<&'a str, Box<dyn Backend + 'a>>,
) -> Vec<(ExecResult, Vec<&'a str>)> {
    let mut exec_results: HashMap<&str, ExecResult> = HashMap::default();

    for (name, b) in backends {
        let result = b.execute(source_file);
        exec_results.insert(name, result);
    }

    compare_exec_results(&exec_results)
}
