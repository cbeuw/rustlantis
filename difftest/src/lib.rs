#![feature(iter_intersperse)]
#![feature(let_chains)]

pub mod backends;

// pub use backend;
use std::{
    collections::{HashMap, HashSet},
    fmt,
    ops::Index,
    path::Path,
    time::Instant,
};

use backends::{Backend, CompExecError, ExecResult};
use colored::Colorize;
use log::{debug, log_enabled};
use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};

pub type BackendName = &'static str;

pub struct ExecResults {
    // Equivalence classes of exec results and backends
    results: HashMap<ExecResult, HashSet<BackendName>>,
}

impl ExecResults {
    pub fn from_exec_results<'a>(
        map: impl Iterator<Item = (&'a BackendName, &'a ExecResult)>,
    ) -> Self {
        //TODO: optimisation here to check if all results are equal directly, since most should be

        // Split execution results into equivalent classes
        let mut eq_classes: HashMap<ExecResult, HashSet<BackendName>> = HashMap::new();

        'outer: for (&name, result) in map {
            for (class_result, names) in &mut eq_classes {
                // Put into an existing equivalence class
                let eq = if let Ok(class_out) = class_result
                    && let Ok(out) = result
                {
                    class_out.stdout == out.stdout
                } else {
                    result == class_result
                };
                if eq {
                    names.insert(name);
                    continue 'outer;
                }
            }

            // No equal execution result, make a new class
            eq_classes.insert(result.clone(), HashSet::from([name]));
        }

        Self {
            results: eq_classes,
        }
    }

    pub fn all_same(&self) -> bool {
        self.results.len() == 1
    }

    pub fn all_success(&self) -> bool {
        self.results.keys().all(|r| r.is_ok())
    }

    pub fn has_ub(&self) -> Option<bool> {
        self.results
            .iter()
            .find_map(|(result, backends)| {
                if backends.contains("miri") {
                    Some(result)
                } else {
                    None
                }
            })
            .map(|result| {
                result.clone().is_err_and(|err| {
                    err.0
                        .stderr
                        .to_string_lossy()
                        .contains("Undefined Behavior")
                })
            })
    }
}

impl Index<BackendName> for ExecResults {
    type Output = ExecResult;

    fn index(&self, index: BackendName) -> &Self::Output {
        for (result, names) in &self.results {
            if names.contains(index) {
                return result;
            }
        }
        panic!("no result for {index}")
    }
}

impl fmt::Display for ExecResults {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (result, names) in &self.results {
            f.write_fmt(format_args!(
                "{} produced the following output:\n",
                names
                    .iter()
                    .copied()
                    .intersperse(", ")
                    .collect::<String>()
                    .blue()
            ))?;
            match result {
                Ok(out) => {
                    f.write_fmt(format_args!("stdout:\n{}", out.stdout.to_string_lossy()))?;
                }
                Err(CompExecError(out)) => {
                    f.write_fmt(format_args!("status: {}\n", out.status))?;
                    f.write_fmt(format_args!(
                        "stdout:\n{}================\n",
                        out.stdout.to_string_lossy()
                    ))?;
                    f.write_fmt(format_args!(
                        "{}:\n{}================\n",
                        "stderr".red(),
                        out.stderr.to_string_lossy()
                    ))?;
                }
            }
        }
        Ok(())
    }
}

pub fn run_diff_test<'a>(
    source_file: &Path,
    backends: HashMap<BackendName, Box<dyn Backend + 'a>>,
) -> ExecResults {
    let target_dir = tempfile::tempdir().unwrap();
    let exec_results: HashMap<BackendName, ExecResult> = backends
        .par_iter()
        .map(|(&name, b)| {
            let target_path = target_dir.path().join(name);
            let result = if log_enabled!(log::Level::Debug) {
                let time = Instant::now();
                let result = b.execute(source_file, &target_path);
                let dur = time.elapsed();
                debug!("{name} took {}s", dur.as_secs_f32());
                result
            } else {
                b.execute(source_file, &target_path)
            };
            (name, result)
        })
        .collect();

    ExecResults::from_exec_results(exec_results.iter())
}
