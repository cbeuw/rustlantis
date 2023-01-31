use std::{path::Path, process::{self, Command}};

pub struct CompExecError(process::Output);

pub trait Backend {
    fn execute(source: &Path) -> Result<process::Output, CompExecError>;
}

pub struct LLVM {}
pub struct Cranelift {}
pub struct Miri {}

impl Backend for LLVM {
    fn execute(source: &Path) -> Result<process::Output, CompExecError> {
        let target_dir = tempfile::tempdir().unwrap();
        let target_path = target_dir.path().join("target");
        let compile_out = Command::new("rustc")
            .arg(source)
            .args(["-o", target_path.to_str().unwrap()])
            .output()
            .expect("failed to execute rustc");
        if !compile_out.status.success() {
            return Err(CompExecError(compile_out));
        }

        let exec_out = Command::new(target_path).output().expect("failed to execute target program");
        Ok(exec_out)
    }
}

impl Backend for Miri {
    fn execute(source: &Path) -> Result<process::Output, CompExecError> {
        let miri_out = Command::new("miri")
            .arg("run")
            .arg(source)
            .output()
            .expect("failed to execute miri");
        // FIXME: we assume the source always exits with 0, and any non-zero return code
        // came from Miri itself (e.g. UB and type check errors)
        if !miri_out.status.success() {
            return Err(CompExecError(miri_out));
        }
        Ok(miri_out)
    }
}

fn main() {

}