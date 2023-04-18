use std::{
    ffi::{OsStr, OsString},
    hash::{Hash, Hasher},
    path::{Path, PathBuf},
    process::{self, Command, ExitStatus},
};

use log::debug;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ProcessOutput {
    pub status: ExitStatus,
    /// The data that the process wrote to stdout.
    pub stdout: OsString,
    /// The data that the process wrote to stderr.
    pub stderr: OsString,
}
impl Hash for ProcessOutput {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.status.code().hash(state);
        self.stdout.hash(state);
        self.stderr.hash(state);
    }
}

impl From<process::Output> for ProcessOutput {
    fn from(value: process::Output) -> Self {
        let stdout: OsString;
        let stderr: OsString;
        #[cfg(unix)]
        {
            use std::os::unix::prelude::OsStrExt;
            stdout = OsStr::from_bytes(&value.stdout).to_owned();
            stderr = OsStr::from_bytes(&value.stderr).to_owned();
        }
        #[cfg(windows)]
        {
            use std::os::windows::prelude::OsStrExt;
            stdout = OsStr::from_wide(&value.stdout).to_owned();
            stderr = OsStr::from_wide(&value.stderr).to_owned();
        }
        Self {
            status: value.status,
            stdout,
            stderr,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct CompExecError(pub ProcessOutput);

// #[derive(Debug, PartialEq, Eq, Clone)]
// pub struct ProgramOutput(pub process::Output);

pub type ExecResult = Result<ProcessOutput, CompExecError>;

#[derive(Debug)]
pub struct BackendInitError(pub String);

pub trait Backend: Send + Sync {
    fn execute(&self, source: &Path) -> ExecResult;
}

#[derive(Debug, Clone, Copy)]
pub enum OptLevel {
    Unoptimised,
    Optimised,
}

impl OptLevel {
    fn rustc_opt_level(&self) -> usize {
        match self {
            OptLevel::Unoptimised => 0,
            OptLevel::Optimised => 3,
        }
    }
}

pub struct LLVM {
    toolchain: Option<String>,
    opt_level: OptLevel,
}

impl LLVM {
    pub fn new(opt_level: OptLevel, toolchain: Option<String>) -> Self {
        Self {
            opt_level,
            toolchain,
        }
    }
}

impl Backend for LLVM {
    fn execute(&self, source: &Path) -> ExecResult {
        let target_dir = tempfile::tempdir().unwrap();
        let target_path = target_dir.path().join("target");
        debug!(
            "Compiling {} with rustc_codegen_llvm",
            source.to_string_lossy()
        );

        let mut command = Command::new("rustc");
        if let Some(toolchain) = &self.toolchain {
            command.arg(format!("+{}", toolchain));
        }

        let compile_out = command
            .arg(source)
            .args(["-o", target_path.to_str().unwrap()])
            .args([
                "-C",
                &format!("opt-level={}", self.opt_level.rustc_opt_level()),
            ])
            .output()
            .expect("can execute rustc and get output");
        if !compile_out.status.success() {
            return Err(CompExecError(compile_out.into()));
        }

        debug!("Executing LLVM compiled {}", source.to_string_lossy());
        let exec_out = Command::new(target_path)
            .output()
            .expect("can execute target program and get output");
        Ok(exec_out.into())
    }
}

pub struct Miri {
    binary: PathBuf,
    sysroot: OsString,
}

impl Miri {
    fn find_sysroot(miri_dir: &Path) -> Result<OsString, BackendInitError> {
        let output = Command::new(miri_dir.join("target/release/cargo-miri"))
            .arg("miri")
            .arg("setup")
            .arg("--print-sysroot")
            .env_clear()
            .env("PATH", env!("PATH"))
            .current_dir(miri_dir)
            .output()
            .expect("can run cargo-miri setup --print-sysroot");
        if !output.status.success() {
            return Err(BackendInitError(format!(
                "failed to find sysroot: {output:?}"
            )));
        }
        let sysroot;
        #[cfg(unix)]
        {
            use std::os::unix::prelude::OsStrExt;
            sysroot = OsStr::from_bytes(output.stdout.trim_ascii_end()).to_owned();
        }
        #[cfg(windows)]
        {
            use std::os::windows::prelude::OsStrExt;
            sysroot = OsStr::from_wide(output.stdout.trim_ascii_end()).to_owned();
        }
        debug!("Miri sysroot at {}", sysroot.to_string_lossy());
        Ok(sysroot)
    }

    pub fn from_repo<P: AsRef<Path>>(miri_dir: P) -> Result<Self, BackendInitError> {
        let miri_dir = miri_dir.as_ref();

        // Detect if Miri already built
        if !Path::exists(&miri_dir.join("target/release/cargo-miri"))
            || !Path::exists(&miri_dir.join("target/release/miri"))
        {
            // Otherwise, build it ourselves
            debug!("Setting up miri toolchain");
            let output = Command::new(miri_dir.join("miri"))
                .arg("toolchain")
                .output()
                .expect("can run miri toolchain and get output");
            if !output.status.success() {
                return Err(BackendInitError(format!(
                    "failed to set up Miri toolchain: {output:?}"
                )));
            }

            debug!("Building Miri under {}", miri_dir.to_string_lossy());
            let output = Command::new(miri_dir.join("miri"))
                .arg("build")
                .arg("--release")
                .env_clear()
                .env("PATH", env!("PATH"))
                .current_dir(miri_dir)
                .output()
                .expect("can run miri build and get output");
            if !output.status.success() {
                return Err(BackendInitError(format!(
                    "failed to build Miri: {output:?}"
                )));
            }
        } else {
            debug!("Detected built Miri under {}", miri_dir.to_string_lossy());
        }

        let sysroot = Self::find_sysroot(miri_dir)?;

        Ok(Self {
            binary: miri_dir.join("target/release/miri"),
            sysroot,
        })
    }

    pub fn from_binary<P: AsRef<Path>>(binary_path: P, sysroot: P) -> Self {
        Self {
            binary: binary_path.as_ref().to_owned(),
            sysroot: sysroot.as_ref().as_os_str().to_owned(),
        }
    }
}

impl Backend for Miri {
    fn execute(&self, source: &Path) -> ExecResult {
        debug!("Executing {} with Miri", source.to_string_lossy());
        let miri_out = Command::new(&self.binary)
            .args([OsStr::new("--sysroot"), self.sysroot.as_os_str()])
            .arg("-Zmiri-tree-borrows")
            .arg(source)
            .env_clear()
            .output()
            .expect("can run miri and get output");
        // FIXME: we assume the source always exits with 0, and any non-zero return code
        // came from Miri itself (e.g. UB and type check errors)
        if !miri_out.status.success() {
            return Err(CompExecError(miri_out.into()));
        }
        Ok(miri_out.into())
    }
}

pub struct Cranelift {
    binary: PathBuf,
    opt_level: OptLevel,
}

impl Cranelift {
    pub fn from_repo<P: AsRef<Path>>(
        clif_dir: P,
        opt_level: OptLevel,
    ) -> Result<Self, BackendInitError> {
        let clif_dir = clif_dir.as_ref();

        if !Path::exists(&clif_dir.join("dist/rustc-clif")) {
            debug!("Setting up cranelift under {}", clif_dir.to_string_lossy());
            let output = Command::new(clif_dir.join("y.rs"))
                .arg("prepare")
                .env_clear()
                .env("PATH", env!("PATH"))
                .current_dir(clif_dir)
                .output()
                .expect("can run y.rs prepare and get output");
            if !output.status.success() {
                return Err(BackendInitError(format!(
                    "failed to prepare Cranelift: {output:?}"
                )));
            }

            let output = Command::new(clif_dir.join("y.rs"))
                .arg("build")
                .env_clear()
                .env("PATH", env!("PATH"))
                .current_dir(clif_dir)
                .output()
                .expect("can run y.rs build and get output");
            if !output.status.success() {
                return Err(BackendInitError(format!(
                    "failed to build Cranelift: {output:?}"
                )));
            }
        } else {
            debug!("Found built Cranelift under {}", clif_dir.to_string_lossy());
        }

        Ok(Cranelift {
            binary: clif_dir.join("dist/rustc-clif"),
            opt_level,
        })
    }

    pub fn from_binary<P: AsRef<Path>>(binary_path: P, opt_level: OptLevel) -> Self {
        Self {
            binary: binary_path.as_ref().to_owned(),
            opt_level,
        }
    }
}

impl Backend for Cranelift {
    fn execute(&self, source: &Path) -> ExecResult {
        let target_dir = tempfile::tempdir().unwrap();
        let target_path = target_dir.path().join("target");
        debug!(
            "Compiling {} with rustc_codegen_cranelift",
            source.to_string_lossy()
        );
        let compile_out = Command::new(&self.binary)
            .arg(source)
            .args(["-o", target_path.to_str().unwrap()])
            .args([
                "-C",
                &format!("opt-level={}", self.opt_level.rustc_opt_level()),
            ])
            .output()
            .expect("can run rustc-clif and get output");
        if !compile_out.status.success() {
            return Err(CompExecError(compile_out.into()));
        }

        debug!("Executing Cranelift compiled {}", source.to_string_lossy());
        let exec_out = Command::new(target_path)
            .output()
            .expect("can run target program and get output");
        Ok(exec_out.into())
    }
}