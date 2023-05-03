use std::{
    ffi::{OsStr, OsString},
    fs::read_to_string,
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
    fn compile(&self, source: &Path, target: &Path) -> ProcessOutput {
        panic!("not implemented")
    }

    fn execute(&self, source: &Path) -> ExecResult {
        let target_dir = tempfile::tempdir().unwrap();
        let target_path = target_dir.path().join("target");
        debug!("Compiling {}", source.to_string_lossy());
        let compile_out = self.compile(source, &target_path);
        if !compile_out.status.success() {
            return Err(CompExecError(compile_out));
        }

        debug!("Executing compiled {}", source.to_string_lossy());
        let exec_out = Command::new(target_path)
            .output()
            .expect("can execute target program and get output");
        Ok(exec_out.into())
    }
}

#[derive(Debug, Clone, Copy)]
pub enum OptLevel {
    Unoptimised = 0,
    Optimised = 3,
}

pub struct LLVM {
    toolchain: Option<String>,
    codegen_opt: OptLevel,
    mir_opt: OptLevel,
}

impl LLVM {
    pub fn new(toolchain: Option<String>, codegen_opt: OptLevel, mir_opt: OptLevel) -> Self {
        Self {
            codegen_opt,
            mir_opt,
            toolchain,
        }
    }
}

impl Backend for LLVM {
    fn compile(&self, source: &Path, target: &Path) -> ProcessOutput {
        let mut command = Command::new("rustc");
        if let Some(toolchain) = &self.toolchain {
            command.arg(format!("+{}", toolchain));
        }

        let compile_out = command
            .arg(source)
            .args(["-o", target.to_str().unwrap()])
            .args(["-C", &format!("opt-level={}", self.codegen_opt as u32)])
            .args(["-Z", &format!("mir-opt-level={}", self.mir_opt as u32)])
            .output()
            .expect("can execute rustc and get output");

        compile_out.into()
    }
}

pub struct Miri {
    binary: PathBuf,
    sysroot: PathBuf,
}

impl Miri {
    fn find_sysroot(miri_dir: &Path) -> Result<PathBuf, BackendInitError> {
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

        let sysroot = PathBuf::from(sysroot);

        debug!("Miri sysroot at {}", sysroot.to_string_lossy());
        if !Path::exists(&sysroot) {
            return Err(BackendInitError("sysroot does not exist".to_string()));
        }

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
            sysroot: sysroot.as_ref().to_owned(),
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
    codegen_opt: OptLevel,
    mir_opt: OptLevel,
}

impl Cranelift {
    pub fn from_repo<P: AsRef<Path>>(
        clif_dir: P,
        codegen_opt: OptLevel,
        mir_opt: OptLevel,
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
            codegen_opt,
            mir_opt,
        })
    }

    pub fn from_binary<P: AsRef<Path>>(
        binary_path: P,
        codegen_opt: OptLevel,
        mir_opt: OptLevel,
    ) -> Self {
        Self {
            binary: binary_path.as_ref().to_owned(),
            codegen_opt,
            mir_opt,
        }
    }
}

impl Backend for Cranelift {
    fn compile(&self, source: &Path, target: &Path) -> ProcessOutput {
        let compile_out = Command::new(&self.binary)
            .arg(source)
            .args(["-o", target.to_str().unwrap()])
            .args(["-C", &format!("opt-level={}", self.codegen_opt as u32)])
            .args(["-Z", &format!("mir-opt-level={}", self.mir_opt as u32)])
            .output()
            .expect("can run rustc-clif and get output");
        compile_out.into()
    }
}

pub struct GCC {
    library: PathBuf,
    sysroot: PathBuf,
    toolchain: String,
    codegen_opt: OptLevel,
    mir_opt: OptLevel,
}

impl GCC {
    pub fn from_built_repo<P: AsRef<Path>>(
        cg_gcc: P,
        codegen_opt: OptLevel,
        mir_opt: OptLevel,
    ) -> Result<Self, BackendInitError> {
        let cg_gcc = cg_gcc.as_ref();

        let toolchain = read_to_string(cg_gcc.join("rust-toolchain")).map_err(|_| {
            BackendInitError(
                "cannot detect rust-toolchain file under rustc_codegen_gcc repo".to_string(),
            )
        })?;
        let library = cg_gcc.join("target/release/librustc_codegen_gcc.so");
        let sysroot = cg_gcc.join("build_sysroot/sysroot");

        if !Path::exists(&library) {
            return Err(BackendInitError(
                "cannot find librustc_codegen_gcc.so".to_string(),
            ));
        }

        if !Path::exists(&sysroot) {
            return Err(BackendInitError("cannot find sysroot".to_string()));
        }

        Ok(Self {
            library,
            sysroot,
            toolchain,
            codegen_opt,
            mir_opt,
        })
    }
}
impl Backend for GCC {
    fn compile(&self, source: &Path, target: &Path) -> ProcessOutput {
        let compile_out = Command::new("rustc")
            .arg(format!("+{}", self.toolchain))
            .arg(source)
            .arg("-Zcodegen-backend")
            .arg(self.library.as_path())
            .arg("--sysroot")
            .arg(&self.sysroot)
            .args(["-o", target.to_str().unwrap()])
            .args(["-C", &format!("opt-level={}", self.codegen_opt as u32)])
            .args(["-Z", &format!("mir-opt-level={}", self.mir_opt as u32)])
            .output()
            .expect("can run rustc-clif and get output");
        compile_out.into()
    }
}
