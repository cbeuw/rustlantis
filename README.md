# Rustlantis
A Rust Mid-level Intermediate Representation fuzzer

## Requirements
- Rust nightly
- rustup

## Quirks
- Cranelift not supported on AArch64 macOS: https://github.com/bjorn3/rustc_codegen_cranelift/issues/1248

## Namesake
The Space Shuttle *Atlantis* docked with *Mir* space station seven times: https://en.wikipedia.org/wiki/Shuttle%E2%80%93Mir_program

## Tropies

### Crashes & ICEs
- https://github.com/rust-lang/rust/issues/110902
- https://github.com/rust-lang/rust/issues/111426
- https://github.com/llvm/llvm-project/issues/63013
- https://github.com/llvm/llvm-project/issues/63033

### Silent Miscompilations
- https://github.com/rust-lang/rust/issues/110947
- https://github.com/rust-lang/rust/issues/111502
- https://github.com/rust-lang/rust/issues/112061 && https://github.com/llvm/llvm-project/issues/63019
- https://github.com/rust-lang/rust/issues/112170 && https://github.com/llvm/llvm-project/issues/63055
- https://github.com/rust-lang/rust/issues/112526 && https://github.com/llvm/llvm-project/issues/63266
- https://github.com/rust-lang/rust/issues/112548
- https://github.com/rust-lang/rust/issues/112767 && https://github.com/llvm/llvm-project/issues/63430

### Previously known bugs
- https://github.com/rust-lang/rust/issues/109567 (first reported https://github.com/rust-lang/rust/issues/102403)
- https://github.com/rust-lang/rust/issues/112213 (first reported https://github.com/llvm/llvm-project/issues/51838)