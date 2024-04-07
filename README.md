# Rustlantis
A Rust Mid-level Intermediate Representation fuzzer

It can generate [custom MIR](https://doc.rust-lang.org/std/intrinsics/mir/index.html) programs containing:
- All primitive integer and floating point types, `bool`, `char`, arrays,
tuples, references, raw pointers, structs, and enums.
- Functions containing multiple basic blocks
- Terminators: `Goto`, `Return`, `SwitchInt` (`match`), `Call`.
- Intrinsic functions: `arith_offset` (for pointer arithmetics), `transmute`,
`bswap`, `fmaf64`.
- Operators: all arithmetic, logical and bitwise operations on integers
and floating points, and checked arithmetic (Add, Sub, Mul) on integers
- All primitive literal expressions, as well as tuple, array, and struct
aggregate expressions
- Creating references and raw pointers, and dereferencing them
- Casts between integers, floating points, `char`, and `bool`

Generated programs are terminating, UB-free, and deterministic. A discrepancy between testing backends
always indicate a bug in them (or a bug in Rustlantis).

## Requirements
- Rust nightly
- rustup

## Config
Copy `config.toml.example` to `config.toml` and supply the paths to the *repository root* of testing backends.

To prepare `rustc_codegen_cranelift`:
```bash
git clone https://github.com/bjorn3/rustc_codegen_cranelift
cd rustc_codegen_cranelift && ./y.rs prepare && ./y.rs build
```

To prepare Miri:
```bash
git clone https://github.com/rust-lang/miri
cargo install rustup-toolchain-install-master
cd miri && ./miri toolchain && ./miri build --release && ./target/release/cargo-miri miri setup
```

## Usage

To generate and difftest one seed, run

```bash
./fuzz-one.sh <seed>
```

A program will be generated to `$TMPDIR` and tested. If difftest passes (no bug), it will exit with 0. If difftest spots a difference between testing backends, it will exit with 1 and save the reproduction file to `./repros/`.

To generate a program only, run `generate`
```
Usage: generate [OPTIONS] <seed>

Arguments:
  <seed>  generation seed

Options:
  -d, --debug                      generate a program where values are printed instead of hashed (slow)
      --call-syntax <call-syntax>  switch between different versions of Call syntaxes [default: v4] [possible values: v1, v2, v3, v4]
  -h, --help                       Print help
  -V, --version                    Print version
```

To difftest an existing program, run `difftest`
```
Usage: difftest <file>

Arguments:
  <file>  

Options:
  -h, --help  Print help
```

## Quirks (LINKS ARE NOT ANONYMOUS)
- Cranelift not supported on AArch64 macOS: bjorn3/rustc_codegen_cranelift/issues/1248
- `rustc_codegen_backend` can be used as a backend, but it doesn't support enough language features yet to be usable

## Namesake
The Space Shuttle *Atlantis* docked with *Mir* space station seven times: https://en.wikipedia.org/wiki/Shuttle%E2%80%93Mir_program

## Trophies (LINKS ARE NOT ANONYMOUS)

🦀: Root cause in Rust
🐉: Root cause in LLVM
🏗️: Root cause in Cranelift

### Crashes & ICEs
- 🦀 `RenameReturnPlace` is broken: rust-lang/rust/issues/110902
- 🦀 `ReferencePropagation` prevents partial initialisation: rust-lang/rust/issues/111426
- 🐉 phi nodes assumed to be non-empty: llvm/llvm-project/issues/63013
- 🐉 Assertion failure in `RegisterCoalescer`: llvm/llvm-project/issues/63033
- 🦀 MIR inlining inserts statements at the wrong place: rust-lang/rust/issues/117355
- 🏗️ Overflowing shift triggers panic in Cranelift: rust-lang/rustc_codegen_cranelift/issues/1455 & bytecodealliance/wasmtime/issues/7865

### Silent Miscompilations
- 🦀 `ConstProp` propagates over mutating borrows: rust-lang/rust/issues/110947
- 🦀 `*const T` in function parameters annotated with `readonly`: rust-lang/rust/issues/111502
- 🐉 Aliasing analysis merges loads from different offsets: rust-lang/rust/issues/112061 & llvm/llvm-project/issues/63019
- 🐉 Constant folding produces invalid boolean values: rust-lang/rust/issues/112170 & llvm/llvm-project/issues/63055
- 🐉 Aliasing analysis broken for overflowing pointer offsets: rust-lang/rust/issues/112526 & llvm/llvm-project/issues/63266
- rust-lang/rust/issues/112548
- 🐉 Copy elision corrupts stack arguments with two parts: rust-lang/rust/issues/112767 & llvm/llvm-project/issues/63430
- 🐉 Copy elision reads stack arguments from the wrong offsets: llvm/llvm-project/issues/63475
- 🦀 Subnormal f64 to f32 cast is wrong: rust-lang/rust/issues/113407
- 🐉 AST size merging is wrong: llvm/llvm-project/issues/64897 
- 🦀 `ConstProp` propagates over assignment of unknown values: rust-lang/rust/issues/118328
- 🐉 Bad `undef`/`poison` handling in `InstCombine`: llvm/llvm-project/issues/74890
- 🦀 `GVN` merges moved function arguments: rust-lang/rust/issues/120613
- 🐉 `GVNPass` forgets to remove poison generating flags: llvm/llvm-project/issues/82884
- 🏗️ Misoptimization of imul + ireduce: rust-lang/rustc_codegen_cranelift/issues/1460 & bytecodealliance/wasmtime/issues/7999
- 🐉 `InstCombine` calculates wrong `insertelement` instructions: rust-lang/rust/issues/121996 & llvm/llvm-project/issues/84025

### Previously known bugs
- 🦀 Const eval gives `x % x` wrong sign when `x` is a negative float: rust-lang/rust/issues/109567 (first reported rust-lang/rust/issues/102403)
- 🐉 Write to dangling pointer is hoisted outside of condition: rust-lang/rust/issues/112213 (first reported llvm/llvm-project/issues/51838)
