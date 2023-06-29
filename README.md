# Rustlantis
A Rust Mid-level Intermediate Representation fuzzer

It can generate [custom MIR](https://doc.rust-lang.org/std/intrinsics/mir/index.html) programs containing:
- All primitive integer and floating point types, `bool`, `char`, arrays,
tuples, raw pointers, and structs.
- Functions containing multiple basic blocks
- Terminators: `Goto`, `Return`, `SwitchInt` (`match`), `Call`.
- Intrinsic functions: `arith_offset` (for pointer arithmetics), `transmute`,
`bswap`, `fmaf64`.
- Operators: all arithmetic, logical and bitwise operations on integers
and floating points, and checked arithmetic (Add, Sub, Mul) on integers
- All primitive literal expressions, as well as tuple, array, and struct
aggregate expressions
- Creating pointers with `addr_of!` and `addr_of_mut!`, and dereferencing
- Casts between integers, floating points, `char`, and `bool`

Generated programs are terminating, UB-free, and deterministic. A discrepancy between testing backends
always indicate a bug in them (or a bug in Rustlantis).

## Requirements
- Rust nightly
- rustup

## Config
Copy `config.toml.example` to `config.toml` and supply the paths to testing backends.

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

## Quirks
- Cranelift not supported on AArch64 macOS: https://github.com/bjorn3/rustc_codegen_cranelift/issues/1248
- `rustc_codegen_backend` can be used as a backend, but it doesn't support enough language features yet to be usable

## Namesake
The Space Shuttle *Atlantis* docked with *Mir* space station seven times: https://en.wikipedia.org/wiki/Shuttle%E2%80%93Mir_program

## Tropies

### Crashes & ICEs
- `RenameReturnPlace` is broken: https://github.com/rust-lang/rust/issues/110902
- `ReferencePropagation` prevents partial initialisation: https://github.com/rust-lang/rust/issues/111426
- phi nodes assumed to be non-empty: https://github.com/llvm/llvm-project/issues/63013
- Assertion failure in `RegisterCoalescer`: https://github.com/llvm/llvm-project/issues/63033

### Silent Miscompilations
- `ConstProp` propagates over mutating borrows: https://github.com/rust-lang/rust/issues/110947
- `*const T` in function parameters annotated with `readonly`: https://github.com/rust-lang/rust/issues/111502
- Aliasing analysis merges loads from different offsets: https://github.com/rust-lang/rust/issues/112061 & https://github.com/llvm/llvm-project/issues/63019
- Constant folding produces invalid boolean values: https://github.com/rust-lang/rust/issues/112170 & https://github.com/llvm/llvm-project/issues/63055
- Aliasing analysis broken for overflowing pointer offsets: https://github.com/rust-lang/rust/issues/112526 & https://github.com/llvm/llvm-project/issues/63266
- https://github.com/rust-lang/rust/issues/112548
- Copy elision corrupts stack arguments with two parts: https://github.com/rust-lang/rust/issues/112767 & https://github.com/llvm/llvm-project/issues/63430
- Copy elision reads stack arguments from the wrong offsets: https://github.com/llvm/llvm-project/issues/63475

### Previously known bugs
- Const eval gives `x % x` wrong sign when `x` is a negative float: https://github.com/rust-lang/rust/issues/109567 (first reported https://github.com/rust-lang/rust/issues/102403)
- Write to dangling pointer is hoisted outside of condition: https://github.com/rust-lang/rust/issues/112213 (first reported https://github.com/llvm/llvm-project/issues/51838)