# pasta-asm

Assembly backends for the Pasta (Pallas and Vesta) field arithmetic of the
[`pasta_curves`](https://github.com/zcash/pasta_curves) crate. The crate provides AArch64 and
x86-64 backends for modular addition and subtraction, Montgomery multiplication and squaring,
a repeated-squaring chain, inversion, and conversion out of Montgomery form. Availability
and CPU requirements differ by operation; see Usage below.

## Provenance

The Montgomery multiplication and squaring backends derive from the Pasta routines of Supranational's
[Semolina](https://github.com/supranational/semolina) v0.1.4
([`src/mach-o/pasta_mul-armv8.S`](https://github.com/supranational/semolina/blob/v0.1.4/src/mach-o/pasta_mul-armv8.S)).
`src/aarch64.rs` carries multiplication and squaring as register-renamed inline `asm!` blocks
of `mul_mont_pasta` and of the squaring loop body of `sqr_n_mul_mont_pasta`, with the same
instructions. The repeated-squaring chain and the conversion out of Montgomery form are
compositions of those blocks. The blocks were ported and adapted in
[zakura-core/common](https://github.com/zakura-core/common) and then in
[zcash/pasta_curves#100](https://github.com/zcash/pasta_curves/pull/100). This crate imports them
from that pull request at commit `efc0c69533f491743162f3263acfb6c23603ad91`, which reaches the
chain and the conversion through assembled routines instead.

The inversion backends in `src/{aarch64,x86_64}/invert.rs` are staged inline-assembly
ports of Semolina v0.1.4's `ct_inverse_pasta` routine (commit
`13ffc78074a6fbec44a4fd12b7f585a0bc1dc154`). Sources are the
[AArch64 generator](https://github.com/supranational/semolina/blob/v0.1.4/src/asm/ct_inverse_mod_256-armv8.pl)
and [x86-64 generator](https://github.com/supranational/semolina/blob/v0.1.4/src/asm/ct_inverse_mod_256-x86_64.pl),
checked against their generated
[AArch64](https://github.com/supranational/semolina/blob/v0.1.4/src/elf/ct_inverse_mod_256-armv8.S)
and [x86-64](https://github.com/supranational/semolina/blob/v0.1.4/src/elf/ct_inverse_mod_256-x86_64.s)
instruction streams. The Montgomery wrapper is adapted from
[`recip.c`](https://github.com/supranational/semolina/blob/v0.1.4/src/recip.c).

The ports retain the approximation, binary-GCD inner-loop, and final-correction
kernels and the fixed 15 × 31 + 47 iteration schedule. They adapt coefficient updates
to fixed-width signed arithmetic instead of upstream's width-specialized helpers,
replace memory-based helper interfaces with register operands, and use a Rust driver.
Every inversion assembly block declares `nomem`; compiler-generated loads and spills
outside the blocks remain possible. Converting the input out of Montgomery form first
and using a split reduction afterward avoids upstream's final multiplication by `R^2`.
There is no global assembly or external assembler. Inversion returns a canonical Montgomery
residue and maps zero to zero. This new port is not covered by the existing Lean
proofs. The independent inversion tests run on native x86-64; AArch64 has been
cross-built but still needs runtime validation on AArch64 hardware.

## Usage

The crate provides all operations on `target_arch = "aarch64"`. On
`target_arch = "x86_64"`, availability is operation-specific:

- `add` and `sub` use baseline x86-64 instructions and register-only operands.
- `from_mont` and `invert` also use register-only assembly, but require BMI2 (MULX).
  They do not require ADX or 64-bit pointers.
- `mul`, `square`, and `sqr_n_mul` use pointer-based assembly operands and require
  64-bit pointers, BMI2, and ADX (MULX and ADCX/ADOX: Intel Broadwell / AMD Zen or newer).

CPU features are not checked at runtime. On other architectures this crate is empty;
consumers must gate each operation appropriately and fall back to portable arithmetic.
The Rust toolchain assembles the inline blocks, so no external assembler or C toolchain
is needed. The crate is `no_std` with no dependencies.

Field elements and moduli are `[u64; 4]`, least significant limb first, and `inv` is
`-modulus[0]^-1 mod 2^64`. The routines take the modulus and `inv` as arguments, so one
implementation serves both fields, but they rely on the shape the two Pasta moduli share:
`modulus[2] = 0` and `modulus[3] = 2^62`. The crate documentation states the operand contract of
each entry point.

## Testing

On AArch64 and x86-64 (with 64-bit pointers if relevant), `cargo test` runs known-answer tests
of the entry points for both fields; on other targets there is nothing to test. `pasta_curves`
tests the backend against its portable arithmetic when its `asm` feature is enabled.
`scripts/ci.sh` runs every check CI runs.

## Formal verification

`lean/` holds a Lean 4 development that models the routines formally and contributes to assuring
their correctness. The model is at the instruction level. Individual blocks of assembly are
proven; from those, each of the six entry points is proved at either Pasta field, under the
condition that the entry point asserts. The transcription is generated from the crate's own
inline blocks, CI regenerates and diffs it, and the independent `nanoda` implementation of the
Lean kernel re-checks the build. See [`lean/README.md`](lean/README.md).

## License

This crate is licensed under the Apache License, Version 2.0 only ([LICENSE](LICENSE)). The
assembly routines are Copyright Supranational LLC under that license, and everything derived
from them, including the inline transcription and any transcription of the routines into
another form, carries the same license. That is part of the reason the backend is a separate
crate rather than part of the dual-licensed `pasta_curves`, which depends on it optionally. The
other part is separation of concerns, keeping the assembly apart from the portable arithmetic.

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion
in this crate by you, as defined in the Apache-2.0 license, shall be licensed as above,
without any additional terms or conditions.
