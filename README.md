# pasta-asm

Assembly backends for the Pasta (Pallas and Vesta) field arithmetic of the
[`pasta_curves`](https://github.com/zcash/pasta_curves) crate. The crate provides AArch64 and
x86-64 backends for modular addition and subtraction, Montgomery multiplication and squaring, a
repeated-squaring chain, and conversion out of Montgomery form, and a constant-time inversion
on every target, from AArch64 assembly blocks or the same blocks in portable Rust.

## Provenance

The routines are transcriptions of the Pasta Montgomery routines of Supranational's
[Semolina](https://github.com/supranational/semolina) v0.1.4
([`src/mach-o/pasta_mul-armv8.S`](https://github.com/supranational/semolina/blob/v0.1.4/src/mach-o/pasta_mul-armv8.S)).
`src/aarch64.rs` carries multiplication and squaring as register-renamed inline `asm!` blocks
of `mul_mont_pasta` and of the squaring loop body of `sqr_n_mul_mont_pasta`, with the same
instructions. The repeated-squaring chain and the conversion out of Montgomery form are
compositions of those blocks. The blocks were ported and adapted in
[zakura-core/common](https://github.com/zakura-core/common) and then in
[zcash/pasta_curves#100](https://github.com/zcash/pasta_curves/pull/100). This crate imports them
from that pull request at commit `efc0c69533f491743162f3263acfb6c23603ad91`, which reaches the
chain and the conversion through assembled routines instead. The addition and subtraction
blocks, which are not Semolina routines, and `src/x86_64.rs`, an x86-64 transcription of the
same Montgomery routines rescheduled around MULX and ADCX/ADOX, were imported from
zakura-pasta-curves.

The inversion, `invert`, follows s2n-bignum's
[`bignum_montinv_p256`](https://github.com/awslabs/s2n-bignum/blob/main/arm/p256/bignum_montinv_p256.S)
(Apache-2.0 OR ISC OR MIT-0), the serial variant of the algorithm of Bernstein, Chen, Harrison,
Huang, Maxwell, Wang, Wuille, and Yang, "Accelerating and verifying constant-time modular
inversion" (EUROCRYPT 2026): its `divstep59` macro on named registers with the Pasta constants,
its updates of `f`, `g`, `u`, and `v` as blocks of one matrix row each, and its
almost-Montgomery reduction for the Pasta modulus shape, composed in Rust as
`design/constant-time-inversion.md` lays out.

## Usage

The crate provides a backend for `target_arch = "aarch64"`, and for `target_arch = "x86_64"`
with 64-bit pointers. On x86-64, `add`, `sub`, and `from_mont` are register-only (MULX needs
BMI2 for `from_mont`). `mul`, `square`, and the routines built on them read limbs through
pointers, which the x32 ABI's 32-bit pointers would break, so the crate is empty on that
target; they also need MULX and ADCX/ADOX (BMI2 and ADX: Intel Broadwell / AMD Zen or newer).
Apple x86-64 targets are excluded altogether: they reserve `rbp`, and so have fewer available
registers than the squaring blocks need.

On every other target, that is any target other than AArch64 and non-Apple x86-64 with 64-bit
pointers, the crate has no Montgomery backend. Nor has it one, on any target, when the compiler
is passed `--cfg pasta_asm_disable` (through `RUSTFLAGS`, or `rustflags` in
`.cargo/config.toml`), which is how to build for old x86-64 CPUs without BMI2 and ADX. A
consumer does not repeat these conditions: it declares its uses of the crate under
`pasta_asm::if_supported!` and its portable fallback under `pasta_asm::if_unsupported!`; the
first expands to its items exactly where the crate has a backend, and the second exactly where
it does not. `pasta_asm::BACKEND` names the result. The constant-time inversion, `invert`, is
provided on every target and under `pasta_asm_disable` too: by assembly blocks on AArch64 with
the assembly enabled, and by the same blocks in portable Rust (`src/portable.rs`) otherwise.
Two things follow for a direct consumer. The expansion is checked in the consumer's crate, so
the consumer declares the cfg as expected, in its `Cargo.toml`:

```toml
[lints.rust]
unexpected_cfgs = { level = "warn", check-cfg = ['cfg(pasta_asm_disable)'] }
```

And a build that sets the flag sets it for rustdoc too (`RUSTDOCFLAGS`): `cargo test` and
`cargo doc` run rustdoc over the consumer's crate, which expands the macros under rustdoc's
flags, and against a crate built with the flag the supported arm does not resolve.

Nothing is assembled at build time: the blocks are compiled by the Rust toolchain, so no C
toolchain is needed, and the crate is `no_std` with no dependencies.

The blocks have no data-dependent branch or memory access, and a release build runs nothing
else. So the routines' timing should not depend on their operands, unless behaviour of the Rust
toolchain or platform introduces an unexpected obstacle to that. A debug build also runs the
assertions' checks, and debug mode carries no constant-time guarantee. The checks are written
without data-dependent branches, and pass their words through `core::hint::black_box`, as
`subtle` does. An inspection of the output of one toolchain (AArch64, Rust 1.96.1) found only
the assertions' own branches left, but that is best effort, which the compiler owes nothing to.

Field elements and moduli are `[u64; 4]`, least significant limb first, and `inv` is
`-modulus[0]^-1 mod 2^64`. The routines take the modulus and `inv` as arguments, so one
implementation serves both fields, but they rely on the shape the two Pasta moduli share:
`modulus[2] = 0` and `modulus[3] = 2^62`. The crate documentation states the operand contract of
each entry point.

`mul` is Montgomery multiplication in the CIOS form (Coarsely Integrated Operand Scanning): see
Çetin Kaya Koç, Tolga Acar, and Burton S. Kaliski Jr.,
[Analyzing and Comparing Montgomery Multiplication Algorithms](https://www.microsoft.com/en-us/research/wp-content/uploads/1996/01/j37acmon.pdf),
also published in IEEE Micro 16(3), 1996. Each of its four rounds adds `lhs` times one limb of
`rhs` to an accumulator, cancels the accumulator's low limb by adding a multiple of the
modulus, and shifts it down by one limb. Textbook CIOS keeps a six-limb accumulator for
four-limb operands. These routines keep five, one fewer, which the operand contracts make safe.
The squaring blocks and the conversion out of Montgomery form make the same cancellations.

## Testing

Where the crate has a backend, `cargo test --release` runs known-answer tests of the entry
points for both fields and replays the reference vectors recorded from the AArch64 assembly;
in a debug build it also checks that the operand assertions fire outside the contracts. The
inversion's blocks are tested one by one against an integer model of the algorithm, and the
inversion against known answers, the identity `x · x^-1 = 1`, and a Fermat inverse computed
with a reference multiplication, over the assembly blocks on AArch64 and over the portable
blocks everywhere. Elsewhere, and with `--cfg pasta_asm_disable`, those tests over the portable
blocks are the ones that run, and the crate documentation's example runs on its portable arm.
`pasta_curves` tests the backend against its portable arithmetic when its `aarch64-asm` feature
is enabled. `scripts/ci.sh` runs every check CI runs.

## Formal verification

`lean/` holds a Lean 4 development that models the routines formally and contributes to
assuring their correctness. The model is at the instruction level. Individual blocks of
assembly are proven; from those, each of the six Montgomery entry points is proved at either
Pasta field, under the condition that the entry point asserts. The inversion's algorithm is
proved on words (`montInv_spec`), each of its six AArch64 blocks is proved to compute its
word-level function, and `invert` is proved at either field from their composition
(`invert_entry_spec`), with the primality of the modulus as a hypothesis. The portable blocks
are not modelled; they are checked against the same known answers as the assembly blocks, and a
translation to Lean by Aeneas is the intended way to bring them under the same proof. The
transcription is generated from the crate's own inline blocks, CI regenerates and diffs it, and
the independent `nanoda` implementation of the Lean kernel re-checks the build. See
[`lean/README.md`](lean/README.md).

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
