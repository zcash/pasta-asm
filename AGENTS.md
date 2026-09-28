# `pasta-asm` — Agent Guidelines

> This file is read by AI coding agents (Claude Code, GitHub Copilot, Cursor, Devin, etc.).
> It provides project context and contribution policies.

This crate provides assembly backends for the Pasta field arithmetic of `pasta_curves`. It
contains an AArch64 backend and an x86-64 backend: Montgomery multiplication and squaring, and
modular addition and subtraction, as inline `asm!` blocks, and a repeated-squaring chain and
conversion out of Montgomery form composed from them; and a constant-time inversion composed
from six more blocks, in AArch64 assembly or, on every other target, in portable Rust. It is
low-level cryptographic code. Our priorities are **correctness, constant-time behaviour, and
performance**, in that order.

The Montgomery routines are transcriptions of Supranational's Semolina v0.1.4, and the
inversion's blocks are adapted from s2n-bignum's `bignum_montinv_p256` (see `README.md`). The
instruction streams are the object of machine-checked correctness proofs, so a change to an
instruction is a change to a specification: keep the transcription, its documentation, and
the proofs in step, and do not "improve" the assembly in passing.

## License & Contribution Terms

- This crate is licensed under the **Apache License, Version 2.0 only**, not the
  `MIT OR Apache-2.0` of `pasta_curves`, because its routines are derived from Supranational's
  Apache-2.0-only code and everything derived from them carries that license. Unless stated
  otherwise, any contribution intentionally submitted for inclusion is licensed under
  Apache-2.0, with no additional terms. See `README.md` and `LICENSE`.
- **Check the license of anything you bring in before building on it.** Before adding a
  dependency, vendoring a file, or transcribing, porting, or generating code from someone
  else's work, read that artifact's own license: its file header, its `LICENSE`, its manifest's
  license field. A statement in a repository's README that all its code is dual-licensed does
  not cover files that repository vendored from elsewhere. A port, a transcription, generated
  code, or comments quoting a source are derivative works and inherit the source's license.
  Anything not compatible with Apache-2.0 must be raised with the maintainers before work
  starts. For Rust dependencies, `cargo license --avoid-dev-deps` lists what ships.

### AI Disclosure

If AI tools were used in preparing a commit, the contributor MUST include a
`Co-Authored-By:` trailer identifying the AI system. The contributor is the sole
responsible author; "the AI generated it" is not a justification during review.

## Build & Test Commands

The crate provides a backend on `target_arch = "aarch64"` and, in part, on
`target_arch = "x86_64"`: `add`, `sub`, and `from_mont` on every x86-64 target, and
`mul` and `square` on x86-64 with 64-bit pointers. It is empty on other targets. Nothing
is assembled at build time, so no C toolchain is needed. On all of those:

```sh
cargo build
cargo test                # the tests, with the debug assertions they check
cargo test --release      # the same tests on the release code
cargo clippy --all-targets -- -D warnings
cargo fmt -- --check
```

`scripts/ci.sh` runs every check CI runs, these and the formalization's, in one go; a check
whose tool is not installed is skipped with a note on how to install it.

On any other target, `cargo build` and `cargo test` must still succeed, with only the
inversion's tests over the portable blocks to run: that is what keeps a consumer's optional
dependency harmless off AArch64. A cfg-gated test that compiles out still reports success, so
CI counts the `#[test]` functions in the source and requires the run to report exactly that
many passed, in both profiles: all of them where the crate has a backend, and those of the
always-compiled modules elsewhere.

Documentation is a synthetic cross-platform build: `cfg(doc)` retains APIs that are unavailable
on the rustdoc host, while `doc(cfg(...))` renders their real architecture requirements. Because
`doc(cfg)` is still unstable, CI and docs.rs use nightly with `--cfg docsrs`. When adding another
backend, update these conditions and keep doc-only fallback bodies non-executable.

The crate is `no_std` with no dependencies, and CI proves both. The no_std check builds `core`
from source on a nightly toolchain instead of using the sysroot (`cargo +nightly build --release
-Z build-std=core,compiler_builtins --target aarch64-apple-darwin`), and the Ubuntu job asserts
that `cargo tree` lists nothing but the crate. Keep it that way; a dependency needs a reason
stated in its commit.

## The Lean Formalization

`lean/` is a Lake package (`PastaAsm`) with shared definitions and architecture-specific
submodules. Its instruction-level models contribute to assuring the routines' correctness; see
`lean/README.md` for the implemented coverage, trust story, theorems and their caveats, and how
those theorems are proven. All architectures use the same formalization pipeline; adding
another architecture extends its existing verification coverage and tooling. Build it from that
directory with the elan-managed `lake` for its `lean-toolchain` (a `lake` of another Lean
version corrupts the shared `.lake` cache):

```sh
cd lean
lake exe cache get          # Mathlib's prebuilt oleans, once
lake build --wfail          # warnings fail the build, as in CI
cd .. && lean/scripts/check.sh   # regenerate the transcription and check the skeletons
```

- **Every architecture's `Transcription.lean` and the shared `Vectors.lean` are generated** by
  `lean/scripts/gen.py` from the Rust `asm!` blocks and the reference vectors. Never edit them
  by hand; change the generator or its inputs and regenerate. Architecture-specific
  `Compositions.lean` mirrors the actual Rust compositions, not another backend's implementation.
  Shared `Compositions.lean` models common operand checks and the inversion's driver over a
  record of a backend's blocks; `Fields.lean` states the two fields' constants. A change on
  either side changes the other.
- **Every architecture's block proofs use generated, checked skeletons.** Generated skeleton
  lines in `Spec.lean` (or `Spec/*.lean`) are not hand-edited. Only theorem statements and
  `-- BEGIN ... -- END` annotation blocks are hand-written. Skeleton generation and `check_spec`
  must be available for each architecture, and the checker must require the unannotated proof
  to match the current generated skeleton. A changed block regenerates the skeleton; its
  annotations are then moved to their new places. Independently handwritten instruction traces
  or proof scripts are not a substitute for this synchronization check.
- **Architecture modules have consistent roles.** `Semantics` defines instruction behavior;
  `Transcription` contains generated block models; `Compositions` models Rust around those
  blocks; `Vectors` checks the backend's routines against the shared generated vectors by kernel
  evaluation; `Spec` proves block and composition correctness; `Entry` contains correctness
  **theorems** specializing those results to `PastaField` and the actual asserted operand
  contracts, not redundant value wrappers. Split per-block proof files belong under
  `<Architecture>/Spec/`, imported by its `Spec.lean`. Shared arithmetic, constants, and
  architecture-independent lemmas stay outside ISA modules.
- **Extend the shared generator pipeline.** `gen.py` owns CLI orchestration, binding storage,
  liveness, formatting, vector emission, SSA naming, and proof skeleton generation/checking.
  `asm_source.py` owns the self-contained Rust source parser and operand/output validation.
  `gen_<architecture>.py` backends supply ISA-specific operand, instruction, flag, and
  round-recognition rules through the shared machinery. Keep common code in `gen.py`, near
  the existing implementation; a separate general-purpose module needs a substantial,
  self-contained responsibility. Extend shared components rather than duplicating them.
  Reject unsupported syntax, uninitialized register/flag reads, and unmodeled memory accesses;
  test those rejection paths. For x86, CF and OF are independent and must not be conflated.

### Adding or extending an architecture

Before implementation, inspect the existing backend end to end and record a parity checklist:
semantics, operand/flag validation, mechanical transcription, repeated-round handling, Rust
compositions/contracts, generated vectors, generated proof skeletons, `check_spec`, block and
composition proofs, field-specialized entry theorems, root imports, and CI/export checks.
For each item identify the existing implementation, what can be shared, any genuine ISA-specific
difference, and the command that verifies it. A missing feature is unfinished work, not an
implicit exception. Obtain explicit maintainer agreement before omitting or weakening a feature;
do not change these instructions or coverage documentation to legitimize an omission.

- Cover every actual assembly block, including helper blocks, and every public composition.
  Factor repeated rounds when appropriate, with mechanical validation of the factoring;
  do not force identical helper structures onto different instruction schedules.
- Check the backend against the shared generated vectors for both Pasta fields, through
  `VectorCheck.lean`. Preserve vector provenance: AArch64 hardware outputs reused for x86 are
  cross-backend reference checks, not x86 hardware captures. Small handwritten examples do not
  replace the vector coverage.
- Match actual Rust assertions at both public and backend entry points. Report discrepancies
  rather than silently strengthening theorem assumptions or changing Rust to make a proof fit.
- `gen.py --check` and `scripts/check.sh` must check all architectures' transcriptions, vectors,
  and proof skeletons, and run generator validation tests. Register every completed module in
  the root import closure so the independent-kernel export includes it. A passing `lake build`
  does not validate files that the build never imports.
- Work in small self-contained commits, each building with `lake build --wfail` and passing
  the relevant generation/skeleton tests. Intermediate coverage may be incomplete, but must be
  explicitly tracked to completion; do not claim architecture support is complete until the
  parity checklist is satisfied. Report any unavailable independent-kernel check separately.
- During moves or refactoring, preserve existing comments, annotation markers, theorem bodies,
  and generated output unless a change is necessary for the requested implementation. Do not
  rewrite or drop explanatory text as incidental cleanup.
- **No `sorry`, no `native_decide`, no new axioms.** The nanoda re-check permits only the
  three standard axioms; concrete facts are checked by `decide +kernel`.

## Code Conventions

- **Preserve constant-time behaviour.** No secret-dependent branches or memory accesses in the
  blocks; the repeated-squaring loop branches only on its public count. Conditional reductions use
  `csel` after a full-width subtraction.
- **Operand contracts are stated on the entry points and checked by `debug_assert!`.** A
  change to a contract needs a change to the proofs that establish it.
- Commit messages: short title, body explaining the motivation for the change.
