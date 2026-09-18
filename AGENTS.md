# `pasta-asm` — Agent Guidelines

> This file is read by AI coding agents (Claude Code, GitHub Copilot, Cursor, Devin, etc.).
> It provides project context and contribution policies.

This crate provides assembly backends for the Pasta field arithmetic of `pasta_curves`. It
contains an AArch64 backend and an x86-64 backend: Montgomery multiplication and squaring as
inline `asm!` blocks, modular addition and subtraction, and a repeated-squaring chain and
conversion out of Montgomery form composed from them. It is low-level cryptographic code. Our
priorities are **correctness, constant-time behaviour, and performance**, in that order.

The routines are transcriptions of Supranational's Semolina v0.1.4 (see `README.md`). The
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

On any other target, `cargo build` and `cargo test` must still succeed, with nothing to test:
that is what keeps a consumer's optional dependency harmless off AArch64. A cfg-gated
test that compiles out still reports success, so CI counts the `#[test]` functions in the
source and requires the run to report exactly that many passed, in both profiles.

Documentation is a synthetic cross-platform build: `cfg(doc)` retains APIs that are unavailable
on the rustdoc host, while `doc(cfg(...))` renders their real architecture requirements. Because
`doc(cfg)` is still unstable, CI and docs.rs use nightly with `--cfg docsrs`. When adding another
backend, update these conditions and keep doc-only fallback bodies non-executable.

The crate is `no_std` with no dependencies, and CI proves both. The no_std check builds `core`
from source on a nightly toolchain instead of using the sysroot (`cargo +nightly build --release
-Z build-std=core,compiler_builtins --target aarch64-apple-darwin`), and the Ubuntu job asserts
that `cargo tree` lists nothing but the crate. Keep it that way; a dependency needs a reason
stated in its commit.

## Code Conventions

- **Preserve constant-time behaviour.** No secret-dependent branches or memory accesses in the
  blocks; the repeated-squaring loop branches only on its public count. Conditional reductions use
  `csel` after a full-width subtraction.
- **Operand contracts are stated on the entry points and checked by `debug_assert!`.** A
  change to a contract needs a change to the proofs that establish it.
- Commit messages: short title, body explaining the motivation for the change.
