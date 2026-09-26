// Copyright the pasta-asm contributors.
// SPDX-License-Identifier: Apache-2.0

#![no_std]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![deny(missing_docs)]

//! Assembly backends for the Pasta fields.
//!
//! # Availability
//!
//! The crate provides a backend for `target_arch = "aarch64"` and, in part,
//! for `target_arch = "x86_64"`. On x86-64, `add`, `sub`, and `from_mont`
//! are register-only. `mul`, `square`, and the routines built on them read
//! limbs through pointers, so they require 64-bit pointers; the x32 ABI's
//! 32-bit pointers would break them (see the module docs for why registers
//! alone cannot serve there). They also need, at run time, a CPU with BMI2
//! and ADX (MULX, ADCX/ADOX: Intel Broadwell / AMD Zen or newer); neither
//! is checked. `from_mont` uses MULX (BMI2) alone. Apple x86-64 targets are
//! excluded altogether: they reserve `rbp`, and so have fewer available
//! registers than the squaring blocks need.
//!
//! On every other target the crate is empty. It is also empty, on any
//! target, when the compiler is passed `--cfg pasta_asm_disable` (through
//! `RUSTFLAGS`, or `rustflags` in `.cargo/config.toml`), which is how to
//! build for old x86-64 CPUs without BMI2 and ADX. A consumer does not
//! repeat these conditions: it declares its uses of the crate under
//! [`if_supported!`] and its portable fallback under [`if_unsupported!`];
//! the first expands to its items exactly where the crate has a backend,
//! and the second exactly where it does not. [`BACKEND`] names the result.
//!
//! ```
//! mod portable {
//!     pub fn add(lhs: &[u64; 4], rhs: &[u64; 4], _modulus: &[u64; 4]) -> [u64; 4] {
//!         // A stand-in for the consumer's arithmetic that only has to work for the example.
//!         [lhs[0] + rhs[0], lhs[1] + rhs[1], lhs[2] + rhs[2], lhs[3] + rhs[3]]
//!     }
//! }
//! pasta_asm::if_supported! { use pasta_asm::add; }
//! pasta_asm::if_unsupported! { use portable::add; }
//!
//! let one = [1, 0, 0, 0];
//! let pallas = [0x992d30ed00000001, 0x224698fc094cf91b, 0, 0x4000000000000000];
//! let two = add(&one, &one, &pallas);
//! assert!(two == [2, 0, 0, 0]);
//! ```
//!
//! Two things follow for a direct consumer. The expansion is checked in the
//! consumer's crate, so the consumer declares the cfg as expected, in its
//! `Cargo.toml`:
//!
//! ```toml
//! [lints.rust]
//! unexpected_cfgs = { level = "warn", check-cfg = ['cfg(pasta_asm_disable)'] }
//! ```
//!
//! And a build that sets the flag sets it for rustdoc too (`RUSTDOCFLAGS`):
//! `cargo test` and `cargo doc` run rustdoc over the consumer's crate, which
//! expands the macros under rustdoc's flags, and against a crate built with
//! the flag the supported arm does not resolve.
//!
//! Nothing is assembled at build time: the blocks are compiled by the Rust
//! toolchain, so no C toolchain is needed, and the crate is `no_std` with
//! no dependencies.
//!
//! # Provenance and license
//!
//! The routines are transcriptions of the Pasta Montgomery routines of
//! Supranational's [Semolina] v0.1.4, which are licensed under the Apache
//! License, Version 2.0 only; so is this crate. See the README for the
//! history of the transcription.
//!
//! [Semolina]: https://github.com/supranational/semolina

/// Declares the items only where this crate has a backend.
///
/// The expansion carries the crate's own condition, the target and the absence of
/// `--cfg pasta_asm_disable`, so a consumer routes its arithmetic through the crate without
/// repeating it. The items are `use`s, functions, modules, or anything else in item position.
#[macro_export]
macro_rules! if_supported {
    ($($item:item)*) => { $(
        // Apple x86-64 targets reserve `rbp`, and so have fewer available registers than the
        // squaring blocks need.
        #[cfg(all(
            not(pasta_asm_disable),
            any(target_arch = "aarch64", all(target_arch = "x86_64", not(target_vendor = "apple")))
        ))]
        $item
    )* };
}

/// Declares the items only where this crate has no backend: the complement of
/// [`if_supported!`], for a consumer's portable fallback.
#[macro_export]
macro_rules! if_unsupported {
    ($($item:item)*) => { $(
        #[cfg(not(all(
            not(pasta_asm_disable),
            any(target_arch = "aarch64", all(target_arch = "x86_64", not(target_vendor = "apple")))
        )))]
        $item
    )* };
}

if_supported! {
    /// The backend in use, for diagnostics: `"aarch64"` or `"x86-64"` where the crate has one,
    /// and `"portable"` where it is empty and a consumer's fallback applies.
    pub const BACKEND: &str = if cfg!(target_arch = "aarch64") { "aarch64" } else { "x86-64" };

    #[cfg(any(target_arch = "aarch64", doc))]
    mod aarch64;

    #[cfg(any(target_arch = "x86_64", doc))]
    mod x86_64;

    // The tests use std only to catch the debug assertions they check, so a release test
    // build stays free of it.
    #[cfg(all(test, debug_assertions))]
    extern crate std;

    #[cfg(test)]
    mod tests;

    mod entry;
    pub use entry::*;
}

if_unsupported! {
    /// The backend in use, for diagnostics: `"aarch64"` or `"x86-64"` where the crate has one,
    /// and `"portable"` where it is empty and a consumer's fallback applies.
    pub const BACKEND: &str = "portable";
}
