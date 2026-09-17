// Copyright the pasta-aarch64-asm contributors.
// SPDX-License-Identifier: Apache-2.0

#![no_std]
#![cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
#![deny(missing_docs)]

//! AArch64 assembly backend for the Pasta fields.
//!
//! Montgomery multiplication and squaring are inline `asm!` blocks below. The
//! repeated-squaring chain and the conversion out of Montgomery form are
//! compositions of them, so the crate contains no assembled file and needs no
//! build script.
//!
//! The inline blocks are register-renamed transcriptions of the upstream
//! Semolina v0.1.4 routines (`mul_mont_pasta`, and the squaring loop body of
//! `sqr_n_mul_mont_pasta`), with rhs limbs and the modulus constants supplied
//! in registers instead of loaded from memory. The per-instruction comments
//! are carried over from the assembly routines they transcribe. Because the
//! operands are ordinary register operands and the blocks are declared
//! `options(pure, nomem, nostack)`, LLVM inlines the wrappers into callers and
//! keeps field values in registers between operations — there is no call,
//! pointer, or ABI-clobber traffic per field operation.
//!
//! The arithmetic relies on the shared Pasta modulus shape: `modulus[2] = 0`
//! and `modulus[3] = 2^62` (materialized inline as an immediate). Only
//! `modulus[0]`, `modulus[1]`, and `inv` vary between Fp and Fq, so a single
//! implementation serves both fields.
//!
//! Operand contract of `mul`: either `lhs` is canonical (below the modulus)
//! and `rhs` is any four-limb value, or `rhs` is canonical with each of its
//! limbs 1 to 3 at most `2^64 - 3` and `lhs` is any four-limb value. This is
//! the contract that the machine-checked proofs in `lean/` establish
//! (`mulMont_spec_of_lhs_lt` and `mulMont_spec_of_rhs_lt`). The input of
//! `square` must be canonical, a contract that the proofs do not cover. With
//! both operands canonical the routines are always safe. Outputs are
//! canonical. `mul` and `square` debug-assert their contracts, so that a
//! caller outside them fails loudly under test instead of silently.
//!
//! Two things can go wrong outside the contract. First, `mul` keeps a
//! five-limb accumulator (one word fewer than textbook CIOS), and the carry
//! chain folding in the high cross-products can wrap: its tail computes
//! `acc4 + high(lhs[3] * rhs_limb) + carry` with `acc4 <= 2`, which reaches
//! `2^64` only when `high(lhs[3] * rhs_limb) >= 2^64 - 3`. A canonical `lhs`
//! has `lhs[3] <= 2^62`, and a `rhs` limb at most `2^64 - 3` caps the high
//! product at `2^64 - 4`, so either condition alone rules the wrap out.
//! Whether the chain can wrap with a `rhs` limb of `2^64 - 2` is not settled
//! by the proofs. Second, `mul` keeps only four limbs of its final candidate
//! `(lhs * rhs + m * p) / R`, where `m < R` is the Montgomery cancellation
//! factor. The candidate is below `2p < R` whenever `lhs * rhs < R * p`, which
//! a canonical `lhs` (with `rhs < R`) or a canonical `rhs` (with `lhs < R`)
//! gives, so under either contract the dropped fifth limb is zero. With both
//! operands unreduced the candidate can reach `R`, and the result is then an
//! incorrect residue that still looks canonical.
//!
//! There are no branches and no memory accesses inside the blocks, and the
//! repeated-squaring loop branches only on its public count, so the code is
//! constant-time.
//!
//! # Availability
//!
//! The backend exists only for `target_arch = "aarch64"`. On every other
//! target this crate is empty, so a consumer gates its use on the same
//! `cfg` and falls back to portable arithmetic elsewhere. Nothing is assembled
//! at build time: the blocks are
//! compiled by the Rust toolchain, so no C toolchain is needed, and the crate
//! is `no_std` with no dependencies.
//!
//! # Provenance and license
//!
//! The routines are transcriptions of the Pasta Montgomery routines of
//! Supranational's [Semolina] v0.1.4, which are licensed under the Apache
//! License, Version 2.0 only; so is this crate. See the README for the
//! history of the transcription.
//!
//! [Semolina]: https://github.com/supranational/semolina

#[cfg(target_arch = "aarch64")]
mod aarch64;

mod unverified;

#[cfg(test)]
mod tests;

/// Four little-endian 64-bit limbs, least significant first: a field element
/// (in Montgomery form, or canonical after [`from_mont`]) or a modulus.
pub type Limbs = [u64; 4];

/// Whether `value < modulus` as little-endian 256-bit integers.
#[inline(always)]
fn is_canonical(value: &Limbs, modulus: &Limbs) -> bool {
    for i in (0..4).rev() {
        if value[i] != modulus[i] {
            return value[i] < modulus[i];
        }
    }
    false
}

/// Multiplies two Montgomery residues for a Pasta modulus. Either `lhs` is
/// canonical and `rhs` is any four-limb value, or `rhs` is canonical with
/// limbs 1 to 3 at most `2^64 - 3` and `lhs` is any four-limb value. The
/// contract is debug-asserted, and the crate docs say what goes wrong outside
/// it.
#[inline(always)]
pub fn mul(lhs: &Limbs, rhs: &Limbs, modulus: &Limbs, inv: u64) -> Limbs {
    debug_assert!(
        is_canonical(lhs, modulus)
            || (is_canonical(rhs, modulus) && rhs[1..].iter().all(|&limb| limb <= u64::MAX - 2)),
        "aarch64_asm::mul requires a canonical lhs, or a canonical rhs with limbs 1 to 3 at most \
         2^64 - 3"
    );

    #[cfg(target_arch = "aarch64")]
    {
        crate::aarch64::mul(lhs, rhs, modulus, inv)
    }

    #[cfg(target_arch = "x86_64")]
    crate::unverified::mul(lhs, rhs, modulus, inv)
}

/// Squares a canonical Montgomery residue for a Pasta modulus (the input's
/// canonicity is debug-asserted).
///
/// Currently only available for `aarch64`.
#[cfg(target_arch = "aarch64")]
#[inline(always)]
pub fn square(value: &Limbs, modulus: &Limbs, inv: u64) -> Limbs {
    debug_assert!(
        is_canonical(value, modulus),
        "aarch64_asm::square requires a canonical input"
    );

    #[cfg(target_arch = "aarch64")]
    {
        crate::aarch64::square(value, modulus, inv)
    }

    // No x86_64 semolina option because calling across the FFI is slower than
    // the portable Rust code.
}

/// Squares a canonical Montgomery residue `count` times, then multiplies the
/// result by the canonical Montgomery residue `rhs`. Each step is one of the
/// inline blocks, which the compiler inlines, so the accumulator stays in
/// registers throughout. A `count` of zero is just the multiplication.
#[inline]
pub fn sqr_n_mul(value: &Limbs, count: usize, rhs: &Limbs, modulus: &Limbs, inv: u64) -> Limbs {
    // When we have inline assembly, the Rust compiler can optimise this general code.
    #[cfg(target_arch = "aarch64")]
    {
        let mut acc = *value;
        for _ in 0..count {
            acc = square(&acc, modulus, inv);
        }
        mul(&acc, rhs, modulus, inv)
    }

    // When we have external assembly, we need to use a fused routine to see benefits
    // (otherwise the repeated FFI-crossing swamps any speedups).
    #[cfg(target_arch = "x86_64")]
    crate::unverified::sqr_n_mul(value, count, rhs, modulus, inv)
}

/// Inverts a canonical Montgomery residue for a Pasta modulus (the input's
/// canonicity is debug-asserted).
#[inline(always)]
pub fn invert(value: &Limbs, modulus: &Limbs, inv: u64) -> Limbs {
    debug_assert!(
        is_canonical(value, modulus),
        "pasta_asm::invert requires a canonical input"
    );

    crate::unverified::invert(value, modulus, inv)
}

/// Converts a Montgomery residue into its canonical integer,
/// `value * 2^-256 mod p`, as a Montgomery multiplication by one. Any
/// four-limb `value` is accepted: `1` is canonical with limbs 1 to 3 zero, so
/// it is a right operand inside the multiplication's contract for any left
/// operand (`mulMont_spec_of_rhs_lt` in `lean/`).
#[cfg(target_arch = "aarch64")]
#[inline]
pub fn from_mont(value: &Limbs, modulus: &Limbs, inv: u64) -> Limbs {
    // When we have inline assembly, the Rust compiler can optimise this general code.
    #[cfg(target_arch = "aarch64")]
    {
        mul(value, &[1, 0, 0, 0], modulus, inv)
    }

    // No x86_64 semolina option because calling across the FFI is slower than
    // the portable Rust code.
}
