// Copyright Supranational LLC (the Semolina v0.1.4 inversion routine).
// Copyright the pasta-asm contributors (the inline-assembly adaptation and Rust driver).
// SPDX-License-Identifier: Apache-2.0

//! Constant-time inversion for the x86-64 backend.
//!
//! The assembly kernels below are register-renamed transcriptions of helpers
//! from Semolina v0.1.4's `ct_inverse_mod_256-x86_64.pl`. The fixed-width
//! coefficient arithmetic and Rust driver adapt the upstream routine rather
//! than literally transcribing its complete instruction stream. The driver
//! runs fifteen 31-iteration approximation batches and one final 47-iteration
//! low-limb batch, for a fixed schedule of 512 iterations. Input-dependent
//! choices use `CMOV` in assembly or wrapping mask arithmetic in Rust; every
//! Rust loop has a public bound.
//!
//! Unlike upstream's memory-based helper interface, every block takes its limbs
//! in registers and declares `nomem`. Rust supplies the operands and manages the
//! intermediate arrays; LLVM may still emit loads or spills outside the blocks.
//! No pointer is passed into the assembly, so these blocks do not assume a
//! pointer width.
//!
//! Here `divstep` is local shorthand for one compare/swap/subtract/halve
//! binary-GCD iteration in Semolina's `__inner_loop_*` helpers, not a claim
//! that those helpers implement another algorithm's formally defined divstep.

use core::arch::asm;

use crate::Limbs;

// Coefficient updates use a 576-bit two's-complement representation. Limb 8 is
// the sign/excess word above the 512-bit value split consumed by normalization.
type Wide = [u64; 9];

/// Inverts a canonical Montgomery residue for a Pasta modulus.
///
/// The input is first taken out of Montgomery form. For nonzero input `x`,
/// Semolina's coefficient is congruent to `x^-1 * R^2` modulo the modulus;
/// Montgomery-reducing its 512-bit split yields the requested `x^-1 * R`.
/// The normalized high half is below `2p`, so one conditional subtraction
/// makes it canonical before adding it to the reduced low half. Zero maps
/// to zero.
///
/// # Safety contract
///
/// `value` must be canonical, `modulus` must be a Pasta modulus, and `inv` must
/// equal `-modulus[0]^-1 mod 2^64`, as required by the public entry point.
#[inline]
pub(crate) fn invert(value: &Limbs, modulus: &Limbs, inv: u64) -> Limbs {
    // The divstep relation is applied to the ordinary integer x. For nonzero x,
    // starting from x rather than xR makes the selected coefficient congruent
    // to x^-1 R^2 modulo p; REDC of its 512-bit split therefore produces the
    // desired Montgomery residue x^-1 R. The zero input remains zero.
    let mut a = crate::from_mont(value, modulus, inv);
    let mut b = *modulus;
    let mut u: Wide = [1, 0, 0, 0, 0, 0, 0, 0, 0];
    let mut v: Wide = [0; 9];

    for _ in 0..15 {
        let matrix = divsteps_31(&a, &b);
        let (next_a, f0, g0) = update_ab(&a, &b, matrix.f0, matrix.g0);
        let (next_b, f1, g1) = update_ab(&a, &b, matrix.f1, matrix.g1);
        let next_u = lincomb(&u, &v, f0, g0);
        let next_v = lincomb(&u, &v, f1, g1);
        a = next_a;
        b = next_b;
        u = next_u;
        v = next_v;
    }

    // The final exact 47 divsteps only need the second coefficient row.
    let matrix = divsteps_47(a[0], b[0]);
    let coefficient = normalize(lincomb(&u, &v, matrix.f1, matrix.g1), modulus);

    let low = [
        coefficient[0],
        coefficient[1],
        coefficient[2],
        coefficient[3],
    ];
    let high = [
        coefficient[4],
        coefficient[5],
        coefficient[6],
        coefficient[7],
    ];

    // REDC(low + high*R) = from_mont(low) + high (mod p). The inherited
    // final-coefficient bound for this fixed Pasta schedule places the selected
    // representative below (2*modulus) << 256. Thus high < 2*modulus, so one
    // subtraction suffices before the final addition of canonical residues.
    let low = crate::from_mont(&low, modulus, inv);
    let high = reduce_once(high, modulus);
    super::add(&low, &high, modulus)
}

/// One transition matrix produced by a 31-iteration approximation batch.
#[derive(Clone, Copy)]
struct Matrix {
    f0: i64,
    g0: i64,
    f1: i64,
    g1: i64,
}

/// Computes a 31-iteration transition matrix with Semolina's
/// `__ab_approximation_31_256` and `__inner_loop_31_256` kernels.
#[inline(always)]
fn divsteps_31(a: &Limbs, b: &Limbs) -> Matrix {
    let mut a0 = a[0];
    let mut a1 = a[1];
    let mut a2 = a[2];
    let a3 = a[3];
    let mut b0 = b[0];
    let b1 = b[1];
    let b2 = b[2];
    let b3 = b[3];

    // SAFETY: this is a register-only transcription of the cited Semolina
    // stages. Its only branch is the fixed 31-iteration loop; all decisions
    // derived from `a` or `b` use conditional moves.
    unsafe {
        asm!(
            // Pick the highest nonzero pair of limbs and retain the limb below
            // it. The resulting top-and-bottom-bit approximation drives the
            // batch; its path need not match steps on the full-width values.
            "mov {t}, {a3}",
            "or {t}, {b3}",
            "cmovz {a3}, {a2}",
            "cmovz {b3}, {b2}",
            "cmovz {a2}, {a1}",
            "cmovz {b2}, {b1}",
            "cmovz {a1}, {a0}",
            "cmovz {b1}, {b0}",
            "mov {t}, {a3}",
            "or {t}, {b3}",
            "cmovz {a3}, {a2}",
            "cmovz {b3}, {b2}",
            "cmovz {a2}, {a1}",
            "cmovz {b2}, {b1}",
            "mov {t}, {a3}",
            "or {t}, {b3}",
            "bsr rcx, {t}",
            "lea rcx, [rcx + 1]",
            "cmovz {a3}, {a0}",
            "cmovz {b3}, {b0}",
            "cmovz rcx, {t}",
            "neg rcx",
            "shld {a3}, {a2}, cl",
            "shld {b3}, {b2}, cl",
            "mov {t:e}, 0x7fffffff",
            "and {a0}, {t}",
            "and {b0}, {t}",
            "not {t}",
            "and {a3}, {t}",
            "and {b3}, {t}",
            "or {a0}, {a3}",
            "or {b0}, {b3}",

            // Packed, biased Thomas Pornin 31-divstep inner loop. Reuse the
            // dead approximation registers exactly as upstream uses its
            // scratch registers.
            "movabs {a1}, 0x7fffffff80000000",
            "movabs {a2}, 0x800000007fffffff",
            "movabs {a3}, 0x7fffffff7fffffff",
            "mov ecx, 31",
            "2:",
            "cmp {a0}, {b0}",
            "mov {b1}, {a0}",
            "mov {b2}, {b0}",
            "mov {b3}, {a1}",
            "mov {t}, {a2}",
            "cmovb {a0}, {b0}",
            "cmovb {b0}, {b1}",
            "cmovb {a1}, {a2}",
            "cmovb {a2}, {b3}",
            "sub {a0}, {b0}",
            "sub {a1}, {a2}",
            "add {a1}, {a3}",
            "test {b1}, 1",
            "cmovz {a0}, {b1}",
            "cmovz {b0}, {b2}",
            "cmovz {a1}, {b3}",
            "cmovz {a2}, {t}",
            "shr {a0}, 1",
            "add {a2}, {a2}",
            "sub {a2}, {a3}",
            "sub ecx, 1",
            "jnz 2b",

            // Unpack f0/g0 and f1/g1 and remove the common bias. Outputs are
            // placed in a0/a1 and b0/a2 respectively.
            "shr {a3}, 32",
            "mov {a0:e}, {a1:e}",
            "mov {b0:e}, {a2:e}",
            "shr {a1}, 32",
            "shr {a2}, 32",
            "sub {a0}, {a3}",
            "sub {a1}, {a3}",
            "sub {b0}, {a3}",
            "sub {a2}, {a3}",
            a0 = inout(reg) a0,
            a1 = inout(reg) a1,
            a2 = inout(reg) a2,
            a3 = inout(reg) a3 => _,
            b0 = inout(reg) b0,
            b1 = inout(reg) b1 => _,
            b2 = inout(reg) b2 => _,
            b3 = inout(reg) b3 => _,
            t = out(reg) _,
            out("rcx") _,
            options(pure, nomem, nostack),
        );
    }

    Matrix {
        f0: a0 as i64,
        g0: a1 as i64,
        f1: b0 as i64,
        g1: a2 as i64,
    }
}

/// Applies a matrix row to the GCD state in fixed-width two's-complement
/// arithmetic, divides the divisible result by `2^31`, and makes it nonnegative.
#[inline(always)]
fn update_ab(a: &Limbs, b: &Limbs, f: i64, g: i64) -> (Limbs, i64, i64) {
    let aa = [a[0], a[1], a[2], a[3], 0];
    let bb = [b[0], b[1], b[2], b[3], 0];
    let [mut r0, mut r1, mut r2, mut r3, r4] = lincomb(&aa, &bb, f, g);
    let mask: u64;
    let bit: u64;

    // SAFETY: register-only final shift and absolute-value transcription of
    // Semolina's `__smulq_256_n_shift_by_31`. Divisibility by 2^31 is an
    // invariant of the divstep matrix, and sign handling is mask based.
    unsafe {
        asm!(
            "shrd {r0}, {r1}, 31",
            "shrd {r1}, {r2}, 31",
            "shrd {r2}, {r3}, 31",
            "shrd {r3}, {r4}, 31",
            "mov {mask}, {r4}",
            "sar {mask}, 63",
            "mov {bit}, {mask}",
            "and {bit}, 1",
            "xor {r0}, {mask}",
            "xor {r1}, {mask}",
            "xor {r2}, {mask}",
            "xor {r3}, {mask}",
            "add {r0}, {bit}",
            "adc {r1}, 0",
            "adc {r2}, 0",
            "adc {r3}, 0",
            r0 = inout(reg) r0,
            r1 = inout(reg) r1,
            r2 = inout(reg) r2,
            r3 = inout(reg) r3,
            r4 = in(reg) r4,
            mask = lateout(reg) mask,
            bit = lateout(reg) bit,
            options(pure, nomem, nostack),
        );
    }

    let corrected_f = ((f as u64) ^ mask).wrapping_add(bit) as i64;
    let corrected_g = ((g as u64) ^ mask).wrapping_add(bit) as i64;
    ([r0, r1, r2, r3], corrected_f, corrected_g)
}

/// Computes `u*f + v*g` modulo `2^(64*N)`.
#[inline(always)]
fn lincomb<const N: usize>(u: &[u64; N], v: &[u64; N], f: i64, g: i64) -> [u64; N] {
    add_words(mul_signed(u, f), &mul_signed(v, g))
}

/// Adds two fixed-width integers modulo `2^(64*N)`.
#[inline(always)]
fn add_words<const N: usize>(mut lhs: [u64; N], rhs: &[u64; N]) -> [u64; N] {
    let mut carry = 0u64;
    for i in 0..N {
        // SAFETY: Rust performs the fixed-index array reads and write around
        // this `nomem` register-only block. The loop bound is public, and the
        // carry above the last limb is intentionally discarded.
        unsafe {
            asm!(
                "bt {carry}, 0",
                "adc {lhs}, {rhs}",
                "sbb {carry}, {carry}",
                "neg {carry}",
                lhs = inout(reg) lhs[i],
                rhs = in(reg) rhs[i],
                carry = inout(reg) carry,
                options(pure, nomem, nostack),
            );
        }
    }
    lhs
}

/// Multiplies a fixed-width signed two's-complement integer by a signed limb.
///
/// This adapts the arithmetic in Semolina's `__smulq_*x63` helpers: the sign of
/// the multiplier conditionally negates the multiplicand, after which one
/// unsigned `mul` chain produces the product modulo `2^(64*N)`.
#[inline(always)]
fn mul_signed<const N: usize>(value: &[u64; N], scalar: i64) -> [u64; N] {
    let scalar = scalar as u64;
    let sign = (scalar as i64 >> 63) as u64;
    let sign_bit = sign & 1;
    let magnitude = (scalar ^ sign).wrapping_add(sign_bit);

    let mut out = [0; N];
    let mut negate_carry = sign_bit;
    let mut product_carry = 0u64;

    for i in 0..N {
        let limb = value[i];
        let next_negate_carry: u8;
        let low: u64;
        let high: u64;
        // SAFETY: Rust performs the fixed-index input read and output write
        // around this `nomem` register-only block. The loop bound and addresses
        // are public; the assembly contains no input-dependent branch.
        unsafe {
            asm!(
                "xor {limb}, {sign}",
                "add {limb}, {negate_carry}",
                "setc {next_negate_carry}",
                "mov rax, {limb}",
                "mul {magnitude}",
                "add rax, {product_carry}",
                "adc rdx, 0",
                limb = inout(reg) limb => _,
                sign = in(reg) sign,
                negate_carry = in(reg) negate_carry,
                next_negate_carry = out(reg_byte) next_negate_carry,
                magnitude = in(reg) magnitude,
                product_carry = in(reg) product_carry,
                out("rax") low,
                out("rdx") high,
                options(pure, nomem, nostack),
            );
        }
        out[i] = low;
        negate_carry = u64::from(next_negate_carry);
        product_carry = high;
    }

    out
}

/// Returns the second row after the final 47 low-limb iterations of Semolina's
/// `__inner_loop_62_256` kernel.
///
/// For nonzero input, the GCD state now fits in the supplied low limbs. For zero
/// input, `a = 0` and `b = p`; the second row still selects a zero coefficient,
/// preserving the zero-to-zero result.
#[inline(always)]
fn divsteps_47(a: u64, b: u64) -> Matrix {
    let mut f0 = 1u64;
    let mut g0 = 0u64;
    let mut f1 = 0u64;
    let mut g1 = 1u64;

    // SAFETY: register-only transcription. The only branch has the public,
    // fixed count 47; input-dependent choices use conditional moves.
    unsafe {
        asm!(
            "mov {count:e}, 47",
            "2:",
            "xor {t0:e}, {t0:e}",
            "test {a}, 1",
            "mov {t1}, {b}",
            "cmovnz {t0}, {b}",
            "sub {t1}, {a}",
            "mov {t2}, {a}",
            "sub {a}, {t0}",
            "cmovc {a}, {t1}",
            "cmovc {b}, {t2}",
            "mov {t0}, {f0}",
            "cmovc {f0}, {f1}",
            "cmovc {f1}, {t0}",
            "mov {t1}, {g0}",
            "cmovc {g0}, {g1}",
            "cmovc {g1}, {t1}",
            "xor {t0:e}, {t0:e}",
            "xor {t1:e}, {t1:e}",
            "shr {a}, 1",
            "test {t2}, 1",
            "cmovnz {t0}, {f1}",
            "cmovnz {t1}, {g1}",
            "add {f1}, {f1}",
            "add {g1}, {g1}",
            "sub {f0}, {t0}",
            "sub {g0}, {t1}",
            "sub {count:e}, 1",
            "jnz 2b",
            a = inout(reg) a => _,
            b = inout(reg) b => _,
            f0 = inout(reg) f0,
            g0 = inout(reg) g0,
            f1 = inout(reg) f1,
            g1 = inout(reg) g1,
            t0 = out(reg) _,
            t1 = out(reg) _,
            t2 = out(reg) _,
            count = out(reg) _,
            options(pure, nomem, nostack),
        );
    }

    Matrix {
        f0: f0 as i64,
        g0: g0 as i64,
        f1: f1 as i64,
        g1: g1 as i64,
    }
}

/// Applies Semolina's final adjustment and returns the coefficient's low and
/// high 256-bit halves.
///
/// For this fixed Pasta schedule, the signed coefficient's ninth limb is
/// `-1`, `0`, or `1`. Semolina's `modx` is `2 * modulus`, the left-aligned
/// 255-bit Pasta modulus. Adding or subtracting `modx << 256` leaves the low
/// half unchanged and selects the representative in
/// `[0, (2 * modulus) << 256)` required by the final split reduction.
#[inline(always)]
fn normalize(mut value: [u64; 9], modulus: &Limbs) -> [u64; 8] {
    let modx = [
        modulus[0] << 1,
        (modulus[1] << 1) | (modulus[0] >> 63),
        (modulus[2] << 1) | (modulus[1] >> 63),
        (modulus[3] << 1) | (modulus[2] >> 63),
    ];
    let [mut h0, mut h1, mut h2, mut h3] = [value[4], value[5], value[6], value[7]];
    let mut excess = value[8];
    let [m0, m1, m2, m3] = modx;

    // SAFETY: Rust has already read the public fixed array indices; this `nomem`
    // block performs only register arithmetic. Its mask conditionally adds the
    // aligned modulus when the coefficient is negative.
    unsafe {
        asm!(
            "mov {mask}, {excess}",
            "sar {mask}, 63",
            "and {m0}, {mask}",
            "and {m1}, {mask}",
            "and {m2}, {mask}",
            "and {m3}, {mask}",
            "add {h0}, {m0}",
            "adc {h1}, {m1}",
            "adc {h2}, {m2}",
            "adc {h3}, {m3}",
            "adc {excess}, 0",
            h0 = inout(reg) h0,
            h1 = inout(reg) h1,
            h2 = inout(reg) h2,
            h3 = inout(reg) h3,
            excess = inout(reg) excess,
            m0 = inout(reg) m0 => _,
            m1 = inout(reg) m1 => _,
            m2 = inout(reg) m2 => _,
            m3 = inout(reg) m3 => _,
            mask = out(reg) _,
            options(pure, nomem, nostack),
        );
    }

    let [m0, m1, m2, m3] = modx;
    // SAFETY: Rust has already read the public fixed array indices; this `nomem`
    // block performs only register arithmetic. If the `-1`, `0`, or `1` excess
    // remains, the upstream `neg; or; sar` masks add or subtract one aligned
    // modulus without data-dependent flow.
    unsafe {
        asm!(
            "mov {nonzero_mask}, {excess}",
            "mov {negative_excess}, {excess}",
            "neg {negative_excess}",
            "or {nonzero_mask}, {negative_excess}",
            "sar {negative_excess}, 63",
            "and {m0}, {nonzero_mask}",
            "and {m1}, {nonzero_mask}",
            "and {m2}, {nonzero_mask}",
            "and {m3}, {nonzero_mask}",
            "xor {m0}, {negative_excess}",
            "xor {zero:e}, {zero:e}",
            "xor {m1}, {negative_excess}",
            "sub {zero}, {negative_excess}",
            "xor {m2}, {negative_excess}",
            "xor {m3}, {negative_excess}",
            "add {m0}, {zero}",
            "adc {m1}, 0",
            "adc {m2}, 0",
            "adc {m3}, 0",
            "add {h0}, {m0}",
            "adc {h1}, {m1}",
            "adc {h2}, {m2}",
            "adc {h3}, {m3}",
            h0 = inout(reg) h0,
            h1 = inout(reg) h1,
            h2 = inout(reg) h2,
            h3 = inout(reg) h3,
            m0 = inout(reg) m0 => _,
            m1 = inout(reg) m1 => _,
            m2 = inout(reg) m2 => _,
            m3 = inout(reg) m3 => _,
            excess = in(reg) excess,
            nonzero_mask = out(reg) _,
            negative_excess = out(reg) _,
            zero = out(reg) _,
            options(pure, nomem, nostack),
        );
    }

    value[4] = h0;
    value[5] = h1;
    value[6] = h2;
    value[7] = h3;
    [
        value[0], value[1], value[2], value[3], value[4], value[5], value[6], value[7],
    ]
}

/// Conditionally subtracts the modulus to canonicalize a value below twice it.
#[inline(always)]
fn reduce_once(mut value: Limbs, modulus: &Limbs) -> Limbs {
    let p0 = modulus[0];
    let p1 = modulus[1];
    let p3 = modulus[3];
    // SAFETY: register-only subtraction and conditional addition. The caller's
    // inherited coefficient bound guarantees that one subtraction is enough.
    unsafe {
        asm!(
            "sub {r0}, {p0}",
            "sbb {r1}, {p1}",
            "sbb {r2}, 0",
            "sbb {r3}, {p3}",
            "mov {zero:e}, 0",
            "cmovnc {p0}, {zero}",
            "cmovnc {p1}, {zero}",
            "cmovnc {p3}, {zero}",
            "add {r0}, {p0}",
            "adc {r1}, {p1}",
            "adc {r2}, 0",
            "adc {r3}, {p3}",
            r0 = inout(reg) value[0],
            r1 = inout(reg) value[1],
            r2 = inout(reg) value[2],
            r3 = inout(reg) value[3],
            p0 = inout(reg) p0 => _,
            p1 = inout(reg) p1 => _,
            p3 = inout(reg) p3 => _,
            zero = out(reg) _,
            options(pure, nomem, nostack),
        );
    }
    value
}
