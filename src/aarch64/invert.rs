// Copyright Supranational LLC (the Semolina v0.1.4 inversion and REDC routines).
// Copyright the pasta-asm contributors (the inline-assembly adaptation and Rust driver).
// SPDX-License-Identifier: Apache-2.0

//! Constant-time inversion for the AArch64 backend.
//!
//! The assembly kernels below are register-renamed transcriptions of helpers
//! from Semolina v0.1.4's `ct_inverse_mod_256-armv8.pl` and
//! `pasta_mul-armv8.pl`. The fixed-width coefficient arithmetic and Rust driver
//! adapt the upstream routine rather than literally transcribing its complete
//! instruction stream. The driver
//! runs fifteen 31-iteration approximation batches and one final 47-iteration
//! low-limb batch, for a fixed schedule of 512 iterations. Input-dependent
//! selections in the assembly use `CSEL`; Rust controls only public loop bounds.
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
/// For nonzero Montgomery input `xR`, Semolina's coefficient is congruent to
/// `(xR)^-1 * R^2 = x^-1 * R` modulo the modulus. REDC removes one factor of
/// `R`; multiplying by `R^2 mod p` restores the requested Montgomery residue
/// `x^-1 * R`. Zero maps to zero.
///
/// # Safety contract
///
/// `value` must be canonical, `modulus` must be a Pasta modulus, and `inv` must
/// equal `-modulus[0]^-1 mod 2^64`, as required by the public entry point.
#[inline]
pub(crate) fn invert(value: &Limbs, modulus: &Limbs, inv: u64) -> Limbs {
    let mut a = *value;
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

    let (f1, g1) = divsteps_47(a[0], b[0]);
    let coefficient = lincomb(&u, &v, f1, g1);
    let (low, high) = normalize_coefficient(&coefficient, modulus);
    let reduced = redc(&low, &high, modulus, inv);
    let rr = crate::montgomery_r2(modulus);

    // `redc_mont_pasta`'s single subtraction does not make its output canonical
    // for every 512-bit input. `rr` is canonical and each of its upper limbs is
    // far below `2^64 - 3`, so `mul` accepts the unrestricted `reduced` lhs and
    // returns the canonical Montgomery result without strengthening REDC's range.
    super::mul(&reduced, &rr, modulus, inv)
}

/// One transition matrix produced by a 31-iteration approximation batch.
#[derive(Clone, Copy)]
struct Matrix {
    f0: i64,
    g0: i64,
    f1: i64,
    g1: i64,
}

/// Computes a 31-iteration transition matrix from approximations of `a` and `b`.
#[inline(always)]
fn divsteps_31(a: &Limbs, b: &Limbs) -> Matrix {
    let [a0, a1, a2, a3] = *a;
    let [b0, b1, b2, b3] = *b;
    let (f0, g0, f1, g1): (i64, i64, i64, i64);

    // SAFETY: register-only arithmetic. The backward branch has the public,
    // fixed count 31; every choice derived from a or b uses CSEL.
    unsafe {
        asm!(
            // __ab_approximation_31_256: combine the low 31 bits with an
            // aligned window from the high end, as required by the batched
            // approximation algorithm. Its path need not match 31 divsteps on
            // the full-width values.
            "orr {t0}, {a3}, {b3}",
            "cmp {t0}, #0",
            "csel {a3}, {a3}, {a2}, ne",
            "csel {b3}, {b3}, {b2}, ne",
            "csel {a2}, {a2}, {a1}, ne",
            "orr {t0}, {a3}, {b3}",
            "csel {b2}, {b2}, {b1}, ne",

            "cmp {t0}, #0",
            "csel {a3}, {a3}, {a2}, ne",
            "csel {b3}, {b3}, {b2}, ne",
            "csel {a2}, {a2}, {a0}, ne",
            "orr {t0}, {a3}, {b3}",
            "csel {b2}, {b2}, {b0}, ne",

            "clz {t0}, {t0}",
            "cmp {t0}, #64",
            "csel {t0}, {t0}, xzr, ne",
            "csel {a3}, {a3}, {a2}, ne",
            "csel {b3}, {b3}, {b2}, ne",
            "neg {t1}, {t0}",

            "lslv {a3}, {a3}, {t0}",
            "lslv {b3}, {b3}, {t0}",
            "lsrv {a2}, {a2}, {t1}",
            "lsrv {b2}, {b2}, {t1}",
            "and {a2}, {a2}, {t1}, asr #6",
            "and {b2}, {b2}, {t1}, asr #6",
            "orr {a3}, {a3}, {a2}",
            "orr {b3}, {b3}, {b2}",
            "bfxil {a3}, {a0}, #0, #31",
            "bfxil {b3}, {b0}, #0, #31",

            // __inner_loop_31_256. The two matrix rows are packed as biased
            // 32-bit halves exactly as in the upstream helper.
            "2:",
            "sbfx {t3}, {a3}, #0, #1",
            "sub {cnt}, {cnt}, #1",
            "and {t0}, {b3}, {t3}",
            "sub {t1}, {b3}, {a3}",
            "subs {t2}, {a3}, {t0}",
            "mov {t0}, {fg1}",
            "csel {b3}, {b3}, {a3}, hs",
            "csel {a3}, {t2}, {t1}, hs",
            "csel {fg1}, {fg1}, {fg0}, hs",
            "csel {fg0}, {fg0}, {t0}, hs",
            "lsr {a3}, {a3}, #1",
            "and {t0}, {fg1}, {t3}",
            "and {t1}, {bias}, {t3}",
            "sub {fg0}, {fg0}, {t0}",
            "add {fg1}, {fg1}, {fg1}",
            "add {fg0}, {fg0}, {t1}",
            "sub {fg1}, {fg1}, {bias}",
            "cbnz {cnt}, 2b",

            "ubfx {bias}, {bias}, #0, #32",
            "ubfx {f0}, {fg0}, #0, #32",
            "ubfx {g0}, {fg0}, #32, #32",
            "ubfx {f1}, {fg1}, #0, #32",
            "ubfx {g1}, {fg1}, #32, #32",
            "sub {f0}, {f0}, {bias}",
            "sub {g0}, {g0}, {bias}",
            "sub {f1}, {f1}, {bias}",
            "sub {g1}, {g1}, {bias}",
            a0 = inout(reg) a0 => _,
            a1 = inout(reg) a1 => _,
            a2 = inout(reg) a2 => _,
            a3 = inout(reg) a3 => _,
            b0 = inout(reg) b0 => _,
            b1 = inout(reg) b1 => _,
            b2 = inout(reg) b2 => _,
            b3 = inout(reg) b3 => _,
            fg0 = inout(reg) 0x7fff_ffff_8000_0000_u64 => _,
            fg1 = inout(reg) 0x8000_0000_7fff_ffff_u64 => _,
            bias = inout(reg) 0x7fff_ffff_7fff_ffff_u64 => _,
            cnt = inout(reg) 31_u64 => _,
            f0 = out(reg) f0,
            g0 = out(reg) g0,
            f1 = out(reg) f1,
            g1 = out(reg) g1,
            t0 = out(reg) _,
            t1 = out(reg) _,
            t2 = out(reg) _,
            t3 = out(reg) _,
            options(pure, nomem, nostack),
        );
    }

    Matrix { f0, g0, f1, g1 }
}

/// Applies a matrix row to the GCD state in fixed-width two's-complement
/// arithmetic, divides the divisible result by `2^31`, and makes it nonnegative.
#[inline(always)]
fn update_ab(a: &Limbs, b: &Limbs, mut f: i64, mut g: i64) -> (Limbs, i64, i64) {
    let [mut a0, mut a1, mut a2, mut a3] = *a;
    let [b0, b1, b2, b3] = *b;

    // SAFETY: direct register-only transcription of
    // __smul_256_n_shift_by_31. Sign handling is mask based.
    unsafe {
        asm!(
            // Signed a*f into a0..a3:t3.
            "asr {t5}, {f}, #63",
            "eor {t6}, {f}, {t5}",
            "eor {a0}, {a0}, {t5}",
            "sub {t6}, {t6}, {t5}",
            "eor {a1}, {a1}, {t5}",
            "adds {a0}, {a0}, {t5}, lsr #63",
            "eor {a2}, {a2}, {t5}",
            "adcs {a1}, {a1}, xzr",
            "eor {a3}, {a3}, {t5}",
            "umulh {t0}, {a0}, {t6}",
            "adcs {a2}, {a2}, xzr",
            "umulh {t1}, {a1}, {t6}",
            "adc {a3}, {a3}, xzr",
            "umulh {t2}, {a2}, {t6}",
            "and {t5}, {t5}, {t6}",
            "umulh {t3}, {a3}, {t6}",
            "neg {t5}, {t5}",
            "mul {a0}, {a0}, {t6}",
            "mul {a1}, {a1}, {t6}",
            "mul {a2}, {a2}, {t6}",
            "adds {a1}, {a1}, {t0}",
            "mul {a3}, {a3}, {t6}",
            "adcs {a2}, {a2}, {t1}",
            "adcs {a3}, {a3}, {t2}",
            "adc {t3}, {t3}, {t5}",

            // Signed b*g into b0..b3:t4.
            "asr {t5}, {g}, #63",
            "eor {t6}, {g}, {t5}",
            "eor {b0}, {b0}, {t5}",
            "sub {t6}, {t6}, {t5}",
            "eor {b1}, {b1}, {t5}",
            "adds {b0}, {b0}, {t5}, lsr #63",
            "eor {b2}, {b2}, {t5}",
            "adcs {b1}, {b1}, xzr",
            "eor {b3}, {b3}, {t5}",
            "umulh {t0}, {b0}, {t6}",
            "adcs {b2}, {b2}, xzr",
            "umulh {t1}, {b1}, {t6}",
            "adc {b3}, {b3}, xzr",
            "umulh {t2}, {b2}, {t6}",
            "and {t5}, {t5}, {t6}",
            "umulh {t4}, {b3}, {t6}",
            "neg {t5}, {t5}",
            "mul {b0}, {b0}, {t6}",
            "mul {b1}, {b1}, {t6}",
            "mul {b2}, {b2}, {t6}",
            "adds {b1}, {b1}, {t0}",
            "mul {b3}, {b3}, {t6}",
            "adcs {b2}, {b2}, {t1}",
            "adcs {b3}, {b3}, {t2}",
            "adc {t4}, {t4}, {t5}",

            "adds {a0}, {a0}, {b0}",
            "adcs {a1}, {a1}, {b1}",
            "adcs {a2}, {a2}, {b2}",
            "adcs {a3}, {a3}, {b3}",
            "adc {b0}, {t3}, {t4}",

            "extr {a0}, {a1}, {a0}, #31",
            "extr {a1}, {a2}, {a1}, #31",
            "extr {a2}, {a3}, {a2}, #31",
            "asr {t4}, {b0}, #63",
            "extr {a3}, {b0}, {a3}, #31",

            "eor {a0}, {a0}, {t4}",
            "eor {a1}, {a1}, {t4}",
            "adds {a0}, {a0}, {t4}, lsr #63",
            "eor {a2}, {a2}, {t4}",
            "adcs {a1}, {a1}, xzr",
            "eor {a3}, {a3}, {t4}",
            "adcs {a2}, {a2}, xzr",
            "adc {a3}, {a3}, xzr",

            "eor {f}, {f}, {t4}",
            "eor {g}, {g}, {t4}",
            "sub {f}, {f}, {t4}",
            "sub {g}, {g}, {t4}",
            a0 = inout(reg) a0,
            a1 = inout(reg) a1,
            a2 = inout(reg) a2,
            a3 = inout(reg) a3,
            b0 = inout(reg) b0 => _,
            b1 = inout(reg) b1 => _,
            b2 = inout(reg) b2 => _,
            b3 = inout(reg) b3 => _,
            f = inout(reg) f,
            g = inout(reg) g,
            t0 = out(reg) _,
            t1 = out(reg) _,
            t2 = out(reg) _,
            t3 = out(reg) _,
            t4 = out(reg) _,
            t5 = out(reg) _,
            t6 = out(reg) _,
            options(pure, nomem, nostack),
        );
    }

    ([a0, a1, a2, a3], f, g)
}

/// Computes `u*f + v*g` modulo `2^576`.
#[inline(always)]
fn lincomb(u: &Wide, v: &Wide, f: i64, g: i64) -> Wide {
    add_words(&mul_signed(u, f), &mul_signed(v, g))
}

/// Adds two 576-bit values modulo `2^576`.
#[inline(always)]
fn add_words(lhs: &Wide, rhs: &Wide) -> Wide {
    let (o0, o1, o2, o3, o4, o5, o6, o7, o8): (u64, u64, u64, u64, u64, u64, u64, u64, u64);

    // SAFETY: Rust reads the fixed-index limbs into register operands. The
    // assembly has no memory access; its straight-line carry chain discards
    // overflow above bit 575. Early-clobber inout operands keep every still-live
    // right-hand limb distinct from the accumulating left-hand limbs.
    unsafe {
        asm!(
            "adds {o0}, {o0}, {r0}",
            "adcs {o1}, {o1}, {r1}",
            "adcs {o2}, {o2}, {r2}",
            "adcs {o3}, {o3}, {r3}",
            "adcs {o4}, {o4}, {r4}",
            "adcs {o5}, {o5}, {r5}",
            "adcs {o6}, {o6}, {r6}",
            "adcs {o7}, {o7}, {r7}",
            "adc {o8}, {o8}, {r8}",
            o0 = inout(reg) lhs[0] => o0,
            o1 = inout(reg) lhs[1] => o1,
            o2 = inout(reg) lhs[2] => o2,
            o3 = inout(reg) lhs[3] => o3,
            o4 = inout(reg) lhs[4] => o4,
            o5 = inout(reg) lhs[5] => o5,
            o6 = inout(reg) lhs[6] => o6,
            o7 = inout(reg) lhs[7] => o7,
            o8 = inout(reg) lhs[8] => o8,
            r0 = in(reg) rhs[0],
            r1 = in(reg) rhs[1],
            r2 = in(reg) rhs[2],
            r3 = in(reg) rhs[3],
            r4 = in(reg) rhs[4],
            r5 = in(reg) rhs[5],
            r6 = in(reg) rhs[6],
            r7 = in(reg) rhs[7],
            r8 = in(reg) rhs[8],
            options(pure, nomem, nostack),
        );
    }

    [o0, o1, o2, o3, o4, o5, o6, o7, o8]
}

/// Multiplies a signed two's-complement value by a signed scalar modulo `2^576`.
#[inline(always)]
fn mul_signed(value: &Wide, scalar: i64) -> Wide {
    let (o0, o1, o2, o3, o4, o5, o6, o7, o8): (u64, u64, u64, u64, u64, u64, u64, u64, u64);

    // SAFETY: Rust reads the fixed-index limbs into inout register operands.
    // The assembly has no memory access. Early-clobber scratch outputs cannot
    // overlap the input limbs; the scalar sign is converted to a mask, and
    // overflow above bit 575 is intentionally dropped.
    unsafe {
        asm!(
            "asr {sign}, {scalar}, #63",
            "eor {mag}, {scalar}, {sign}",
            "sub {mag}, {mag}, {sign}",

            "eor {o0}, {o0}, {sign}",
            "eor {o1}, {o1}, {sign}",
            "eor {o2}, {o2}, {sign}",
            "eor {o3}, {o3}, {sign}",
            "eor {o4}, {o4}, {sign}",
            "eor {o5}, {o5}, {sign}",
            "eor {o6}, {o6}, {sign}",
            "eor {o7}, {o7}, {sign}",
            "eor {o8}, {o8}, {sign}",
            "adds {o0}, {o0}, {sign}, lsr #63",
            "adcs {o1}, {o1}, xzr",
            "adcs {o2}, {o2}, xzr",
            "adcs {o3}, {o3}, xzr",
            "adcs {o4}, {o4}, xzr",
            "adcs {o5}, {o5}, xzr",
            "adcs {o6}, {o6}, xzr",
            "adcs {o7}, {o7}, xzr",
            "adc {o8}, {o8}, xzr",

            "umulh {carry}, {o0}, {mag}",
            "mul {o0}, {o0}, {mag}",
            "umulh {hi}, {o1}, {mag}",
            "mul {o1}, {o1}, {mag}",
            "adds {o1}, {o1}, {carry}",
            "adc {carry}, {hi}, xzr",
            "umulh {hi}, {o2}, {mag}",
            "mul {o2}, {o2}, {mag}",
            "adds {o2}, {o2}, {carry}",
            "adc {carry}, {hi}, xzr",
            "umulh {hi}, {o3}, {mag}",
            "mul {o3}, {o3}, {mag}",
            "adds {o3}, {o3}, {carry}",
            "adc {carry}, {hi}, xzr",
            "umulh {hi}, {o4}, {mag}",
            "mul {o4}, {o4}, {mag}",
            "adds {o4}, {o4}, {carry}",
            "adc {carry}, {hi}, xzr",
            "umulh {hi}, {o5}, {mag}",
            "mul {o5}, {o5}, {mag}",
            "adds {o5}, {o5}, {carry}",
            "adc {carry}, {hi}, xzr",
            "umulh {hi}, {o6}, {mag}",
            "mul {o6}, {o6}, {mag}",
            "adds {o6}, {o6}, {carry}",
            "adc {carry}, {hi}, xzr",
            "umulh {hi}, {o7}, {mag}",
            "mul {o7}, {o7}, {mag}",
            "adds {o7}, {o7}, {carry}",
            "adc {carry}, {hi}, xzr",
            "mul {o8}, {o8}, {mag}",
            "add {o8}, {o8}, {carry}",
            scalar = in(reg) scalar,
            o0 = inout(reg) value[0] => o0,
            o1 = inout(reg) value[1] => o1,
            o2 = inout(reg) value[2] => o2,
            o3 = inout(reg) value[3] => o3,
            o4 = inout(reg) value[4] => o4,
            o5 = inout(reg) value[5] => o5,
            o6 = inout(reg) value[6] => o6,
            o7 = inout(reg) value[7] => o7,
            o8 = inout(reg) value[8] => o8,
            sign = out(reg) _,
            mag = out(reg) _,
            carry = out(reg) _,
            hi = out(reg) _,
            options(pure, nomem, nostack),
        );
    }

    [o0, o1, o2, o3, o4, o5, o6, o7, o8]
}

/// Returns the second row after the final 47 low-limb iterations.
///
/// For nonzero input, the GCD state now fits in the supplied low limbs. For zero
/// input, `a = 0` and `b = p`; the second row still selects a zero coefficient,
/// preserving the zero-to-zero result.
#[inline(always)]
fn divsteps_47(a: u64, b: u64) -> (i64, i64) {
    let (f1, g1): (i64, i64);

    // SAFETY: direct register-only transcription of `__inner_loop_62_256`,
    // specialized to its public count of 47. Input-dependent choices use CSEL.
    unsafe {
        asm!(
            "2:",
            "sbfx {odd}, {a}, #0, #1",
            "sub {cnt}, {cnt}, #1",
            "and {t0}, {b}, {odd}",
            "sub {t1}, {b}, {a}",
            "subs {t2}, {a}, {t0}",
            "mov {t0}, {f0}",
            "csel {b}, {b}, {a}, hs",
            "csel {a}, {t2}, {t1}, hs",
            "mov {t1}, {g0}",
            "csel {f0}, {f0}, {f1}, hs",
            "csel {f1}, {f1}, {t0}, hs",
            "csel {g0}, {g0}, {g1}, hs",
            "csel {g1}, {g1}, {t1}, hs",
            "lsr {a}, {a}, #1",
            "and {t0}, {f1}, {odd}",
            "and {t1}, {g1}, {odd}",
            "add {f1}, {f1}, {f1}",
            "add {g1}, {g1}, {g1}",
            "sub {f0}, {f0}, {t0}",
            "sub {g0}, {g0}, {t1}",
            "cbnz {cnt}, 2b",
            a = inout(reg) a => _,
            b = inout(reg) b => _,
            cnt = inout(reg) 47_u64 => _,
            f0 = inout(reg) 1_i64 => _,
            g0 = inout(reg) 0_i64 => _,
            f1 = inout(reg) 0_i64 => f1,
            g1 = inout(reg) 1_i64 => g1,
            odd = out(reg) _,
            t0 = out(reg) _,
            t1 = out(reg) _,
            t2 = out(reg) _,
            options(pure, nomem, nostack),
        );
    }

    (f1, g1)
}

/// Applies Semolina's final adjustment and returns the coefficient's low and
/// high 256-bit halves.
///
/// For this fixed Pasta schedule, the signed coefficient's ninth limb is
/// `-1`, `0`, or `1`. Semolina's `modx` is `2 * modulus`, the left-aligned
/// 255-bit Pasta modulus. Adding or subtracting `modx << 256` removes the
/// signed excess while leaving the low half unchanged. The returned high half
/// is an arbitrary four-limb value below `R = 2^256`.
#[inline(always)]
fn normalize_coefficient(value: &Wide, modulus: &Limbs) -> (Limbs, Limbs) {
    let low = [value[0], value[1], value[2], value[3]];
    let (w4, w5, w6, w7): (u64, u64, u64, u64);

    // SAFETY: Rust reads the fixed-index limbs into register operands; the low
    // half is unchanged and stays outside the block. There is no memory access.
    // Early-clobber scratch outputs cannot overlap the input limbs. Straight-line
    // mask arithmetic adds the aligned modulus to a negative coefficient, then
    // uses the remaining `-1`, `0`, or `1` excess to add or subtract it once.
    unsafe {
        asm!(
            "asr {sign}, {w8}, #63",

            // modulus << 257 occupies limbs 4..7 because Pasta moduli have
            // bit length 255. These are the upstream `modx` limbs.
            "lsl {m4}, {p0}, #1",
            "lsr {tmp}, {p0}, #63",
            "orr {m5}, {tmp}, {p1}, lsl #1",
            "lsr {m6}, {p1}, #63",
            "mov {m7}, #0x8000000000000000",

            // Add the aligned modulus if the signed coefficient is negative.
            "and {tmp}, {m4}, {sign}",
            "adds {w4}, {w4}, {tmp}",
            "and {tmp}, {m5}, {sign}",
            "adcs {w5}, {w5}, {tmp}",
            "and {tmp}, {m6}, {sign}",
            "adcs {w6}, {w6}, {tmp}",
            "and {tmp}, {m7}, {sign}",
            "adcs {w7}, {w7}, {tmp}",
            "adc {w8}, {w8}, xzr",

            // Upstream final adjustment: if an excess remains, add or
            // subtract one aligned modulus according to its sign.
            "neg {sign}, {w8}",
            "orr {excess}, {w8}, {sign}",
            "asr {sign}, {sign}, #63",
            "and {m4}, {m4}, {excess}",
            "and {m5}, {m5}, {excess}",
            "and {m6}, {m6}, {excess}",
            "and {m7}, {m7}, {excess}",
            "eor {m4}, {m4}, {sign}",
            "eor {m5}, {m5}, {sign}",
            "adds {m4}, {m4}, {sign}, lsr #63",
            "eor {m6}, {m6}, {sign}",
            "adcs {m5}, {m5}, xzr",
            "eor {m7}, {m7}, {sign}",
            "adcs {m6}, {m6}, xzr",
            "adc {m7}, {m7}, xzr",
            "adds {w4}, {w4}, {m4}",
            "adcs {w5}, {w5}, {m5}",
            "adcs {w6}, {w6}, {m6}",
            "adc {w7}, {w7}, {m7}",
            p0 = in(reg) modulus[0],
            p1 = in(reg) modulus[1],
            w4 = inout(reg) value[4] => w4,
            w5 = inout(reg) value[5] => w5,
            w6 = inout(reg) value[6] => w6,
            w7 = inout(reg) value[7] => w7,
            w8 = inout(reg) value[8] => _,
            sign = out(reg) _,
            excess = out(reg) _,
            m4 = out(reg) _,
            m5 = out(reg) _,
            m6 = out(reg) _,
            m7 = out(reg) _,
            tmp = out(reg) _,
            options(pure, nomem, nostack),
        );
    }

    (low, [w4, w5, w6, w7])
}

/// Montgomery-reduces an arbitrary 512-bit integer using Semolina's
/// `redc_mont_pasta` schedule.
///
/// This is the generator's `__mul_by_1_mont_pasta` low-half reduction followed
/// by its high-half addition, excess-carry subtraction, and conditional select.
/// For a 512-bit input `T < R^2`, low reduction is at most `p`; adding the high
/// half makes the candidate less than `R + p`, so the selected result is below
/// `R`. Its single subtraction need not make that result canonical (`< p`).
#[inline(always)]
fn redc(low: &Limbs, high: &Limbs, modulus: &Limbs, inv: u64) -> Limbs {
    let (mut r0, mut r1, mut r2, mut r3) = (low[0], low[1], low[2], low[3]);

    // SAFETY: this is a register-renamed transcription of Semolina v0.1.4's
    // `redc_mont_pasta` and `__mul_by_1_mont_pasta`. Rust reads every fixed
    // input limb into a register; the block performs no memory or stack access.
    // All input-dependent selection is constant-time. Early-clobber inout and
    // output operands keep the low accumulator and scratch registers distinct
    // from high limbs and public modulus inputs while they remain live.
    unsafe {
        asm!(
            // Low reduction round 0.
            "mul {q}, {inv}, {r0}",
            "mul {t1}, {p1}, {q}",
            "lsl {t3}, {q}, #62",
            "subs xzr, {r0}, #1",
            "umulh {t0}, {p0}, {q}",
            "adcs {r1}, {r1}, {t1}",
            "umulh {t1}, {p1}, {q}",
            "adcs {r2}, {r2}, xzr",
            "adcs {r3}, {r3}, {t3}",
            "lsr {t3}, {q}, #2",
            "adc {r4}, xzr, xzr",
            "adds {r0}, {r1}, {t0}",
            "adcs {r1}, {r2}, {t1}",
            "adcs {r2}, {r3}, xzr",
            "mul {q}, {inv}, {r0}",
            "adc {r3}, {r4}, {t3}",

            // Low reduction round 1.
            "mul {t1}, {p1}, {q}",
            "lsl {t3}, {q}, #62",
            "subs xzr, {r0}, #1",
            "umulh {t0}, {p0}, {q}",
            "adcs {r1}, {r1}, {t1}",
            "umulh {t1}, {p1}, {q}",
            "adcs {r2}, {r2}, xzr",
            "adcs {r3}, {r3}, {t3}",
            "lsr {t3}, {q}, #2",
            "adc {r4}, xzr, xzr",
            "adds {r0}, {r1}, {t0}",
            "adcs {r1}, {r2}, {t1}",
            "adcs {r2}, {r3}, xzr",
            "mul {q}, {inv}, {r0}",
            "adc {r3}, {r4}, {t3}",

            // Low reduction round 2.
            "mul {t1}, {p1}, {q}",
            "lsl {t3}, {q}, #62",
            "subs xzr, {r0}, #1",
            "umulh {t0}, {p0}, {q}",
            "adcs {r1}, {r1}, {t1}",
            "umulh {t1}, {p1}, {q}",
            "adcs {r2}, {r2}, xzr",
            "adcs {r3}, {r3}, {t3}",
            "lsr {t3}, {q}, #2",
            "adc {r4}, xzr, xzr",
            "adds {r0}, {r1}, {t0}",
            "adcs {r1}, {r2}, {t1}",
            "adcs {r2}, {r3}, xzr",
            "mul {q}, {inv}, {r0}",
            "adc {r3}, {r4}, {t3}",

            // Low reduction round 3.
            "mul {t1}, {p1}, {q}",
            "lsl {t3}, {q}, #62",
            "subs xzr, {r0}, #1",
            "umulh {t0}, {p0}, {q}",
            "adcs {r1}, {r1}, {t1}",
            "umulh {t1}, {p1}, {q}",
            "adcs {r2}, {r2}, xzr",
            "adcs {r3}, {r3}, {t3}",
            "lsr {t3}, {q}, #2",
            "adc {r4}, xzr, xzr",
            "adds {r0}, {r1}, {t0}",
            "adcs {r1}, {r2}, {t1}",
            "adcs {r2}, {r3}, xzr",
            "adc {r3}, {r4}, {t3}",

            // Add the unreduced high half and preserve its excess carry.
            "adds {r0}, {r0}, {h0}",
            "adcs {r1}, {r1}, {h1}",
            "adcs {r2}, {r2}, {h2}",
            "adcs {r3}, {r3}, {h3}",
            "adc {r4}, xzr, xzr",

            // Subtract all five limbs of p, including the excess carry, and
            // retain the original candidate exactly when the subtraction borrows.
            "subs {t0}, {r0}, {p0}",
            "sbcs {t1}, {r1}, {p1}",
            "sbcs {t2}, {r2}, {p2}",
            "sbcs {t3}, {r3}, {p3}",
            "sbcs xzr, {r4}, xzr",
            "csel {r0}, {r0}, {t0}, lo",
            "csel {r1}, {r1}, {t1}, lo",
            "csel {r2}, {r2}, {t2}, lo",
            "csel {r3}, {r3}, {t3}, lo",
            r0 = inout(reg) r0,
            r1 = inout(reg) r1,
            r2 = inout(reg) r2,
            r3 = inout(reg) r3,
            h0 = in(reg) high[0],
            h1 = in(reg) high[1],
            h2 = in(reg) high[2],
            h3 = in(reg) high[3],
            p0 = in(reg) modulus[0],
            p1 = in(reg) modulus[1],
            p2 = in(reg) modulus[2],
            p3 = in(reg) modulus[3],
            inv = in(reg) inv,
            q = out(reg) _,
            r4 = out(reg) _,
            t0 = out(reg) _,
            t1 = out(reg) _,
            t2 = out(reg) _,
            t3 = out(reg) _,
            options(pure, nomem, nostack),
        );
    }

    [r0, r1, r2, r3]
}

/// Conditionally subtracts the modulus once.
///
/// Kept temporarily because the current generated Lean transcription and proof
/// still refer to this block; the AArch64 Rust inversion path no longer calls it.
#[allow(dead_code)]
#[inline(always)]
fn reduce_once(mut value: Limbs, modulus: &Limbs) -> Limbs {
    // SAFETY: register-only subtraction and conditional selection. This returns
    // value unchanged below the modulus and value - modulus otherwise.
    unsafe {
        asm!(
            "subs {t0}, {r0}, {p0}",
            "sbcs {t1}, {r1}, {p1}",
            "sbcs {t2}, {r2}, {p2}",
            "sbcs {t3}, {r3}, {p3}",
            "csel {r0}, {t0}, {r0}, cs",
            "csel {r1}, {t1}, {r1}, cs",
            "csel {r2}, {t2}, {r2}, cs",
            "csel {r3}, {t3}, {r3}, cs",
            r0 = inout(reg) value[0],
            r1 = inout(reg) value[1],
            r2 = inout(reg) value[2],
            r3 = inout(reg) value[3],
            p0 = in(reg) modulus[0],
            p1 = in(reg) modulus[1],
            p2 = in(reg) modulus[2],
            p3 = in(reg) modulus[3],
            t0 = out(reg) _,
            t1 = out(reg) _,
            t2 = out(reg) _,
            t3 = out(reg) _,
            options(pure, nomem, nostack),
        );
    }
    value
}
