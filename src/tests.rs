//! Known-answer tests of the four entry points, for both Pasta fields.
//!
//! The expected values were computed independently with big-integer Montgomery
//! arithmetic (`a * b * 2^-256 mod p`) in Python, and the ones that are also among
//! the reference vectors recorded from the assembly on Apple M-series hardware
//! agree with those. The differential tests against portable arithmetic live in
//! `pasta_curves`, which has both implementations.

// The mul-family routines are gated on 64-bit pointers on x86-64, so on
// other targets the constants below are unused; the known answers are
// always kept in full so the sources match across targets.
#![allow(dead_code)]

use super::{Limbs, add, from_mont, is_canonical, sub};

#[cfg(any(
    target_arch = "aarch64",
    all(target_arch = "x86_64", target_pointer_width = "64")
))]
use super::{mul, sqr_n_mul, square};

/// One field's constants and known answers.
struct Field {
    modulus: Limbs,
    /// `-modulus[0]^-1 mod 2^64`.
    inv: u64,
    /// `R = 2^256 mod p`, the Montgomery form of `1`.
    r: Limbs,
    /// `2R mod p`.
    two_r: Limbs,
    /// `3R mod p`.
    three_r: Limbs,
    /// `R^2 mod p`.
    r2: Limbs,
    /// `R^3 mod p`.
    r3: Limbs,
    /// `mul(R2, R3) = R^4 mod p`.
    r4: Limbs,
    /// `sqr_n_mul(R2, 2, R3) = R^7 mod p`.
    r7: Limbs,
    /// `mul(p - 1, p - 1)`.
    pm1_sq: Limbs,
    /// `p - 2`.
    pm2: Limbs,
}

/// The Pallas base field (`pasta_curves::Fp`).
const FP: Field = Field {
    modulus: [
        0x992d30ed00000001,
        0x224698fc094cf91b,
        0x0000000000000000,
        0x4000000000000000,
    ],
    inv: 0x992d30ecffffffff,
    r: [
        0x34786d38fffffffd,
        0x992c350be41914ad,
        0xffffffffffffffff,
        0x3fffffffffffffff,
    ],
    two_r: [
        0xcfc3a984fffffff9,
        0x1011d11bbee5303e,
        0xffffffffffffffff,
        0x3fffffffffffffff,
    ],
    three_r: [
        0x6b0ee5d0fffffff5,
        0x86f76d2b99b14bd0,
        0xfffffffffffffffe,
        0x3fffffffffffffff,
    ],
    r2: [
        0x8c78ecb30000000f,
        0xd7d30dbd8b0de0e7,
        0x7797a99bc3c95d18,
        0x096d41af7b9cb714,
    ],
    r3: [
        0xf185a5993a9e10f9,
        0xf6a68f3b6ac5b1d1,
        0xdf8d1014353fd42c,
        0x2ae309222d2d9910,
    ],
    r4: [
        0x1dfc65f6ad0492ae,
        0x84379b4cc10e927b,
        0x710d6cd04c692c97,
        0x21cce888a6cab566,
    ],
    r7: [
        0x7a3a1c29d1d1bd45,
        0x17023e5920bb6157,
        0x9004eaaf35c21e06,
        0x007efbf9151076fc,
    ],
    pm1_sq: [
        0xcf3f8e8753a769a9,
        0xac9fba6a4077fc57,
        0x70cb2996efc89a65,
        0x21f1c4ff1e2278d5,
    ],
    pm2: [
        0x992d30ecffffffff,
        0x224698fc094cf91b,
        0x0000000000000000,
        0x4000000000000000,
    ],
};

/// The Vesta base field (`pasta_curves::Fq`).
const FQ: Field = Field {
    modulus: [
        0x8c46eb2100000001,
        0x224698fc0994a8dd,
        0x0000000000000000,
        0x4000000000000000,
    ],
    inv: 0x8c46eb20ffffffff,
    r: [
        0x5b2b3e9cfffffffd,
        0x992c350be3420567,
        0xffffffffffffffff,
        0x3fffffffffffffff,
    ],
    two_r: [
        0x2a0f9218fffffff9,
        0x1011d11bbcef61f1,
        0xffffffffffffffff,
        0x3fffffffffffffff,
    ],
    three_r: [
        0xf8f3e594fffffff5,
        0x86f76d2b969cbe7a,
        0xfffffffffffffffe,
        0x3fffffffffffffff,
    ],
    r2: [
        0xfc9678ff0000000f,
        0x67bb433d891a16e3,
        0x7fae231004ccf590,
        0x096d41af7ccfdaa9,
    ],
    r3: [
        0x008b421c249dae4c,
        0xe13bda50dba41326,
        0x88fececb8e15cb63,
        0x07dd97a06e6792c8,
    ],
    r4: [
        0x569bba29179df5c1,
        0xf7abe57547cfa14c,
        0x8d0f36071632bdab,
        0x2c37a71489ba6088,
    ],
    r7: [
        0x56244c6793e8be1f,
        0xbe518f1c2a1b26e6,
        0xb6c73001c86b2b65,
        0x1b7d3aff1b7fd420,
    ],
    pm1_sq: [
        0x6119a3dd8e1a6f7f,
        0xc68de1279dc601eb,
        0x5790be58c050df13,
        0x1f7a89dd17647953,
    ],
    pm2: [
        0x8c46eb20ffffffff,
        0x224698fc0994a8dd,
        0x0000000000000000,
        0x4000000000000000,
    ],
};

const FIELDS: [&Field; 2] = [&FP, &FQ];

const ONE: Limbs = [1, 0, 0, 0];
const ZERO: Limbs = [0, 0, 0, 0];

/// `p - 1`; `modulus[0]` is odd, so the subtraction does not borrow.
fn p_minus_1(f: &Field) -> Limbs {
    let mut limbs = f.modulus;
    limbs[0] -= 1;
    limbs
}

#[test]
fn add_known_answers() {
    for f in FIELDS {
        assert_eq!(add(&f.r, &f.r, &f.modulus), f.two_r);
        assert_eq!(add(&f.r, &f.two_r, &f.modulus), f.three_r);
        assert_eq!(add(&f.two_r, &f.r, &f.modulus), f.three_r);
        let pm1 = p_minus_1(f);
        assert_eq!(add(&pm1, &pm1, &f.modulus), f.pm2);
        assert_eq!(add(&ZERO, &pm1, &f.modulus), pm1);
        assert_eq!(add(&pm1, &ZERO, &f.modulus), pm1);
    }
}

#[test]
fn sub_known_answers() {
    for f in FIELDS {
        assert_eq!(sub(&f.r, &f.r, &f.modulus), ZERO);
        assert_eq!(sub(&f.two_r, &f.r, &f.modulus), f.r);
        assert_eq!(sub(&f.three_r, &f.r, &f.modulus), f.two_r);
        assert_eq!(sub(&f.three_r, &f.two_r, &f.modulus), f.r);
        let pm1 = p_minus_1(f);
        assert_eq!(sub(&pm1, &pm1, &f.modulus), ZERO);
        assert_eq!(sub(&pm1, &f.pm2, &f.modulus), ONE);
    }
}

#[cfg(any(
    target_arch = "aarch64",
    all(target_arch = "x86_64", target_pointer_width = "64")
))]
#[test]
fn mul_known_answers() {
    for f in FIELDS {
        assert_eq!(mul(&f.r, &f.r, &f.modulus, f.inv), f.r);
        assert_eq!(mul(&f.r, &f.r2, &f.modulus, f.inv), f.r2);
        assert_eq!(mul(&f.r2, &f.r3, &f.modulus, f.inv), f.r4);
        assert_eq!(mul(&f.r3, &f.r2, &f.modulus, f.inv), f.r4);
        let pm1 = p_minus_1(f);
        assert_eq!(mul(&pm1, &pm1, &f.modulus, f.inv), f.pm1_sq);
        assert_eq!(mul(&ZERO, &pm1, &f.modulus, f.inv), ZERO);
    }
}

#[cfg(any(
    target_arch = "aarch64",
    all(target_arch = "x86_64", target_pointer_width = "64")
))]
#[test]
fn square_known_answers() {
    for f in FIELDS {
        assert_eq!(square(&f.r, &f.modulus, f.inv), f.r);
        assert_eq!(square(&f.r2, &f.modulus, f.inv), f.r3);
        let pm1 = p_minus_1(f);
        assert_eq!(square(&pm1, &f.modulus, f.inv), f.pm1_sq);
        assert_eq!(square(&ZERO, &f.modulus, f.inv), ZERO);
    }
}

#[cfg(any(
    target_arch = "aarch64",
    all(target_arch = "x86_64", target_pointer_width = "64")
))]
#[test]
fn sqr_n_mul_known_answers() {
    for f in FIELDS {
        assert_eq!(sqr_n_mul(&f.r2, 0, &f.r3, &f.modulus, f.inv), f.r4);
        assert_eq!(sqr_n_mul(&f.r, 1, &f.r2, &f.modulus, f.inv), f.r2);
        assert_eq!(sqr_n_mul(&f.r2, 1, &f.r, &f.modulus, f.inv), f.r3);
        assert_eq!(sqr_n_mul(&f.r2, 2, &f.r3, &f.modulus, f.inv), f.r7);
    }
}

#[test]
fn from_mont_known_answers() {
    for f in FIELDS {
        assert_eq!(from_mont(&f.r, &f.modulus, f.inv), ONE);
        assert_eq!(from_mont(&f.r2, &f.modulus, f.inv), f.r);
        assert_eq!(from_mont(&ZERO, &f.modulus, f.inv), ZERO);
    }
    // `from_mont` accepts any four-limb value: the all-ones input is the
    // extreme case of that contract, where the candidate is largest.
    assert_eq!(
        from_mont(&[u64::MAX; 4], &FP.modulus, FP.inv),
        [
            0xc9eda265ac589659,
            0x75a6de91c8d4fcc3,
            0x8f34d6691037659a,
            0x1e0e3b00e1dd872a,
        ]
    );
    assert_eq!(
        from_mont(&[u64::MAX; 4], &FQ.modulus, FQ.inv),
        [
            0x2b2d474371e59083,
            0x5bb8b7d46bcea6f2,
            0xa86f41a73faf20ec,
            0x20857622e89b86ac,
        ]
    );
}

// ---------------------------------------------------------------------------
// Portable reference implementation.
//
// Differential testing needs a second implementation that shares no code with
// the assembly. This is a textbook 4x4 schoolbook product followed by a
// four-step Montgomery reduction on the full eight-limb accumulator, written
// against `u128` so that it has no carry chains of its own to get wrong. It
// accepts *any* four-limb inputs, reduced or not, so it also covers `mul`'s
// unreduced-`lhs` allowance.
//
// `reference_matches_the_known_answers` pins the reference itself against the
// independently computed vectors above; without that, a differential test
// between two wrong implementations proves nothing.
// ---------------------------------------------------------------------------

/// The full 512-bit schoolbook product.
fn mul_wide(a: &Limbs, b: &Limbs) -> [u64; 8] {
    let mut out = [0u64; 8];
    for i in 0..4 {
        let mut carry = 0u64;
        for j in 0..4 {
            let t = (out[i + j] as u128) + (a[i] as u128) * (b[j] as u128) + (carry as u128);
            out[i + j] = t as u64;
            carry = (t >> 64) as u64;
        }
        out[i + 4] = carry;
    }
    out
}

/// `t * 2^-256 mod modulus`, reduced into `[0, modulus)`.
fn redc(mut t: [u64; 8], modulus: &Limbs, inv: u64) -> Limbs {
    let mut extra = 0u64;
    for i in 0..4 {
        let m = t[i].wrapping_mul(inv);
        let mut carry = 0u64;
        for j in 0..4 {
            let s = (t[i + j] as u128) + (m as u128) * (modulus[j] as u128) + (carry as u128);
            t[i + j] = s as u64;
            carry = (s >> 64) as u64;
        }
        assert_eq!(t[i], 0, "the Montgomery step must cancel limb {i}");
        let mut k = i + 4;
        while carry != 0 && k < 8 {
            let s = (t[k] as u128) + (carry as u128);
            t[k] = s as u64;
            carry = (s >> 64) as u64;
            k += 1;
        }
        if carry != 0 {
            extra += carry;
        }
    }
    // The candidate is `extra * 2^256 + t[4..8]`, below `2 * modulus`.
    let mut r = [t[4], t[5], t[6], t[7], extra];
    while !(r[4] == 0 && is_canonical(&[r[0], r[1], r[2], r[3]], modulus)) {
        // Wide five-limb subtraction of the modulus.
        let mut borrow = 0u128;
        for j in 0..4 {
            let d = (r[j] as u128)
                .wrapping_sub(modulus[j] as u128)
                .wrapping_sub(borrow);
            r[j] = d as u64;
            borrow = (d >> 127) & 1;
        }
        r[4] = r[4].wrapping_sub(borrow as u64);
    }
    [r[0], r[1], r[2], r[3]]
}

/// `a * b * 2^-256 mod modulus`, for any four-limb `a` and `b`.
fn mul_ref(a: &Limbs, b: &Limbs, modulus: &Limbs, inv: u64) -> Limbs {
    redc(mul_wide(a, b), modulus, inv)
}

/// `a + b mod modulus`, for canonical `a` and `b`.
fn add_ref(a: &Limbs, b: &Limbs, modulus: &Limbs) -> Limbs {
    let mut r = [0u64; 5];
    let mut carry = 0u128;
    for j in 0..4 {
        let s = (a[j] as u128) + (b[j] as u128) + carry;
        r[j] = s as u64;
        carry = s >> 64;
    }
    r[4] = carry as u64;
    while !(r[4] == 0 && is_canonical(&[r[0], r[1], r[2], r[3]], modulus)) {
        let mut borrow = 0u128;
        for j in 0..4 {
            let d = (r[j] as u128)
                .wrapping_sub(modulus[j] as u128)
                .wrapping_sub(borrow);
            r[j] = d as u64;
            borrow = (d >> 127) & 1;
        }
        r[4] = r[4].wrapping_sub(borrow as u64);
    }
    [r[0], r[1], r[2], r[3]]
}

/// `a - b mod modulus`, for canonical `a` and `b`.
fn sub_ref(a: &Limbs, b: &Limbs, modulus: &Limbs) -> Limbs {
    let mut r = [0u64; 4];
    let mut borrow = 0u128;
    for j in 0..4 {
        let d = (a[j] as u128)
            .wrapping_sub(b[j] as u128)
            .wrapping_sub(borrow);
        r[j] = d as u64;
        borrow = (d >> 127) & 1;
    }
    if borrow != 0 {
        let mut carry = 0u128;
        for j in 0..4 {
            let s = (r[j] as u128) + (modulus[j] as u128) + carry;
            r[j] = s as u64;
            carry = s >> 64;
        }
    }
    r
}

/// SplitMix64, so the vectors are pseudo-random but the run is reproducible:
/// a failure reported from CI is replayable verbatim.
struct Rng(u64);

impl Rng {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    /// Any four-limb value, including values at or above the modulus.
    fn any(&mut self) -> Limbs {
        [
            self.next_u64(),
            self.next_u64(),
            self.next_u64(),
            self.next_u64(),
        ]
    }

    /// A uniform canonical residue. Rejection sampling over the top 63 bits
    /// keeps the whole range reachable, including `[2^254, p)`, which masking
    /// the top limb to 62 bits would exclude.
    fn canonical(&mut self, modulus: &Limbs) -> Limbs {
        loop {
            let v = [
                self.next_u64(),
                self.next_u64(),
                self.next_u64(),
                self.next_u64() >> 1,
            ];
            if is_canonical(&v, modulus) {
                return v;
            }
        }
    }
}

/// How many random vectors each property test draws per field.
const ROUNDS: usize = 512;

#[test]
fn reference_matches_the_known_answers() {
    for f in FIELDS {
        assert_eq!(mul_ref(&f.r, &f.r, &f.modulus, f.inv), f.r);
        assert_eq!(mul_ref(&f.r2, &f.r3, &f.modulus, f.inv), f.r4);
        let pm1 = p_minus_1(f);
        assert_eq!(mul_ref(&pm1, &pm1, &f.modulus, f.inv), f.pm1_sq);
        assert_eq!(mul_ref(&f.r, &ONE, &f.modulus, f.inv), ONE);
        assert_eq!(add_ref(&f.r, &f.two_r, &f.modulus), f.three_r);
        assert_eq!(sub_ref(&f.three_r, &f.r, &f.modulus), f.two_r);
        assert_eq!(add_ref(&pm1, &ONE, &f.modulus), ZERO);
        assert_eq!(sub_ref(&ZERO, &ONE, &f.modulus), pm1);
    }
}

// ---------------------------------------------------------------------------
// Boundaries the known answers above do not reach.
// ---------------------------------------------------------------------------

#[test]
fn is_canonical_at_the_boundary() {
    for f in FIELDS {
        let pm1 = p_minus_1(f);
        assert!(is_canonical(&ZERO, &f.modulus));
        assert!(is_canonical(&pm1, &f.modulus));
        // The modulus itself is not canonical, and neither is anything above.
        assert!(!is_canonical(&f.modulus, &f.modulus));
        assert!(!is_canonical(&[u64::MAX; 4], &f.modulus));
        // A value differing only in a high limb must be decided by that limb,
        // not by the low limbs that `is_canonical` sees first in memory.
        assert!(is_canonical(&[u64::MAX, u64::MAX, u64::MAX, 0], &f.modulus));
        assert!(!is_canonical(&[0, 0, 0, f.modulus[3] + 1], &f.modulus));
        // Equal in limbs 3 and 2, decided at limb 1.
        assert!(is_canonical(
            &[u64::MAX, f.modulus[1] - 1, 0, f.modulus[3]],
            &f.modulus
        ));
    }
}

#[test]
fn add_reduces_exactly_at_the_modulus() {
    for f in FIELDS {
        let pm1 = p_minus_1(f);
        // The sum is exactly the modulus: the conditional subtraction must
        // fire and leave zero.
        assert_eq!(add(&pm1, &ONE, &f.modulus), ZERO);
        assert_eq!(add(&ONE, &pm1, &f.modulus), ZERO);
        // One below the modulus: the conditional subtraction must not fire.
        assert_eq!(add(&f.pm2, &ONE, &f.modulus), pm1);
        assert_eq!(add(&ZERO, &ZERO, &f.modulus), ZERO);
    }
}

#[test]
fn sub_borrows_through_every_limb() {
    for f in FIELDS {
        let pm1 = p_minus_1(f);
        // `0 - 1` underflows all four limbs, so the conditional add-back of
        // the modulus has to run. No vector above takes this branch.
        assert_eq!(sub(&ZERO, &ONE, &f.modulus), pm1);
        assert_eq!(sub(&ZERO, &pm1, &f.modulus), ONE);
        assert_eq!(sub(&ZERO, &ZERO, &f.modulus), ZERO);
        assert_eq!(
            sub(&f.r, &f.two_r, &f.modulus),
            sub_ref(&f.r, &f.two_r, &f.modulus)
        );
        // `1 - (p - 2) = 3 - p`, which is `3` once the modulus is added back.
        assert_eq!(sub(&ONE, &f.pm2, &f.modulus), [3, 0, 0, 0]);
    }
}

#[test]
fn from_mont_of_the_modulus_is_zero() {
    for f in FIELDS {
        // `p * 2^-256 = 0 mod p`, and it is the one input whose pre-reduction
        // candidate lands exactly on the modulus, so the final conditional
        // subtraction must fire.
        assert_eq!(from_mont(&f.modulus, &f.modulus, f.inv), ZERO);
        let pm1 = p_minus_1(f);
        assert_eq!(
            from_mont(&pm1, &f.modulus, f.inv),
            mul_ref(&pm1, &ONE, &f.modulus, f.inv)
        );
        assert_eq!(
            from_mont(&ONE, &f.modulus, f.inv),
            mul_ref(&ONE, &ONE, &f.modulus, f.inv)
        );
    }
}

// ---------------------------------------------------------------------------
// Differential tests against the portable reference.
// ---------------------------------------------------------------------------

#[test]
fn add_matches_the_reference() {
    let mut rng = Rng(0x0add_0000_0000_0001);
    for f in FIELDS {
        for _ in 0..ROUNDS {
            let a = rng.canonical(&f.modulus);
            let b = rng.canonical(&f.modulus);
            assert_eq!(
                add(&a, &b, &f.modulus),
                add_ref(&a, &b, &f.modulus),
                "add({a:016x?}, {b:016x?})"
            );
        }
    }
}

#[test]
fn sub_matches_the_reference() {
    let mut rng = Rng(0x0005_0b00_0000_0001);
    for f in FIELDS {
        for _ in 0..ROUNDS {
            let a = rng.canonical(&f.modulus);
            let b = rng.canonical(&f.modulus);
            assert_eq!(
                sub(&a, &b, &f.modulus),
                sub_ref(&a, &b, &f.modulus),
                "sub({a:016x?}, {b:016x?})"
            );
        }
    }
}

#[test]
fn from_mont_matches_the_reference_on_any_four_limb_input() {
    let mut rng = Rng(0x0f20_3407_0000_0001);
    for f in FIELDS {
        for _ in 0..ROUNDS {
            // `from_mont` accepts any four-limb value, reduced or not.
            let a = rng.any();
            assert_eq!(
                from_mont(&a, &f.modulus, f.inv),
                mul_ref(&a, &ONE, &f.modulus, f.inv),
                "from_mont({a:016x?})"
            );
        }
    }
}

#[cfg(any(
    target_arch = "aarch64",
    all(target_arch = "x86_64", target_pointer_width = "64")
))]
#[test]
fn mul_matches_the_reference() {
    let mut rng = Rng(0x0111_0000_0000_0001);
    for f in FIELDS {
        for _ in 0..ROUNDS {
            let a = rng.canonical(&f.modulus);
            let b = rng.canonical(&f.modulus);
            assert_eq!(
                mul(&a, &b, &f.modulus, f.inv),
                mul_ref(&a, &b, &f.modulus, f.inv),
                "mul({a:016x?}, {b:016x?})"
            );
        }
    }
}

#[cfg(any(
    target_arch = "aarch64",
    all(target_arch = "x86_64", target_pointer_width = "64")
))]
#[test]
fn square_matches_the_reference() {
    let mut rng = Rng(0x0591_0000_0000_0001);
    for f in FIELDS {
        for _ in 0..ROUNDS {
            let a = rng.canonical(&f.modulus);
            assert_eq!(
                square(&a, &f.modulus, f.inv),
                mul_ref(&a, &a, &f.modulus, f.inv),
                "square({a:016x?})"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Algebraic laws. These need no reference implementation: they are the field
// axioms, so a failure is a bug in the assembly by itself. They also tie the
// routines to each other, which matters most on x86-64, where `mul`,
// `square`, `sqr_n_mul`, and `from_mont` are four separate instruction
// streams that agree only if all four are right.
// ---------------------------------------------------------------------------

#[cfg(any(
    target_arch = "aarch64",
    all(target_arch = "x86_64", target_pointer_width = "64")
))]
#[test]
fn square_agrees_with_mul() {
    let mut rng = Rng(0x0592_4d17_0000_0001);
    for f in FIELDS {
        for _ in 0..ROUNDS {
            let a = rng.canonical(&f.modulus);
            assert_eq!(
                square(&a, &f.modulus, f.inv),
                mul(&a, &a, &f.modulus, f.inv),
                "square({a:016x?})"
            );
        }
    }
}

#[test]
fn from_mont_agrees_with_multiplication_by_one() {
    let mut rng = Rng(0x0f11_0000_0000_0001);
    for f in FIELDS {
        for _ in 0..ROUNDS {
            let a = rng.canonical(&f.modulus);
            #[cfg(any(
                target_arch = "aarch64",
                all(target_arch = "x86_64", target_pointer_width = "64")
            ))]
            assert_eq!(
                from_mont(&a, &f.modulus, f.inv),
                mul(&a, &ONE, &f.modulus, f.inv),
                "from_mont({a:016x?})"
            );
            assert_eq!(
                from_mont(&a, &f.modulus, f.inv),
                mul_ref(&a, &ONE, &f.modulus, f.inv),
                "from_mont({a:016x?})"
            );
        }
    }
}

#[test]
fn add_and_sub_form_an_abelian_group() {
    let mut rng = Rng(0x0ab1_0000_0000_0001);
    for f in FIELDS {
        for _ in 0..ROUNDS {
            let a = rng.canonical(&f.modulus);
            let b = rng.canonical(&f.modulus);
            let c = rng.canonical(&f.modulus);
            // Identity.
            assert_eq!(add(&a, &ZERO, &f.modulus), a);
            assert_eq!(sub(&a, &ZERO, &f.modulus), a);
            // Commutativity.
            assert_eq!(add(&a, &b, &f.modulus), add(&b, &a, &f.modulus));
            // Associativity.
            let ab_c = add(&add(&a, &b, &f.modulus), &c, &f.modulus);
            let a_bc = add(&a, &add(&b, &c, &f.modulus), &f.modulus);
            assert_eq!(ab_c, a_bc);
            // Inverses, in both directions: this is the only law that forces
            // `sub`'s conditional add-back and `add`'s conditional
            // subtraction to agree.
            assert_eq!(add(&sub(&a, &b, &f.modulus), &b, &f.modulus), a);
            assert_eq!(sub(&add(&a, &b, &f.modulus), &b, &f.modulus), a);
            assert_eq!(
                add(&a, &sub(&ZERO, &a, &f.modulus), &f.modulus),
                ZERO,
                "a + (-a) for a = {a:016x?}"
            );
        }
    }
}

#[cfg(any(
    target_arch = "aarch64",
    all(target_arch = "x86_64", target_pointer_width = "64")
))]
#[test]
fn mul_is_a_commutative_monoid_and_distributes() {
    let mut rng = Rng(0x0d15_7217_0000_0001);
    for f in FIELDS {
        for _ in 0..ROUNDS {
            let a = rng.canonical(&f.modulus);
            let b = rng.canonical(&f.modulus);
            let c = rng.canonical(&f.modulus);
            // `R` is the Montgomery form of one, so it is the unit.
            assert_eq!(mul(&a, &f.r, &f.modulus, f.inv), a);
            assert_eq!(mul(&f.r, &a, &f.modulus, f.inv), a);
            assert_eq!(mul(&a, &ZERO, &f.modulus, f.inv), ZERO);
            // Commutativity.
            assert_eq!(
                mul(&a, &b, &f.modulus, f.inv),
                mul(&b, &a, &f.modulus, f.inv)
            );
            // Associativity.
            assert_eq!(
                mul(&mul(&a, &b, &f.modulus, f.inv), &c, &f.modulus, f.inv),
                mul(&a, &mul(&b, &c, &f.modulus, f.inv), &f.modulus, f.inv)
            );
            // Distributivity ties `mul` to `add`: a wrong conditional
            // subtraction in either shows up here.
            assert_eq!(
                mul(&add(&a, &b, &f.modulus), &c, &f.modulus, f.inv),
                add(
                    &mul(&a, &c, &f.modulus, f.inv),
                    &mul(&b, &c, &f.modulus, f.inv),
                    &f.modulus
                )
            );
        }
    }
}

#[cfg(any(
    target_arch = "aarch64",
    all(target_arch = "x86_64", target_pointer_width = "64")
))]
#[test]
fn sqr_n_mul_matches_the_unfused_composition() {
    let mut rng = Rng(0x0509_0000_0000_0001);
    for f in FIELDS {
        for _ in 0..16 {
            let a = rng.canonical(&f.modulus);
            let b = rng.canonical(&f.modulus);
            // Small counts, including the zero-squaring case, plus a count of
            // the order a field inversion uses: the x86-64 backend's fused
            // loop carries the accumulator in registers across iterations,
            // and only a long run exercises that.
            for count in [0usize, 1, 2, 3, 7, 64, 253] {
                let mut acc = a;
                for _ in 0..count {
                    acc = square(&acc, &f.modulus, f.inv);
                }
                let expected = mul(&acc, &b, &f.modulus, f.inv);
                assert_eq!(
                    sqr_n_mul(&a, count, &b, &f.modulus, f.inv),
                    expected,
                    "sqr_n_mul({a:016x?}, {count}, {b:016x?})"
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The unreduced-`lhs` allowance, pinned here rather than only in
// `pasta_curves`: this crate is what documents and debug-asserts the
// contract, so this is where it belongs.
// ---------------------------------------------------------------------------

#[cfg(any(
    target_arch = "aarch64",
    all(target_arch = "x86_64", target_pointer_width = "64")
))]
#[test]
fn mul_accepts_an_unreduced_lhs_at_the_documented_rhs_bound() {
    for f in FIELDS {
        // The documented worst case: a canonical `rhs` whose limbs 1 and 2
        // sit at the stated bound of `2^64 - 3`. Limb 3 is capped at `2^62`
        // by canonicity, so it can never reach the bound.
        let rhs = [u64::MAX, u64::MAX - 2, u64::MAX - 2, f.modulus[3] - 1];
        assert!(is_canonical(&rhs, &f.modulus));

        for lhs in [
            [u64::MAX; 4],
            f.modulus,
            [u64::MAX, u64::MAX, u64::MAX, f.modulus[3]],
            [0, 0, 0, u64::MAX],
        ] {
            assert!(
                !is_canonical(&lhs, &f.modulus),
                "this vector is meant to be unreduced"
            );
            assert_eq!(
                mul(&lhs, &rhs, &f.modulus, f.inv),
                mul_ref(&lhs, &rhs, &f.modulus, f.inv),
                "mul({lhs:016x?}, {rhs:016x?})"
            );
        }

        // And randomly, over unreduced left operands.
        let mut rng = Rng(0x0075_0000_0000_0001);
        for _ in 0..ROUNDS {
            let lhs = rng.any();
            let mut rhs = rng.canonical(&f.modulus);
            rhs[1] = u64::MAX - 2;
            rhs[2] = u64::MAX - 2;
            rhs[3] = f.modulus[3] - 1;
            assert!(is_canonical(&rhs, &f.modulus));
            assert_eq!(
                mul(&lhs, &rhs, &f.modulus, f.inv),
                mul_ref(&lhs, &rhs, &f.modulus, f.inv),
                "mul({lhs:016x?}, {rhs:016x?})"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// End-to-end: Fermat's little theorem. Nothing in this test is a stored
// vector, so it cannot agree with the implementation by construction, and it
// drives the full 256-step exponentiation ladder that a field inversion uses.
// ---------------------------------------------------------------------------

/// `base^exp` in Montgomery form, by square-and-multiply over the crate's own
/// routines.
#[cfg(any(
    target_arch = "aarch64",
    all(target_arch = "x86_64", target_pointer_width = "64")
))]
fn pow(base: &Limbs, exp: &Limbs, f: &Field) -> Limbs {
    let mut acc = f.r;
    for i in (0..4).rev() {
        for bit in (0..64).rev() {
            acc = square(&acc, &f.modulus, f.inv);
            if (exp[i] >> bit) & 1 == 1 {
                acc = mul(&acc, base, &f.modulus, f.inv);
            }
        }
    }
    acc
}

#[cfg(any(
    target_arch = "aarch64",
    all(target_arch = "x86_64", target_pointer_width = "64")
))]
#[test]
fn fermat_and_inversion_round_trip() {
    let mut rng = Rng(0x0fe4_3a70_0000_0001);
    for f in FIELDS {
        let pm1 = p_minus_1(f);
        for _ in 0..4 {
            let a = rng.canonical(&f.modulus);
            if a == ZERO {
                continue;
            }
            // a^(p-1) = 1, in Montgomery form `R`.
            assert_eq!(pow(&a, &pm1, f), f.r, "a^(p-1) for a = {a:016x?}");
            // a^(p-2) is a's inverse, so a * a^(p-2) = 1.
            let inverse = pow(&a, &f.pm2, f);
            assert_eq!(
                mul(&a, &inverse, &f.modulus, f.inv),
                f.r,
                "a * a^-1 for a = {a:016x?}"
            );
            // The same inverse through the fused chain, which is how a real
            // inversion computes it.
            assert_eq!(sqr_n_mul(&a, 0, &inverse, &f.modulus, f.inv), f.r);
        }
    }
}
