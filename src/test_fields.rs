// Copyright the pasta-asm contributors.
// SPDX-License-Identifier: Apache-2.0

//! The two fields' constants and known answers for the tests, computed independently with
//! big-integer arithmetic in Python, and a reference Montgomery multiplication and Fermat
//! inverse in `u128` arithmetic, for checking any backend's inversion.

use crate::Limbs;

/// One field's constants and known answers.
pub(crate) struct Field {
    pub(crate) modulus: Limbs,
    /// `-modulus[0]^-1 mod 2^64`.
    pub(crate) inv: u64,
    /// `R = 2^256 mod p`, the Montgomery form of `1`.
    pub(crate) r: Limbs,
    /// `2R mod p`.
    pub(crate) two_r: Limbs,
    /// `3R mod p`.
    pub(crate) three_r: Limbs,
    /// `R^2 mod p`.
    pub(crate) r2: Limbs,
    /// `R^3 mod p`.
    pub(crate) r3: Limbs,
    /// `mul(R2, R3) = R^4 mod p`.
    pub(crate) r4: Limbs,
    /// `sqr_n_mul(R2, 2, R3) = R^7 mod p`.
    pub(crate) r7: Limbs,
    /// `mul(p - 1, p - 1)`.
    pub(crate) pm1_sq: Limbs,
    /// `p - 2`.
    pub(crate) pm2: Limbs,
    /// `2^562 mod p`, the starting `v` of `invert`.
    pub(crate) v0: Limbs,
    /// Inputs and outputs of `invert`: `7R`, `0`, `1`, `p - 1`, and a small value, from the
    /// integer model of the algorithm.
    pub(crate) inversions: [(Limbs, Limbs); 5],
}

/// The Pallas base field (`pasta_curves::Fp`).
pub(crate) const FP: Field = Field {
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
    v0: [
        0x9a5f583ce5084635,
        0x4f417e233776c195,
        0x74634b1a733f7785,
        0x1c51de5ea66f0f25,
    ],
    inversions: [
        (
            [0xd83bd700ffffffe5, 0x628ddd6b04e1ba16, 0xfffffffffffffffc, 0x3fffffffffffffff],
            [0x8398bdd8b6db6db7, 0xbbc0f148939d4828, 0xdb6db6db6db6db6d, 0x2db6db6db6db6db6],
        ),
        (
            [0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
            [0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
        ),
        (
            [0x0000000000000001, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
            [0x8c78ecb30000000f, 0xd7d30dbd8b0de0e7, 0x7797a99bc3c95d18, 0x096d41af7b9cb714],
        ),
        (
            [0x992d30ed00000000, 0x224698fc094cf91b, 0x0000000000000000, 0x4000000000000000],
            [0x0cb44439fffffff2, 0x4a738b3e7e3f1834, 0x886856643c36a2e7, 0x3692be50846348eb],
        ),
        (
            [0xfc962fc962fc9630, 0x369d0369d0369cd2, 0x0000000000000000, 0x0000000000000000],
            [0x33912c173eb52b5e, 0x8094d7a33b979988, 0x4c1c894cf5cc5f05, 0x2d05c75a616fc8d4],
        ),
    ],
};

/// The Vesta base field (`pasta_curves::Fq`).
pub(crate) const FQ: Field = Field {
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
    v0: [
        0xa3efbd8ee5083303,
        0xfbadea62cefef7a1,
        0xd6418abb493f6cf9,
        0x2aa5feb88c401333,
    ],
    inversions: [
        (
            [0x34853384ffffffe5, 0x628ddd6afd5230a2, 0xfffffffffffffffc, 0x3fffffffffffffff],
            [0x81c0fd04b6db6db7, 0xbbc0f14893a785d6, 0xdb6db6db6db6db6d, 0x2db6db6db6db6db6],
        ),
        (
            [0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
            [0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
        ),
        (
            [0x0000000000000001, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
            [0xfc9678ff0000000f, 0x67bb433d891a16e3, 0x7fae231004ccf590, 0x096d41af7ccfdaa9],
        ),
        (
            [0x8c46eb2100000000, 0x224698fc0994a8dd, 0x0000000000000000, 0x4000000000000000],
            [0x8fb07221fffffff2, 0xba8b55be807a91f9, 0x8051dceffb330a6f, 0x3692be5083302556],
        ),
        (
            [0xfc962fc962fc9630, 0x369d0369d0369cd2, 0x0000000000000000, 0x0000000000000000],
            [0xe5c6fb7bddd0cf4b, 0x65ee805e3b7d0d89, 0x7562671be840d861, 0x1253ce66fd1d1868],
        ),
    ],
};

pub(crate) const FIELDS: [&Field; 2] = [&FP, &FQ];

pub(crate) const ONE: Limbs = [1, 0, 0, 0];
pub(crate) const ZERO: Limbs = [0, 0, 0, 0];

/// `p - 1`; `modulus[0]` is odd, so the subtraction does not borrow.
pub(crate) fn p_minus_1(f: &Field) -> Limbs {
    let mut limbs = f.modulus;
    limbs[0] -= 1;
    limbs
}

/// `a - b` as little-endian 256-bit integers, for `b ≤ a`.
pub(crate) fn sub_limbs(a: &Limbs, b: &Limbs) -> Limbs {
    let mut out = ZERO;
    let mut borrow = false;
    for i in 0..4 {
        let (d, b1) = a[i].overflowing_sub(b[i]);
        let (d, b2) = d.overflowing_sub(u64::from(borrow));
        out[i] = d;
        borrow = b1 | b2;
    }
    assert!(!borrow, "{b:x?} exceeds {a:x?}");
    out
}

/// A Montgomery inverse computed independently of the crate's routines, by Fermat's little
/// theorem over a plain Montgomery multiplication in `u128` arithmetic (textbook CIOS with a
/// six-limb accumulator, for canonical operands, as pasta_curves' portable backend multiplies).
pub(crate) mod reference {
    use super::Limbs;

    /// `lhs * rhs * 2^-256 mod p` for canonical operands, canonical.
    pub(crate) fn mont_mul(lhs: &Limbs, rhs: &Limbs, modulus: &Limbs, inv: u64) -> Limbs {
        let mut t = [0u64; 6];
        for &b in rhs {
            let mut carry = 0u128;
            for j in 0..4 {
                let v = u128::from(t[j]) + u128::from(lhs[j]) * u128::from(b) + carry;
                t[j] = v as u64;
                carry = v >> 64;
            }
            let v = u128::from(t[4]) + carry;
            t[4] = v as u64;
            t[5] = (v >> 64) as u64;
            let m = t[0].wrapping_mul(inv);
            let v = u128::from(t[0]) + u128::from(m) * u128::from(modulus[0]);
            let mut carry = v >> 64;
            for j in 1..4 {
                let v = u128::from(t[j]) + u128::from(m) * u128::from(modulus[j]) + carry;
                t[j - 1] = v as u64;
                carry = v >> 64;
            }
            let v = u128::from(t[4]) + carry;
            t[3] = v as u64;
            t[4] = t[5] + (v >> 64) as u64;
        }
        // The candidate is below `2p`; subtract `p` unless that borrows past its top word.
        let mut out = [t[0], t[1], t[2], t[3]];
        let mut borrow = false;
        let mut diff = [0u64; 4];
        for i in 0..4 {
            let (d, b1) = out[i].overflowing_sub(modulus[i]);
            let (d, b2) = d.overflowing_sub(u64::from(borrow));
            diff[i] = d;
            borrow = b1 | b2;
        }
        if t[4] != 0 || !borrow {
            out = diff;
        }
        out
    }

    /// The Montgomery inverse of the Montgomery residue `x`: `x^(p-2)` in the Montgomery
    /// domain, starting from `R`, the Montgomery form of `1`.
    pub(crate) fn montgomery_inverse(
        x: &Limbs,
        modulus: &Limbs,
        inv: u64,
        r: &Limbs,
        pm2: &Limbs,
    ) -> Limbs {
        let mut acc = *r;
        for bit in (0..256).rev() {
            acc = mont_mul(&acc, &acc, modulus, inv);
            if (pm2[bit / 64] >> (bit % 64)) & 1 == 1 {
                acc = mont_mul(&acc, x, modulus, inv);
            }
        }
        acc
    }
}
