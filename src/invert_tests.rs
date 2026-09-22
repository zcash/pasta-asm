//! Differential tests for inversion against dependency-free integer arithmetic.

use crate::{Limbs, invert};

#[cfg(any(
    target_arch = "aarch64",
    all(target_arch = "x86_64", target_pointer_width = "64")
))]
use crate::mul;

const ZERO: Limbs = [0; 4];
const ONE: Limbs = [1, 0, 0, 0];

struct Field {
    name: &'static str,
    modulus: Limbs,
    /// `-modulus[0]^-1 mod 2^64`.
    inv: u64,
}

const FP: Field = Field {
    name: "Fp",
    modulus: [
        0x992d30ed00000001,
        0x224698fc094cf91b,
        0x0000000000000000,
        0x4000000000000000,
    ],
    inv: 0x992d30ecffffffff,
};

const FQ: Field = Field {
    name: "Fq",
    modulus: [
        0x8c46eb2100000001,
        0x224698fc0994a8dd,
        0x0000000000000000,
        0x4000000000000000,
    ],
    inv: 0x8c46eb20ffffffff,
};

const FIELDS: [&Field; 2] = [&FP, &FQ];

fn is_less(lhs: &Limbs, rhs: &Limbs) -> bool {
    for i in (0..4).rev() {
        if lhs[i] != rhs[i] {
            return lhs[i] < rhs[i];
        }
    }
    false
}

fn sub_noborrow(lhs: &Limbs, rhs: &Limbs) -> Limbs {
    let mut ret = [0; 4];
    let mut borrow = false;
    for i in 0..4 {
        let (difference, borrow_1) = lhs[i].overflowing_sub(rhs[i]);
        let (difference, borrow_2) = difference.overflowing_sub(borrow as u64);
        ret[i] = difference;
        borrow = borrow_1 || borrow_2;
    }
    assert!(!borrow);
    ret
}

/// Adds two canonical residues without ever constructing a five-limb value.
fn add_mod(lhs: &Limbs, rhs: &Limbs, modulus: &Limbs) -> Limbs {
    debug_assert!(is_less(lhs, modulus));
    debug_assert!(is_less(rhs, modulus));

    // lhs + rhs mod p = lhs - (p - rhs) when lhs >= p - rhs. This avoids
    // overflow at 2^256 and uses only ordinary integer operations.
    let modulus_minus_rhs = sub_noborrow(modulus, rhs);
    if is_less(lhs, &modulus_minus_rhs) {
        let mut ret = [0; 4];
        let mut carry = false;
        for i in 0..4 {
            let (sum, carry_1) = lhs[i].overflowing_add(rhs[i]);
            let (sum, carry_2) = sum.overflowing_add(carry as u64);
            ret[i] = sum;
            carry = carry_1 || carry_2;
        }
        assert!(!carry);
        ret
    } else {
        sub_noborrow(lhs, &modulus_minus_rhs)
    }
}

/// Reference `lhs * rhs mod modulus`, scanning all 256 bits of `rhs`.
fn mul_mod(lhs: &Limbs, rhs: &Limbs, modulus: &Limbs) -> Limbs {
    debug_assert!(is_less(lhs, modulus));
    debug_assert!(is_less(rhs, modulus));

    let mut product = ZERO;
    let mut doubled = *lhs;
    for bit in 0..256 {
        if (rhs[bit / 64] >> (bit % 64)) & 1 == 1 {
            product = add_mod(&product, &doubled, modulus);
        }
        doubled = add_mod(&doubled, &doubled, modulus);
    }
    product
}

/// Reference `base^exponent mod modulus`, scanning all 256 exponent bits.
fn pow_mod(base: &Limbs, exponent: &Limbs, modulus: &Limbs) -> Limbs {
    let mut product = ONE;
    let mut power = *base;
    for bit in 0..256 {
        if (exponent[bit / 64] >> (bit % 64)) & 1 == 1 {
            product = mul_mod(&product, &power, modulus);
        }
        power = mul_mod(&power, &power, modulus);
    }
    product
}

fn minus_small(value: &Limbs, amount: u64) -> Limbs {
    let mut ret = *value;
    let (limb, mut borrow) = ret[0].overflowing_sub(amount);
    ret[0] = limb;
    for limb in &mut ret[1..] {
        if !borrow {
            break;
        }
        let (value, next_borrow) = limb.overflowing_sub(1);
        *limb = value;
        borrow = next_borrow;
    }
    assert!(!borrow);
    ret
}

/// Converts an ordinary canonical integer to `value * R mod p`, independently.
fn to_mont(value: &Limbs, modulus: &Limbs) -> Limbs {
    let mut ret = *value;
    for _ in 0..256 {
        ret = add_mod(&ret, &ret, modulus);
    }
    ret
}

fn reference_inverse(value: &Limbs, modulus: &Limbs) -> Limbs {
    if *value == ZERO {
        ZERO
    } else {
        pow_mod(value, &minus_small(modulus, 2), modulus)
    }
}

fn reduce(mut value: Limbs, modulus: &Limbs) -> Limbs {
    // Both Pasta moduli have their most significant set bit at bit 254, so a
    // four-limb input needs at most three subtractions to become canonical.
    while !is_less(&value, modulus) {
        value = sub_noborrow(&value, modulus);
    }
    value
}

fn next_random(state: &mut u64) -> u64 {
    // xorshift64* with a fixed nonzero seed: deterministic test data only.
    let mut x = *state;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    *state = x;
    x.wrapping_mul(0x2545_f491_4f6c_dd1d)
}

fn check_inverse(field: &Field, ordinary: Limbs) {
    assert!(is_less(&ordinary, &field.modulus));
    let input = to_mont(&ordinary, &field.modulus);
    assert!(
        is_less(&input, &field.modulus),
        "{} generated a non-canonical Montgomery input for {ordinary:016x?}: {input:016x?}",
        field.name,
    );
    let expected_ordinary = reference_inverse(&ordinary, &field.modulus);
    let expected = to_mont(&expected_ordinary, &field.modulus);
    let actual = invert(&input, &field.modulus, field.inv);

    assert!(
        is_less(&actual, &field.modulus),
        "{} inversion output is not canonical for input {ordinary:016x?}: {actual:016x?}",
        field.name,
    );
    assert_eq!(
        actual, expected,
        "{} inversion mismatch for ordinary input {ordinary:016x?}",
        field.name,
    );

    if ordinary == ZERO {
        assert_eq!(actual, ZERO, "{} invert(0) must be zero", field.name);
    } else {
        // The public Montgomery multiplier supplies an independent end-to-end
        // check that input * inverse(input) is Montgomery one.
        #[cfg(any(
            target_arch = "aarch64",
            all(target_arch = "x86_64", target_pointer_width = "64")
        ))]
        assert_eq!(
            mul(&input, &actual, &field.modulus, field.inv),
            to_mont(&ONE, &field.modulus),
            "{} input times inverse is not one for {ordinary:016x?}",
            field.name,
        );
    }
}

#[test]
fn invert_matches_reference() {
    for field in FIELDS {
        check_inverse(field, ZERO);
        check_inverse(field, ONE);
        check_inverse(field, minus_small(&field.modulus, 1));
        check_inverse(field, minus_small(&field.modulus, 2));

        // Regression cases whose wrapped inversion coefficients can leave a
        // normalized high half at least twice the modulus. In particular, 91's
        // Pallas high half requires all three conditional subtractions.
        for value in [
            11, 13, 15, 39, 67, 91, 101, 147, 153, 171, 175, 183, 195, 227, 245,
        ] {
            check_inverse(field, [value, 0, 0, 0]);
        }

        // Exercise powers of two around every limb boundary and near the
        // field's most significant bit. Bit zero is already covered by ONE.
        for bit in [
            1, 2, 31, 32, 63, 64, 65, 95, 127, 128, 129, 159, 191, 192, 193, 223, 252, 253,
        ] {
            let mut value = ZERO;
            value[bit / 64] = 1 << (bit % 64);
            check_inverse(field, value);
        }

        let mut state = match field.name {
            "Fp" => 0x6a09_e667_f3bc_c909,
            "Fq" => 0xbb67_ae85_84ca_a73b,
            _ => unreachable!(),
        };
        for _ in 0..32 {
            let value = reduce(
                [
                    next_random(&mut state),
                    next_random(&mut state),
                    next_random(&mut state),
                    next_random(&mut state),
                ],
                &field.modulus,
            );
            check_inverse(field, value);
        }
    }
}
