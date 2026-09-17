use crate::Limbs;

#[inline(always)]
pub(crate) fn mul(lhs: &Limbs, rhs: &Limbs, modulus: &Limbs, inv: u64) -> Limbs {
    let mut out = Limbs::default();
    unsafe { pasta_mul(&mut out, lhs, rhs, modulus, inv) };
    out
}

#[inline(always)]
pub(crate) fn sqr_n_mul(a: &Limbs, n: usize, b: &Limbs, modulus: &Limbs, inv: u64) -> Limbs {
    if n > 0 {
        let mut unreduced = Limbs::default();
        let mut out = Limbs::default();
        unsafe { sqrx_n_mul_mont_pasta(&mut unreduced, a, n, b, modulus, inv) };
        // Use add(_, 0) for the side-effect of a final reduction.
        unsafe { pasta_add(&mut out, &unreduced, &[0; 4], modulus) };
        out
    } else {
        mul(a, b, modulus, inv)
    }
}

#[inline(always)]
pub(crate) fn invert(a: &Limbs, modulus: &Limbs, inv: u64) -> Limbs {
    let mut out = Limbs::default();
    unsafe { pasta_reciprocal(&mut out, a, modulus, inv) };
    out
}

unsafe extern "C" {
    fn pasta_add(out: *mut Limbs, a: *const Limbs, b: *const Limbs, p: *const Limbs);
    fn pasta_mul(out: *mut Limbs, a: *const Limbs, b: *const Limbs, p: *const Limbs, p0: u64);
    fn sqrx_n_mul_mont_pasta(
        out: *mut Limbs,
        a: *const Limbs,
        n: usize,
        b: *const Limbs,
        p: *const Limbs,
        p0: u64,
    );
    fn pasta_reciprocal(out: *mut Limbs, a: *const Limbs, p: *const Limbs, p0: u64);
}
