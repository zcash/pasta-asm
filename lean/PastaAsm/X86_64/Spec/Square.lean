/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.Spec
import PastaAsm.X86_64.Compositions
import PastaAsm.X86_64.Transcription

/-!
# Correctness of the x86-64 squaring blocks and their compositions
-/

namespace PastaAsm.X86_64

-- BEGIN sqrMont_spec statement
/-- Montgomery squaring by the two inline blocks: for a canonical `value`, the result is below `p`
and `2^256 * result ≡ value * value (mod p)`. `squareLo` forms the eight-limb square exactly;
`squareHi` reduces its low half by four Montgomery cancellation steps, adds the high half, and
reduces once conditionally. The candidate is below `2 * p < 2^256`, so the carry dropped by the
high-half addition is `0`. -/
theorem sqrMont_spec (value modulus : Limbs) (inv : Nat) (hv : value.Bounded)
    (hm : modulus.Bounded) (hshape : modulus.l2 = 0 ∧ modulus.l3 = 2^62)
    (hinv_lt : inv < 2^64) (hinv : (inv * modulus.l0 + 1) % 2^64 = 0)
    (hlt : value.toNat < modulus.toNat) :
    ∀ r, r = sqrMont value modulus inv →
      r.Bounded ∧ r.toNat < modulus.toNat ∧
        2^256 * r.toNat ≡ value.toNat * value.toNat [MOD modulus.toNat] := by
  sorry
-- END sqrMont_spec statement
-- BEGIN sqrMont_spec corollaries
/-- The crate's `sqr_n_mul`: the squaring pair `count` times, then the multiplication block by
any four-limb `rhs`. For a canonical `value` the output is below `p` and
`2^(256 * 2^count) * output ≡ value^(2^count) * rhs (mod p)`. The chain keeps its value
canonical, so the multiplication is under its first contract. -/
theorem sqrNMul_spec (value : Limbs) (count : Nat) (rhs modulus : Limbs) (inv : Nat)
    (hv : value.Bounded) (hrhs : rhs.Bounded) (hm : modulus.Bounded)
    (hshape : modulus.l2 = 0 ∧ modulus.l3 = 2^62)
    (hinv_lt : inv < 2^64) (hinv : (inv * modulus.l0 + 1) % 2^64 = 0)
    (hlt : value.toNat < modulus.toNat) :
    ∀ r, r = sqrNMul value count rhs modulus inv →
      r.Bounded ∧ r.toNat < modulus.toNat ∧
        2^(256 * 2^count) * r.toNat ≡ value.toNat^(2^count) * rhs.toNat [MOD modulus.toNat] := by
  sorry
-- END sqrMont_spec corollaries

end PastaAsm.X86_64
