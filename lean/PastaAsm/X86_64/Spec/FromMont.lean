/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.Spec
import PastaAsm.X86_64.Transcription

/-!
# Correctness of x86-64 Montgomery reduction

-/

namespace PastaAsm.X86_64

-- BEGIN fromMont_spec statement
/-- The standalone x86-64 conversion block performs four Montgomery cancellation steps and one
conditional subtraction: for every four-limb `value`, the result is below `p` and
`2^256 * result ≡ value (mod p)`. -/
theorem fromMont_spec (value modulus : Limbs) (inv : Nat) (hv : value.Bounded)
    (hm : modulus.Bounded) (hshape : modulus.l2 = 0 ∧ modulus.l3 = 2^62)
    (hinv_lt : inv < 2^64) (hinv : (inv * modulus.l0 + 1) % 2^64 = 0) :
    ∀ r, r = fromMont value modulus inv →
      r.Bounded ∧ r.toNat < modulus.toNat ∧
        2^256 * r.toNat ≡ value.toNat [MOD modulus.toNat] := by
  sorry
-- END fromMont_spec statement

end PastaAsm.X86_64
