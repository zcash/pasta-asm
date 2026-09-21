/-
Copyright Supranational LLC (the routines, transcribed from Semolina v0.1.4).
Copyright (c) 2026 the pasta-asm contributors (the transcription and the proofs).
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.Spec
import PastaAsm.X86_64.Transcription

/-!
# Correctness of the transcribed Pasta multiplication block

See the parent module's documentation for details.
-/

namespace PastaAsm.X86_64

-- BEGIN mulMont_spec statement
-- END mulMont_spec statement

-- BEGIN mulMont_spec corollaries
/-- The contract the crate's callers use: a canonical left operand and any four-limb right
operand. -/
theorem mulMont_spec_of_lhs_lt (lhs rhs modulus : Limbs) (inv : Nat) (hlhs : lhs.Bounded)
    (hrhs : rhs.Bounded) (hm : modulus.Bounded) (hshape : modulus.l2 = 0 ∧ modulus.l3 = 2^62)
    (hinv_lt : inv < 2^64) (hinv : (inv * modulus.l0 + 1) % 2^64 = 0)
    (hlt : lhs.toNat < modulus.toNat) :
    ∀ r, r = mulMont lhs rhs modulus inv →
      r.Bounded ∧ r.toNat < modulus.toNat ∧
        2^256 * r.toNat ≡ lhs.toNat * rhs.toNat [MOD modulus.toNat] := by
  sorry

/-- The other safe contract: any four-limb left operand, a canonical right operand whose limbs 1
to 3 are at most `2^64 - 3`. -/
theorem mulMont_spec_of_rhs_lt (lhs rhs modulus : Limbs) (inv : Nat) (hlhs : lhs.Bounded)
    (hrhs : rhs.Bounded) (hm : modulus.Bounded) (hshape : modulus.l2 = 0 ∧ modulus.l3 = 2^62)
    (hinv_lt : inv < 2^64) (hinv : (inv * modulus.l0 + 1) % 2^64 = 0)
    (hlt : rhs.toNat < modulus.toNat)
    (hlimbs : rhs.l1 + 3 ≤ 2^64 ∧ rhs.l2 + 3 ≤ 2^64 ∧ rhs.l3 + 3 ≤ 2^64) :
    ∀ r, r = mulMont lhs rhs modulus inv →
      r.Bounded ∧ r.toNat < modulus.toNat ∧
        2^256 * r.toNat ≡ lhs.toNat * rhs.toNat [MOD modulus.toNat] := by
  sorry
-- END mulMont_spec corollaries

end PastaAsm.X86_64
