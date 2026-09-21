/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.Spec
import PastaAsm.X86_64.Transcription

/-!
# Correctness of x86-64 modular addition
-/

namespace PastaAsm.X86_64

-- BEGIN addMod corollary
/-- Addition of canonical operands produces a canonical residue congruent to their sum. -/
theorem addMod_spec_of_lt (lhs rhs modulus : Limbs) (hlhs : lhs.Bounded) (hrhs : rhs.Bounded)
    (hm : modulus.Bounded) (hshape : modulus.l2 = 0 ∧ modulus.l3 = 2^62)
    (hlhs_lt : lhs.toNat < modulus.toNat) (hrhs_lt : rhs.toNat < modulus.toNat) :
    ∀ r, r = addMod lhs rhs modulus →
      r.Bounded ∧ r.toNat < modulus.toNat ∧
        r.toNat ≡ lhs.toNat + rhs.toNat [MOD modulus.toNat] := by
  sorry
-- END addMod corollary

end PastaAsm.X86_64
