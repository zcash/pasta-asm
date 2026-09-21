/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.Spec
import PastaAsm.X86_64.Transcription

/-!
# Correctness of x86-64 modular subtraction
-/

namespace PastaAsm.X86_64

-- BEGIN subMod corollary
/-- Subtraction of canonical operands produces a canonical modular difference. -/
theorem subMod_spec_of_lt (lhs rhs modulus : Limbs) (hlhs : lhs.Bounded) (hrhs : rhs.Bounded)
    (hm : modulus.Bounded) (hshape : modulus.l2 = 0 ∧ modulus.l3 = 2^62)
    (hlhs_lt : lhs.toNat < modulus.toNat) (hrhs_lt : rhs.toNat < modulus.toNat) :
    ∀ r, r = subMod lhs rhs modulus →
      r.Bounded ∧ r.toNat < modulus.toNat ∧
        r.toNat + rhs.toNat ≡ lhs.toNat [MOD modulus.toNat] := by
  sorry
-- END subMod corollary

end PastaAsm.X86_64
