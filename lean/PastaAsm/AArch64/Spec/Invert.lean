/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.InversionFields
import PastaAsm.AArch64.Compositions

/-!
# Correctness contract for the AArch64 inversion composition

This is the fixed top-level obligation used by `invert_entry_spec`. Intermediate
commits may leave its proof unfinished; merge readiness requires discharging it
without changing the public contract or assuming internal convergence/bounds.
-/

namespace PastaAsm.AArch64

/-- Inversion of a canonical Montgomery residue at either supported Pasta field.
The result is canonical, zero maps to zero, and a nonzero input times its result
is congruent to `R²`. The schedule and coefficient bounds are proof obligations,
not additional preconditions. -/
theorem invert_spec (F : PastaField) (hF : IsInversionField F) (value : Limbs)
    (hv : value.Bounded) (hlt : value.toNat < F.modulus.toNat) :
    (invert value F.modulus F.inv).Bounded ∧
      (invert value F.modulus F.inv).toNat < F.modulus.toNat ∧
      (if value.toNat = 0 then
        invert value F.modulus F.inv = Limbs.ofNat 0
      else
        value.toNat * (invert value F.modulus F.inv).toNat ≡ R^2 [MOD F.modulus.toNat]) := by
  sorry

end PastaAsm.AArch64
