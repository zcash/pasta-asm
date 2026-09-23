/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.X86_64.Spec.Invert.Correctness

/-!
# Correctness contract for the x86-64 inversion composition

This is the fixed top-level obligation used by `invert_entry_spec`. Intermediate
commits may leave its proof unfinished; merge readiness requires discharging it
without changing the public contract or assuming internal convergence/bounds.
-/

namespace PastaAsm.X86_64

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
  let initial : InvertState :=
    ⟨value, F.modulus, ⟨1, 0, 0, 0, 0, 0, 0, 0, 0⟩,
      ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
  let state := invertBatches 15 initial
  let matrix := divsteps47 state.a.l0 state.b.l0
  let coefficient := invertLincomb9 state.u state.v matrix.f1 matrix.g1
  have hschedule := invertSchedule_spec F hF value hv hlt
  change coefficient.Bounded ∧
      -(InversionNormalization.coefficientRadix : Int) ≤ coefficient.toInt ∧
      coefficient.toInt ≤ InversionNormalization.coefficientRadix ∧
      (if value.toNat = 0 then coefficient.toInt = 0
       else (value.toNat : Int) * coefficient.toInt ≡ (R^2 : Nat)
         [ZMOD F.modulus.toNat]) at hschedule
  obtain ⟨hcoefficient, hlower, hupper, hscheduleResult⟩ := hschedule
  have hepilogue := invertEpilogue_spec F hF coefficient hcoefficient hlower hupper
  let normalized := normalize512 coefficient F.modulus
  let reduced := redcMont normalized F.modulus F.inv
  let out := mulMont reduced (montgomeryR2 F.modulus) F.modulus F.inv
  change out.Bounded ∧ out.toNat < F.modulus.toNat ∧
    (out.toNat : Int) ≡ coefficient.toInt [ZMOD F.modulus.toNat] at hepilogue
  change out.Bounded ∧ out.toNat < F.modulus.toNat ∧ _
  refine ⟨hepilogue.1, hepilogue.2.1, ?_⟩
  by_cases hzero : value.toNat = 0
  · rw [if_pos hzero]
    change out = Limbs.ofNat 0
    have hcoefficientZero : coefficient.toInt = 0 := by
      simpa only [hzero, if_true] using hscheduleResult
    have houtZeroInt : (out.toNat : Int) ≡ 0 [ZMOD F.modulus.toNat] := by
      simpa only [hcoefficientZero] using hepilogue.2.2
    have houtZeroMod : out.toNat ≡ 0 [MOD F.modulus.toNat] :=
      Int.natCast_modEq_iff.mp houtZeroInt
    have houtZero : out.toNat = 0 := by
      rw [Nat.ModEq] at houtZeroMod
      simpa only [Nat.mod_eq_of_lt hepilogue.2.1, Nat.zero_mod] using houtZeroMod
    rcases out with ⟨o0, o1, o2, o3⟩
    have hlimbs : ((o0 = 0 ∧ o1 = 0) ∧ o2 = 0) ∧ o3 = 0 := by
      simpa [Limbs.toNat, Nat.add_eq_zero_iff, Nat.mul_eq_zero] using houtZero
    rcases hlimbs with ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
    simp [Limbs.ofNat]
  · rw [if_neg hzero]
    have hcoefficientResult : (value.toNat : Int) * coefficient.toInt ≡ (R^2 : Nat)
        [ZMOD F.modulus.toNat] := by
      simpa only [hzero, if_false] using hscheduleResult
    have hresultInt : (value.toNat : Int) * out.toNat ≡ (R^2 : Nat)
        [ZMOD F.modulus.toNat] :=
      (hepilogue.2.2.mul_left (value.toNat : Int)).trans hcoefficientResult
    exact Int.natCast_modEq_iff.mp (by
      simpa only [Int.natCast_mul] using hresultInt)

end PastaAsm.X86_64
