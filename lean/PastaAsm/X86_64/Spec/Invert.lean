/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.Fields.Inversion
import PastaAsm.X86_64.Spec.Add
import PastaAsm.X86_64.Spec.FromMont
import PastaAsm.X86_64.Spec.Invert.Adjustment
import PastaAsm.X86_64.Spec.Invert.Correctness

/-!
# Correctness contract for the x86-64 inversion composition

This is the fixed top-level obligation used by `invert_entry_spec`. Intermediate
commits may leave its proof unfinished; merge readiness requires discharging it
without changing the public contract or assuming internal convergence/bounds.
-/

namespace PastaAsm.X86_64

open Spec.Invert Spec.Invert.Convergence Spec.Invert.Normalize

set_option maxRecDepth 2000

/-- Named fixed chunks keep concrete batch reduction out of schedule proofs. -/
private def batch2 (state : InvertState) := invertBatch (invertBatch state)
private def batch4 (state : InvertState) := batch2 (batch2 state)
private def batch8 (state : InvertState) := batch4 (batch4 state)
private def batch15 (state : InvertState) :=
  invertBatch (batch2 (batch4 (batch8 state)))

private theorem batch1_rep (state : InvertState) (start : BatchPoint)
    (hstate : InvertStateRep state start.values start.coeff) :
    ∃ finish : BatchPoint,
      InvertStateRep (invertBatch state) finish.values finish.coeff ∧
      RelationN BatchRel 1 start finish := by
  let view := semolinaBatchView start.values hstate.2.2.2.2.1
  let finish : BatchPoint := ⟨view.nextState, start.coeff.update view.batchMatrix⟩
  refine ⟨finish, (invertBatch_rep state start.values start.coeff hstate view).1, ?_⟩
  exact RelationN.succ ⟨view, rfl, rfl⟩ (RelationN.zero _)

private theorem batch2_rep (state : InvertState) (start : BatchPoint)
    (hstate : InvertStateRep state start.values start.coeff) :
    ∃ finish : BatchPoint,
      InvertStateRep (batch2 state) finish.values finish.coeff ∧
      RelationN BatchRel 2 start finish := by
  obtain ⟨middle, hmiddle, hleft⟩ := batch1_rep state start hstate
  obtain ⟨finish, hfinish, hright⟩ := batch1_rep (invertBatch state) middle hmiddle
  exact ⟨finish, hfinish, hleft.append hright⟩

private theorem batch4_rep (state : InvertState) (start : BatchPoint)
    (hstate : InvertStateRep state start.values start.coeff) :
    ∃ finish : BatchPoint,
      InvertStateRep (batch4 state) finish.values finish.coeff ∧
      RelationN BatchRel 4 start finish := by
  obtain ⟨middle, hmiddle, hleft⟩ := batch2_rep state start hstate
  obtain ⟨finish, hfinish, hright⟩ := batch2_rep (batch2 state) middle hmiddle
  exact ⟨finish, hfinish, hleft.append hright⟩

private theorem batch8_rep (state : InvertState) (start : BatchPoint)
    (hstate : InvertStateRep state start.values start.coeff) :
    ∃ finish : BatchPoint,
      InvertStateRep (batch8 state) finish.values finish.coeff ∧
      RelationN BatchRel 8 start finish := by
  obtain ⟨middle, hmiddle, hleft⟩ := batch4_rep state start hstate
  obtain ⟨finish, hfinish, hright⟩ := batch4_rep (batch4 state) middle hmiddle
  exact ⟨finish, hfinish, hleft.append hright⟩

private theorem batch15_rep (state : InvertState) (start : BatchPoint)
    (hstate : InvertStateRep state start.values start.coeff) :
    ∃ finish : BatchPoint,
      InvertStateRep (batch15 state) finish.values finish.coeff ∧
      RelationN BatchRel 15 start finish := by
  obtain ⟨p8, hp8, h8⟩ := batch8_rep state start hstate
  obtain ⟨p12, hp12, h4⟩ := batch4_rep (batch8 state) p8 hp8
  obtain ⟨p14, hp14, h2⟩ := batch2_rep (batch4 (batch8 state)) p12 hp12
  obtain ⟨finish, hfinish, h1⟩ := batch1_rep (batch2 (batch4 (batch8 state))) p14 hp14
  exact ⟨finish, hfinish, h8.append (h4.append (h2.append h1))⟩

private theorem invertBatches15_eq (state : InvertState) :
    invertBatches 15 state = batch15 state := by
  change batch15 state = batch15 state
  rfl

/-- The coefficient consumed by the epilogue, factored out so execution-state
rewrites never need to traverse the normalization and reduction terms. -/
private def inversionFinalCoefficient (state : InvertState) : PastaAsm.WideLimbs :=
  let matrix := divsteps47 state.a.l0 state.b.l0
  invertLincomb9 state.u state.v matrix.f1 matrix.g1

/-- The arithmetic epilogue, factored out so fixed-schedule execution can be
rewritten by congruence at its state argument. -/
private def inversionEpilogueOutput (coefficient : PastaAsm.WideLimbs)
    (modulus : Limbs) (inv : Nat) : Limbs :=
  let normalized := normalizeCoefficient coefficient modulus
  let low := fromMont normalized.1 modulus inv
  let high1 := reduceOnce normalized.2 modulus
  let high2 := reduceOnce high1 modulus
  let high := reduceOnce high2 modulus
  addMod low high modulus

/-- Expose the fixed fifteen-batch execution through the small output helpers. -/
private theorem invert_eq_batch15_output (value modulus : Limbs) (inv : Nat) :
    invert value modulus inv =
      inversionEpilogueOutput
        (inversionFinalCoefficient
          (batch15 ⟨fromMont value modulus inv, modulus,
            ⟨1, 0, 0, 0, 0, 0, 0, 0, 0⟩,
            ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩)) modulus inv := by
  change inversionEpilogueOutput
      (inversionFinalCoefficient
        (invertBatches 15 ⟨fromMont value modulus inv, modulus,
          ⟨1, 0, 0, 0, 0, 0, 0, 0, 0⟩,
          ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩)) modulus inv = _
  exact congrArg (fun state =>
    inversionEpilogueOutput (inversionFinalCoefficient state) modulus inv)
    (invertBatches15_eq _)

/-- A bounded limb vector representing zero is the canonical zero vector. -/
private theorem limbs_eq_zero_of_bounded_toNat_eq_zero (value : Limbs)
    (_hv : value.Bounded) (hzero : value.toNat = 0) : value = Limbs.ofNat 0 := by
  rcases value with ⟨v0, v1, v2, v3⟩
  simp only [Limbs.toNat] at hzero
  have hwords : v0 = 0 ∧ v1 = 0 ∧ v2 = 0 ∧ v3 = 0 := by omega
  rcases hwords with ⟨rfl, rfl, rfl, rfl⟩
  rfl

private theorem invert_zero_pallas :
    invert (Limbs.ofNat 0) pallasBase.modulus pallasBase.inv = Limbs.ofNat 0 := by
  decide +kernel

private theorem invert_zero_vesta :
    invert (Limbs.ofNat 0) vestaBase.modulus vestaBase.inv = Limbs.ofNat 0 := by
  decide +kernel

/-- The fixed x86-64 composition maps zero to zero at either supported field. -/
private theorem invert_zero (F : PastaField) (hF : IsInversionField F) :
    invert (Limbs.ofNat 0) F.modulus F.inv = Limbs.ofNat 0 := by
  rcases hF with rfl | rfl
  · exact invert_zero_pallas
  · exact invert_zero_vesta

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
  let converted := fromMont value F.modulus F.inv
  obtain ⟨hconvertedBound, hconvertedLt, hconvertedMod⟩ :=
    fromMont_spec value F.modulus F.inv hv F.bounded F.shape F.inv_lt F.inv_spec converted rfl
  by_cases hzero : value.toNat = 0
  · have hvalueZero : value = Limbs.ofNat 0 :=
      limbs_eq_zero_of_bounded_toNat_eq_zero value hv hzero
    have houtZero : invert value F.modulus F.inv = Limbs.ofNat 0 := by
      rw [hvalueZero]
      exact invert_zero F hF
    refine ⟨?_, ?_, ?_⟩
    · rw [houtZero]
      simp [Limbs.Bounded, Limbs.ofNat]
    · rw [houtZero]
      have hp := PastaAsm.X86_64.IsInversionField.pastaSizedOdd hF
      have hmodulusPos : 0 < F.modulus.toNat := (by positivity : 0 < 2^254).trans_le hp.2.1
      simpa only [Limbs.ofNat, Limbs.toNat] using hmodulusPos
    · simp only [hzero, if_pos]
      exact houtZero
  · have hconvertedNe : converted.toNat ≠ 0 := by
      intro hconvertedZero
      have hmodZero : value.toNat % F.modulus.toNat = 0 := by
        simpa only [hconvertedZero, Nat.mul_zero, Nat.zero_mod] using hconvertedMod.symm
      rw [Nat.mod_eq_of_lt hlt] at hmodZero
      exact hzero hmodZero
    have hcoprime : converted.toNat.Coprime F.modulus.toNat :=
      hF.coprime_of_nonzero_of_lt hconvertedNe hconvertedLt
    have hp := PastaAsm.X86_64.IsInversionField.pastaSizedOdd hF
    have hconvertedSmall : converted.toNat < 2^255 := hconvertedLt.trans hp.2.2
    let initial : InvertState :=
      ⟨converted, F.modulus, ⟨1, 0, 0, 0, 0, 0, 0, 0, 0⟩,
        ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
    have hinitial : InvertStateRep initial (converted.toNat, F.modulus.toNat)
        initialCoefficients := by
      exact ⟨hconvertedBound, F.bounded, rfl, rfl, hp.1, wideCoeffRep_one,
        wideCoeffRep_zero⟩
    obtain ⟨finish, hfinish, hschedule⟩ := batch15_rep initial
      ⟨(converted.toNat, F.modulus.toNat), initialCoefficients⟩ hinitial
    let state := batch15 initial
    have hstateEq : state = batch15 initial := rfl
    have hfinishRep : InvertStateRep state finish.values finish.coeff := hfinish
    clear_value state
    have hfinishParts := hfinishRep
    rcases hfinishParts with ⟨hstateABound, hstateBBound, hstateAValue, hstateBValue,
      hstateOdd, hstateURep, hstateVRep⟩
    have hvalues : finish.values =
        semolinaBatchesNat 15 (converted.toNat, F.modulus.toNat) := by
      simpa only using batchSchedule_values hschedule
    have hword := semolinaBatches15_lt_word hconvertedSmall hp.2.2 hp.1 hcoprime.gcd_eq_one
    have hfinishWord : finish.values.1 < 2^64 ∧ finish.values.2 < 2^64 := by
      rwa [hvalues]
    have hstateAWord : state.a.toNat < 2^64 := by rw [hstateAValue]; exact hfinishWord.1
    have hstateBWord : state.b.toNat < 2^64 := by rw [hstateBValue]; exact hfinishWord.2
    have hstateA0 : state.a.l0 = finish.values.1 := by
      rw [PastaAsm.X86_64.Limbs.l0_eq_toNat_of_lt_word state.a hstateAWord, hstateAValue]
    have hstateB0 : state.b.l0 = finish.values.2 := by
      rw [PastaAsm.X86_64.Limbs.l0_eq_toNat_of_lt_word state.b hstateBWord, hstateBValue]
    let matrix := divsteps47 state.a.l0 state.b.l0
    have hmatrixEq : matrix = divsteps47 state.a.l0 state.b.l0 := rfl
    let final := approxSteps 47 (ApproxState.initial state.a.l0 state.b.l0)
    have hfinalEq : final = approxSteps 47 (ApproxState.initial state.a.l0 state.b.l0) := rfl
    obtain ⟨hmatrix, hfinalOdd, hmatrixBound⟩ :=
      divsteps47_spec state.a.l0 state.b.l0
        (by rw [hstateA0]; exact hfinishWord.1)
        (by rw [hstateB0]; exact hfinishWord.2)
        (by simpa only [hstateB0] using hstateOdd) matrix rfl
    have hmatrixRep : InvertMatrixRep matrix final.matrix := hmatrix
    have hmatrixBoundRep : final.matrix.Bounded (2^47) := hmatrixBound
    rcases hmatrixRep with ⟨hmatrixF0, hmatrixG0, hmatrixF1, hmatrixG1⟩
    rcases hmatrixBoundRep with ⟨hmatrixRow0Bound, hmatrixRow1Bound⟩
    have hterminalB : final.b = 1 := by
      calc
        final.b = (exactSteps 47 (state.a.l0, state.b.l0)).2 := by
          simpa only [final, ApproxState.initial] using
            approxSteps_second 47 (ApproxState.initial state.a.l0 state.b.l0)
        _ = (exactSteps 47 (semolinaBatchesNat 15
            (converted.toNat, F.modulus.toNat))).2 := by rw [hstateA0, hstateB0, hvalues]
        _ = 1 := semolinaBatches15_exactSteps47_second_eq_one
          hconvertedSmall hp.2.2 hp.1 hcoprime.gcd_eq_one
    have htransition : ScaledTransition 47 final.matrix
        ⟨finish.values.1, finish.values.2⟩ ⟨final.a, final.b⟩ := by
      have hrepr := approxSteps_initial_representation 47 state.a.l0 state.b.l0
        (by simpa only [hstateB0] using hstateOdd)
      simpa only [final, hstateA0, hstateB0] using hrepr
    have hterminalBInt : (final.b : Int) = 1 := by exact_mod_cast hterminalB
    clear_value matrix
    clear_value final
    let coefficient := invertLincomb9 state.u state.v matrix.f1 matrix.g1
    obtain ⟨hcoefficientBound, hcoefficientLower, hcoefficientUpper,
        hcoefficientInvariantR⟩ :=
      finalCoefficient_schedule_spec state.u state.v matrix.f1 matrix.g1 hschedule rfl rfl
        htransition hterminalBInt hstateURep hstateVRep hmatrixF1 hmatrixG1 hmatrixRow1Bound
    have hepilogue := invertEpilogue_spec coefficient F.modulus F.inv converted.toNat
      value.toNat hcoefficientBound F.bounded F.shape F.inv_lt F.inv_spec hp
      hcoefficientLower hcoefficientUpper hcoefficientInvariantR hconvertedMod
    have hcoefficientEq : inversionFinalCoefficient (batch15 initial) = coefficient := by
      unfold inversionFinalCoefficient
      rw [← hstateEq, ← hmatrixEq]
    have houtEq : invert value F.modulus F.inv =
        let normalized := normalizeCoefficient coefficient F.modulus
        let low := fromMont normalized.1 F.modulus F.inv
        let high1 := reduceOnce normalized.2 F.modulus
        let high2 := reduceOnce high1 F.modulus
        let high := reduceOnce high2 F.modulus
        addMod low high F.modulus := by
      rw [invert_eq_batch15_output]
      change inversionEpilogueOutput (inversionFinalCoefficient (batch15 initial))
        F.modulus F.inv = inversionEpilogueOutput coefficient F.modulus F.inv
      exact congrArg (fun concreteCoefficient =>
        inversionEpilogueOutput concreteCoefficient F.modulus F.inv) hcoefficientEq
    rw [houtEq]
    simpa only [hzero, if_neg] using hepilogue

end PastaAsm.X86_64
