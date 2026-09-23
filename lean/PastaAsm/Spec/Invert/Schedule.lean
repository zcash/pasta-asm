/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.Spec.Invert.Batch

/-!
# Compact relation iterator shared by both inversion schedules

The induction kernels in this module are entirely generic.  The generated
Semolina computation occurs only behind the one-edge `BatchRel` adapter, never
in an induction motive.
-/

namespace PastaAsm.Spec.Invert.Schedule

open Spec.Invert Spec.Invert.Convergence

/-- A named batch view carries the actual scaled transition without exposing
its approximation computation to schedule induction. -/
theorem SemolinaBatchView.scaledTransition {values : Nat × Nat}
    (view : SemolinaBatchView values) :
    ScaledTransition 31 view.batchMatrix ⟨values.1, values.2⟩
      ⟨view.nextState.1, view.nextState.2⟩ := by
  constructor
  · change (2^31 : Int) * (view.nextState.1 : Int) =
      view.batchMatrix.row0.apply (values.1 : Int) (values.2 : Int)
    rw [view.row0_eq, SignedRow.apply_scale, ← view.numerator_fst]
    rw [view.next_fst, view.quotient_fst]
    have hmul := Int.ediv_mul_cancel view.numerator_fst_dvd
    calc
      (2^31 : Int) * (view.numerators.1 / (2^31 : Int)).natAbs =
          (view.numerators.1 / (2^31 : Int)).natAbs * 2^31 := by ring
      _ = (orient (view.numerators.1 / (2^31 : Int)) *
          (view.numerators.1 / (2^31 : Int))) * 2^31 := by rw [orient_mul_self]
      _ = orient (view.numerators.1 / (2^31 : Int)) * view.numerators.1 := by
        conv_rhs => rhs; rw [← hmul]
        ring
  · change (2^31 : Int) * (view.nextState.2 : Int) =
      view.batchMatrix.row1.apply (values.1 : Int) (values.2 : Int)
    rw [view.row1_eq, SignedRow.apply_scale, ← view.numerator_snd]
    rw [view.next_snd, view.quotient_snd]
    have hmul := Int.ediv_mul_cancel view.numerator_snd_dvd
    calc
      (2^31 : Int) * (view.numerators.2 / (2^31 : Int)).natAbs =
          (view.numerators.2 / (2^31 : Int)).natAbs * 2^31 := by ring
      _ = (orient (view.numerators.2 / (2^31 : Int)) *
          (view.numerators.2 / (2^31 : Int))) * 2^31 := by rw [orient_mul_self]
      _ = orient (view.numerators.2 / (2^31 : Int)) * view.numerators.2 := by
        conv_rhs => rhs; rw [← hmul]
        ring

/-- Exact-length iteration of an arbitrary relation. -/
inductive RelationN {α : Type} (rel : α → α → Prop) : Nat → α → α → Prop
  | zero (a : α) : RelationN rel 0 a a
  | succ {n : Nat} {a b c : α} (head : rel a b) (tail : RelationN rel n b c) :
      RelationN rel (n + 1) a c

/-- Iterate a deterministic state transformer. -/
def applyN {σ : Type} (step : σ → σ) : Nat → σ → σ
  | 0, state => state
  | n + 1, state => applyN step n (step state)

/-- Concatenate two exact-length relation segments. -/
theorem RelationN.append {α : Type} {rel : α → α → Prop}
    {m n : Nat} {a b c : α} (left : RelationN rel m a b)
    (right : RelationN rel n b c) : RelationN rel (n + m) a c := by
  induction left generalizing c with
  | zero a => simpa using right
  | @succ k first next finish head tail ih =>
      simpa only [Nat.add_assoc] using RelationN.succ head (ih right)

/-- Split generic iteration at an arbitrary chunk boundary. -/
theorem applyN_add {σ : Type} (step : σ → σ) (m n : Nat) (state : σ) :
    applyN step (m + n) state = applyN step n (applyN step m state) := by
  induction m generalizing state with
  | zero => simp only [Nat.zero_add, applyN]
  | succ m ih =>
      simp only [Nat.succ_add, applyN]
      exact ih (step state)

/-- A one-edge simulation lifts through an arbitrary exact-length relation. -/
theorem RelationN.lift {α σ : Type} {rel : α → α → Prop} {step : σ → σ}
    {rep : σ → α → Prop} (hone : ∀ {state before after},
      rel before after → rep state before → rep (step state) after)
    {n : Nat} {state : σ} {before after : α}
    (schedule : RelationN rel n before after) (hrep : rep state before) :
    rep (applyN step n state) after := by
  induction schedule generalizing state with
  | zero a => simpa [applyN] using hrep
  | succ head tail ih =>
      simpa only [applyN] using ih (hone head hrep)

/-- A one-edge indexed proof and a left-composition rule lift through an
arbitrary exact-length relation. -/
theorem RelationN.fold {α : Type} {rel : α → α → Prop}
    {proof : Nat → α → α → Prop}
    (hzero : ∀ a, proof 0 a a)
    (hone : ∀ {a b}, rel a b → proof 1 a b)
    (hcons : ∀ {n a b c}, proof 1 a b → proof n b c → proof (n + 1) a c)
    {n : Nat} {a b : α} (schedule : RelationN rel n a b) : proof n a b := by
  induction schedule with
  | zero a => exact hzero a
  | succ head tail ih => exact hcons (hone head) ih

/-- The abstract data needed at a concrete batch boundary. -/
structure BatchPoint where
  values : Nat × Nat
  coeff : CoeffPair

/-- One edge hides a named opaque view while retaining only its successor data. -/
def BatchRel (before after : BatchPoint) : Prop :=
  ∃ view : SemolinaBatchView before.values,
    view.nextState = after.values ∧ before.coeff.update view.batchMatrix = after.coeff

/-- The value pair of the shared approximation iterator is the exact iterator. -/
theorem approxSteps_pair (n : Nat) (state : ApproxState) :
    ((approxSteps n state).a, (approxSteps n state).b) =
      exactSteps n (state.a, state.b) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      rw [approxSteps, exactSteps]
      have hstep : ((approxStep state).a, (approxStep state).b) =
          exactStep state.a state.b := by
        unfold approxStep exactStep
        split_ifs <;> rfl
      rw [ih, hstep]

/-- Scalar second-coordinate form of `approxSteps_pair`; specializing this
opaque theorem does not unfold a fixed approximation trace. -/
theorem approxSteps_second (n : Nat) (state : ApproxState) :
    (approxSteps n state).b =
      (exactSteps n (state.a, state.b)).2 :=
  congrArg Prod.snd (approxSteps_pair n state)

/-- A schedule of opaque edges exists for every requested length from an odd
second state. -/
theorem exists_batchSchedule (n : Nat) (start : BatchPoint) (hodd : Odd start.values.2) :
    ∃ finish : BatchPoint, RelationN BatchRel n start finish ∧
      finish.values = semolinaBatchesNat n start.values := by
  induction n generalizing start with
  | zero =>
      exact ⟨start, RelationN.zero start, rfl⟩
  | succ n ih =>
      let view := semolinaBatchView start.values hodd
      let next : BatchPoint :=
        ⟨view.nextState, start.coeff.update view.batchMatrix⟩
      obtain ⟨finish, htail, hvalues⟩ := ih next view.next_odd
      refine ⟨finish, RelationN.succ ?_ htail, ?_⟩
      · exact ⟨view, rfl, rfl⟩
      · rw [hvalues]
        simp only [semolinaBatchesNat_succ, next, view.next_eq]

/-- After the fixed prefix, both natural states fit in the low machine word. -/
theorem semolinaBatches15_lt_word {a b : Nat}
    (ha : a < 2^255) (hbBound : b < 2^255) (hb : Odd b)
    (hgcd : Nat.gcd a b = 1) :
    (semolinaBatchesNat 15 (a, b)).1 < 2^64 ∧
      (semolinaBatchesNat 15 (a, b)).2 < 2^64 := by
  have hprogress := semolinaBatches15_terminal_or_length_le_45 ha hbBound hb
  rcases hprogress with hzero | hlength
  · have hgcdAfter := (semolinaBatchesNat_preserves_gcd_and_odd 15
      (a := a) (b := b) hb).1.trans hgcd
    have hsecond : (semolinaBatchesNat 15 (a, b)).2 = 1 := by
      simpa only [hzero, Nat.gcd_zero_left] using hgcdAfter
    rw [hzero, hsecond]
    norm_num
  · unfold lengthSum at hlength
    have hfirstBits : bitLength (semolinaBatchesNat 15 (a, b)).1 ≤ 45 := by omega
    have hsecondBits : bitLength (semolinaBatchesNat 15 (a, b)).2 ≤ 45 := by omega
    constructor
    · exact (lt_two_pow_bitLength _).trans_le
        (Nat.pow_le_pow_right (by omega) (hfirstBits.trans (by omega)))
    · exact (lt_two_pow_bitLength _).trans_le
        (Nat.pow_le_pow_right (by omega) (hsecondBits.trans (by omega)))

/-- The fixed exact tail has second coordinate one after the fifteen-batch
prefix. This scalar corollary avoids projecting the large pair endpoint proof. -/
theorem semolinaBatches15_exactSteps47_second_eq_one {a b : Nat}
    (ha : a < 2^255) (hbBound : b < 2^255) (hb : Odd b)
    (hgcd : Nat.gcd a b = 1) :
    (exactSteps 47 (semolinaBatchesNat 15 (a, b))).2 = 1 := by
  have hschedule := semolinaBatches15_terminal_or_length_le_45 ha hbBound hb
  have hproduct :
      (semolinaBatchesNat 15 (a, b)).1 * (semolinaBatchesNat 15 (a, b)).2 < 2^47 := by
    rcases hschedule with hzero | hlength
    · rw [hzero, Nat.zero_mul]
      positivity
    · exact (product_lt_two_pow_of_lengthSum_le hlength).trans
        (Nat.pow_lt_pow_right (by omega) (by omega))
  have hterminal := exactSteps_47_state_product_eq_zero
    (semolinaBatchesNat 15 (a, b)) hproduct
  have hbatchInv := semolinaBatchesNat_preserves_gcd_and_odd 15
    (a := a) (b := b) hb
  have hafterOdd : Odd (semolinaBatchesNat 15 (a, b)).2 := hbatchInv.2
  have hfinishOdd : Odd (exactSteps 47 (semolinaBatchesNat 15 (a, b))).2 :=
    exactSteps_state_second_odd 47 (semolinaBatchesNat 15 (a, b)) hafterOdd
  have hfinishSecondNe : (exactSteps 47 (semolinaBatchesNat 15 (a, b))).2 ≠ 0 := by
    rcases hfinishOdd with ⟨k, hk⟩
    omega
  have hfinishFirst : (exactSteps 47 (semolinaBatchesNat 15 (a, b))).1 = 0 := by
    rcases hterminal with hzero | hzero
    · exact hzero
    · exact (hfinishSecondNe hzero).elim
  have hafterCoprime :
      Nat.Coprime (semolinaBatchesNat 15 (a, b)).1
        (semolinaBatchesNat 15 (a, b)).2 := by
    rw [Nat.coprime_iff_gcd_eq_one]
    exact hbatchInv.1.trans hgcd
  have hfinishCoprime :
      Nat.Coprime (exactSteps 47 (semolinaBatchesNat 15 (a, b))).1
        (exactSteps 47 (semolinaBatchesNat 15 (a, b))).2 :=
    exactSteps_state_coprime 47 (semolinaBatchesNat 15 (a, b)) hafterOdd hafterCoprime
  simpa only [Nat.coprime_zero_left, hfinishFirst] using hfinishCoprime


/-- A flat schedule's endpoint is the shared natural batch iterator. -/
theorem batchSchedule_values {n : Nat} {before after : BatchPoint}
    (schedule : RelationN BatchRel n before after) :
    after.values = semolinaBatchesNat n before.values := by
  induction schedule with
  | zero point => rfl
  | @succ n first next finish edge tail ih =>
      rcases edge with ⟨view, hvalues, _⟩
      rw [ih, ← hvalues, view.next_eq]
      rfl

/-- A flat schedule also records the shared bounded coefficient batches. -/
theorem batchSchedule_batches {n : Nat} {before after : BatchPoint}
    (schedule : RelationN BatchRel n before after) :
    Batches 31 n before.coeff after.coeff := by
  apply schedule.fold (proof := fun n a b => Batches 31 n a.coeff b.coeff)
  · exact fun point => Batches.zero point.coeff
  · intro a b hedge
    rcases hedge with ⟨view, _, hcoeff⟩
    exact Batches.succ view.batchMatrix view.matrix_bounded hcoeff.symm (Batches.zero _)
  · intro n a b c head tail
    cases head with
    | succ matrix hmatrix hcoeff rest =>
        cases rest
        exact Batches.succ matrix hmatrix hcoeff tail

/-- The complete fixed prefix and final matrix give the honest schedule bound
for the second-row coefficient. -/
theorem schedule_row1_coefficient_bound {coeff : CoeffPair} {row : SignedRow}
    (hbatches : Batches 31 15 initialCoefficients coeff)
    (hrow : row.norm ≤ 2^47) :
    (row.apply coeff.first coeff.second).natAbs ≤ 2^scheduleBits :=
  full_schedule_coefficient_bound hbatches hrow

/-- At terminal second coordinate one, the accumulated prefix and final-tail
scales are exactly the complete schedule scale. -/
theorem final_coefficient_invariant {modulus input coefficient finalB : Int}
    (hsecond : modulus ∣
      (1 * 2^prefixBits * 2^47) * finalB - coefficient * input)
    (hfinalB : finalB = 1) :
    modulus ∣ (2^scheduleBits : Int) - coefficient * input := by
  rw [hfinalB] at hsecond
  simpa only [scheduleBits, Nat.mul_one, pow_add] using hsecond

/-- A final scaled transition ending in second coordinate one exposes the
second coefficient's complete-schedule congruence without exporting the full
transported invariant proof. -/
theorem transition_final_coefficient_invariant
    {modulus input : Int} {before : GCDState} {coeff : CoeffPair}
    {matrix : SignedMatrix} {after : GCDState}
    (htransition : ScaledTransition 47 matrix before after)
    (hinvariant : CoeffInvariant modulus input (1 * 2^prefixBits) before coeff)
    (hafter : after.second = 1) :
    modulus ∣ (2^scheduleBits : Int) - matrix.row1.apply coeff.first coeff.second * input := by
  have hfinal := htransition.preserves_invariant hinvariant
  exact final_coefficient_invariant hfinal.2 (by exact_mod_cast hafter)

/-- The coefficient congruence invariant follows the same flat schedule. -/
theorem batchSchedule_preserves_invariant {n : Nat} {before after : BatchPoint}
    {modulus input scale : Int} (schedule : RelationN BatchRel n before after)
    (hinvariant : CoeffInvariant modulus input scale
      ⟨before.values.1, before.values.2⟩ before.coeff) :
    CoeffInvariant modulus input (scale * 2^(31 * n))
      ⟨after.values.1, after.values.2⟩ after.coeff := by
  induction schedule generalizing scale with
  | zero point => simpa using hinvariant
  | @succ n first next finish edge tail ih =>
      rcases edge with ⟨view, hvalues, hcoeff⟩
      have hone := (Spec.Invert.Schedule.SemolinaBatchView.scaledTransition view).preserves_invariant
        hinvariant
      have hnext : CoeffInvariant modulus input (scale * 2^31)
          ⟨next.values.1, next.values.2⟩ next.coeff := by
        rw [← hvalues, ← hcoeff]
        exact hone
      have htail := ih hnext
      have hscale : (scale * 2^31) * 2^(31 * n) =
          scale * 2^(31 * (n + 1)) := by
        rw [Nat.mul_add, pow_add]
        ring
      rw [← hscale]
      exact htail

/-- Fold the fixed prefix invariant and final-tail transition behind one opaque
boundary, so concrete callers retain only the resulting coefficient congruence. -/
theorem schedule_transition_final_coefficient_invariant
    {modulus input : Int} {start finish : BatchPoint}
    {matrix : SignedMatrix} {after : GCDState}
    (schedule : RelationN BatchRel 15 start finish)
    (hinitial : CoeffInvariant modulus input 1
      ⟨start.values.1, start.values.2⟩ start.coeff)
    (htransition : ScaledTransition 47 matrix
      ⟨finish.values.1, finish.values.2⟩ after)
    (hafter : after.second = 1) :
    modulus ∣ (2^scheduleBits : Int) -
      matrix.row1.apply finish.coeff.first finish.coeff.second * input := by
  have hprefix := batchSchedule_preserves_invariant schedule hinitial
  exact transition_final_coefficient_invariant htransition hprefix hafter

/-- Specialization of the complete coefficient invariant to the driver's
identity initial coefficients.  Keeping this construction behind an opaque
boundary avoids elaborating the transported invariant in the concrete driver. -/
theorem schedule_identity_final_coefficient_invariant
    {modulus input : Nat} {start finish : BatchPoint}
    {matrix : SignedMatrix} {after : GCDState}
    (schedule : RelationN BatchRel 15 start finish)
    (hstartValues : start.values = (input, modulus))
    (hstartCoeff : start.coeff = initialCoefficients)
    (htransition : ScaledTransition 47 matrix
      ⟨finish.values.1, finish.values.2⟩ after)
    (hafter : after.second = 1) :
    (modulus : Int) ∣ (2^scheduleBits : Int) -
      matrix.row1.apply finish.coeff.first finish.coeff.second * input := by
  have hinitial : CoeffInvariant (modulus : Int) input 1
      ⟨start.values.1, start.values.2⟩ start.coeff := by
    rw [hstartValues, hstartCoeff]
    constructor
    · simp [initialCoefficients]
    · refine ⟨1, ?_⟩
      simp [initialCoefficients]
  exact schedule_transition_final_coefficient_invariant schedule hinitial htransition hafter

end PastaAsm.Spec.Invert.Schedule
