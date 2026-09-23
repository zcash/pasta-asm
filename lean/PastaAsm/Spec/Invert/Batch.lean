/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.Spec.Invert.FarLength
import PastaAsm.Spec.Invert.NearLength
import Mathlib.Data.Nat.Prime.Basic

/-!
# GCD preservation of an approximation batch

The actual Semolina batch divides two signed matrix numerators by `2^31` and
then conditionally negates them.  This module proves that this normalized state
retains the input GCD and has an odd second component.  The proof uses the
actual scaled transition and determinant, rather than identifying the
approximation-controlled trace with an exact full-width binary-GCD trace.
-/

namespace PastaAsm.Spec.Invert.Convergence

/-- A scaled two-row transition with determinant magnitude equal to its scale
preserves the natural GCD when the designated second component is odd before
and after the transition.  Oddness makes every divisor of either GCD coprime
to the power-of-two scale, so the scale can be cancelled in both directions. -/
theorem scaledTransition_gcd_eq_of_det_natAbs {bits : Nat} {m : SignedMatrix}
    {a b c d : Nat}
    (htransition : ScaledTransition bits m ⟨a, b⟩ ⟨c, d⟩)
    (hdet : (matrixDet m).natAbs = 2^bits) (hb : Odd b) (hd : Odd d) :
    Nat.gcd c d = Nat.gcd a b := by
  let beforeGCD := Nat.gcd a b
  let afterGCD := Nat.gcd c d
  have hbeforeA : beforeGCD ∣ a := Nat.gcd_dvd_left a b
  have hbeforeB : beforeGCD ∣ b := Nat.gcd_dvd_right a b
  have hbeforeAInt : (beforeGCD : Int) ∣ (a : Int) := Int.natCast_dvd_natCast.mpr hbeforeA
  have hbeforeBInt : (beforeGCD : Int) ∣ (b : Int) := Int.natCast_dvd_natCast.mpr hbeforeB
  have hbeforeRow0 : (beforeGCD : Int) ∣ m.row0.apply a b := by
    exact dvd_add (hbeforeAInt.mul_left m.row0.left) (hbeforeBInt.mul_left m.row0.right)
  have hbeforeRow1 : (beforeGCD : Int) ∣ m.row1.apply a b := by
    exact dvd_add (hbeforeAInt.mul_left m.row1.left) (hbeforeBInt.mul_left m.row1.right)
  have hbeforeScaleCInt : (beforeGCD : Int) ∣ (2^bits : Int) * c := by
    rw [htransition.1]
    exact hbeforeRow0
  have hbeforeScaleDInt : (beforeGCD : Int) ∣ (2^bits : Int) * d := by
    rw [htransition.2]
    exact hbeforeRow1
  have hbeforeScaleC : beforeGCD ∣ 2^bits * c := by
    exact_mod_cast hbeforeScaleCInt
  have hbeforeScaleD : beforeGCD ∣ 2^bits * d := by
    exact_mod_cast hbeforeScaleDInt
  have hbeforeOdd : Odd beforeGCD := by
    exact hb.of_dvd_nat hbeforeB
  have hbeforeCoprime : Nat.Coprime beforeGCD (2^bits) :=
    (hbeforeOdd.coprime_two_right).pow_right bits
  have hbeforeC : beforeGCD ∣ c :=
    hbeforeCoprime.dvd_of_dvd_mul_left hbeforeScaleC
  have hbeforeD : beforeGCD ∣ d :=
    hbeforeCoprime.dvd_of_dvd_mul_left hbeforeScaleD
  have hbeforeAfter : beforeGCD ∣ afterGCD := Nat.dvd_gcd hbeforeC hbeforeD

  have hafterC : afterGCD ∣ c := Nat.gcd_dvd_left c d
  have hafterD : afterGCD ∣ d := Nat.gcd_dvd_right c d
  have hafterCInt : (afterGCD : Int) ∣ (c : Int) := Int.natCast_dvd_natCast.mpr hafterC
  have hafterDInt : (afterGCD : Int) ∣ (d : Int) := Int.natCast_dvd_natCast.mpr hafterD
  have hafterScaleC : (afterGCD : Int) ∣ (2^bits : Int) * c := hafterCInt.mul_left _
  have hafterScaleD : (afterGCD : Int) ∣ (2^bits : Int) * d := hafterDInt.mul_left _
  have hafterRow0 : (afterGCD : Int) ∣ m.row0.apply a b := by
    rw [← htransition.1]
    exact hafterScaleC
  have hafterRow1 : (afterGCD : Int) ∣ m.row1.apply a b := by
    rw [← htransition.2]
    exact hafterScaleD
  have hafterDetAInt : (afterGCD : Int) ∣ matrixDet m * (a : Int) := by
    unfold SignedRow.apply at hafterRow0 hafterRow1
    unfold matrixDet
    have hcomb := dvd_sub (hafterRow0.mul_left m.row1.right)
      (hafterRow1.mul_left m.row0.right)
    convert hcomb using 1
    all_goals ring
  have hafterDetBInt : (afterGCD : Int) ∣ matrixDet m * (b : Int) := by
    unfold SignedRow.apply at hafterRow0 hafterRow1
    unfold matrixDet
    have hcomb := dvd_sub (hafterRow1.mul_left m.row0.left)
      (hafterRow0.mul_left m.row1.left)
    convert hcomb using 1
    all_goals ring
  have hafterDetA : afterGCD ∣ (matrixDet m).natAbs * a := by
    simpa [Int.natAbs_mul] using Int.natCast_dvd.mp hafterDetAInt
  have hafterDetB : afterGCD ∣ (matrixDet m).natAbs * b := by
    simpa [Int.natAbs_mul] using Int.natCast_dvd.mp hafterDetBInt
  have hafterScaleA : afterGCD ∣ 2^bits * a := by simpa [hdet] using hafterDetA
  have hafterScaleB : afterGCD ∣ 2^bits * b := by simpa [hdet] using hafterDetB
  have hafterOdd : Odd afterGCD := by
    exact hd.of_dvd_nat hafterD
  have hafterCoprime : Nat.Coprime afterGCD (2^bits) :=
    (hafterOdd.coprime_two_right).pow_right bits
  have hafterA : afterGCD ∣ a := hafterCoprime.dvd_of_dvd_mul_left hafterScaleA
  have hafterB : afterGCD ∣ b := hafterCoprime.dvd_of_dvd_mul_left hafterScaleB
  have hafterBefore : afterGCD ∣ beforeGCD := Nat.dvd_gcd hafterA hafterB
  exact Nat.dvd_antisymm hafterBefore hbeforeAfter

/-- Conditional row negation changes the determinant only by a sign, so the
actual normalized batch matrix still has determinant magnitude `2^31`. -/
theorem semolinaBatch_det_natAbs (a b : Nat) :
    (matrixDet (semolinaBatchMatrix a b)).natAbs = 2^31 := by
  let q := semolinaQuotients a b
  let m := (semolinaShort a b).matrix
  have horient (x : Int) : (orient x).natAbs = 1 := by
    unfold orient
    split_ifs <;> simp
  have hmatrix : matrixDet (semolinaBatchMatrix a b) =
      orient q.1 * orient q.2 * matrixDet m := by
    simp only [semolinaBatchMatrix, q, m, matrixDet, SignedRow.scale]
    ring
  rw [hmatrix, Int.natAbs_mul, Int.natAbs_mul, horient, horient,
    one_mul, semolinaShort_det_natAbs]
  simp

/-- If the second signed real quotient is odd, one actual approximation-chosen
quotient step leaves its second quotient odd.  In the swap branch this follows
from the low-bit agreement for the first quotient. -/
theorem signedQuotientStep_second_odd {controlA controlB : Nat} {realA realB : Int}
    (hparity : realA % 2 = (controlA : Int) % 2) (hodd : Odd realB) :
    Odd (signedQuotientStep (controlA, controlB) (realA, realB)).2 := by
  unfold signedQuotientStep
  by_cases heven : Even controlA
  · rw [if_pos heven]
    exact hodd
  · rw [if_neg heven]
    split_ifs
    · exact hodd
    · rw [Int.odd_iff]
      rw [hparity]
      exact_mod_cast (Nat.odd_iff.mp (Nat.not_even_iff_odd.mp heven))

/-- The second actual full-width signed quotient remains odd through every
prefix of the concrete 31-operation approximation-controlled batch. -/
theorem semolinaPrefixReal_second_odd {a b t : Nat} (hb : Odd b) (ht : t ≤ 31) :
    Odd (semolinaPrefixReal a b t).2 := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
      cases t with
      | zero =>
          simpa [semolinaPrefixReal, semolinaApprox, ApproxState.initial,
            approxSteps, SignedRow.apply, identityMatrix] using hb
      | succ t =>
          have htlt : t < 31 := by omega
          have hprevious : Odd (semolinaPrefixReal a b t).2 := ih t (by omega) (by omega)
          have hparity := (semolina_prefix_quotient_emod_two (a := a) (b := b)
            (t := t) hb htlt).1
          rw [semolinaPrefixReal_succ hb htlt]
          apply signedQuotientStep_second_odd (hodd := hprevious)
          simpa [semolinaPrefixReal, semolinaPrefixApprox] using hparity

/-- The second signed quotient produced by the complete actual Semolina short
batch is odd. -/
theorem semolinaQuotients_snd_odd {a b : Nat} (hb : Odd b) :
    Odd (semolinaQuotients a b).2 := by
  have hodd := semolinaPrefixReal_second_odd (a := a) (b := b) (t := 31) hb (by omega)
  simpa [semolinaPrefixReal, semolinaQuotients, semolinaNumerators, semolinaShort] using hodd

/-- One actual full-width normalized Semolina batch preserves the input GCD and
keeps its designated second state odd.  No nonzero hypothesis on `a` is needed. -/
theorem semolinaBatch_preserves_gcd_and_odd (a b : Nat) (hb : Odd b) :
    Nat.gcd (semolinaBatchState a b).first.natAbs
        (semolinaBatchState a b).second.natAbs = Nat.gcd a b ∧
      Odd (semolinaBatchState a b).second := by
  let q := semolinaQuotients a b
  have htransition : ScaledTransition 31 (semolinaBatchMatrix a b)
      ⟨a, b⟩ ⟨q.1.natAbs, q.2.natAbs⟩ := by
    simpa [semolinaBatchState, q] using semolinaBatch_transition a b hb
  have hqodd : Odd q.2 := by simpa [q] using semolinaQuotients_snd_odd hb
  have hnatOdd : Odd q.2.natAbs := hqodd.natAbs
  have hfirst : (semolinaBatchState a b).first = (q.1.natAbs : Int) := rfl
  have hsecond : (semolinaBatchState a b).second = (q.2.natAbs : Int) := rfl
  rw [hfirst, hsecond]
  simp only [Int.natAbs_natCast]
  constructor
  · exact scaledTransition_gcd_eq_of_det_natAbs htransition
      (semolinaBatch_det_natAbs a b) hb hnatOdd
  · exact_mod_cast hnatOdd

/-- If the full-width state fits in the approximation window, the concrete
Semolina approximation is the identity. -/
theorem semolinaApprox_eq_of_max_bitLength_le_64 {a b : Nat}
    (hsmall : max (bitLength a) (bitLength b) ≤ 64) :
    semolinaApprox a b = (a, b) := by
  simp [semolinaApprox, approximate, hsmall]

/-- Componentwise absolute value of a signed quotient pair. -/
def quotientNatAbs (q : Int × Int) : Nat × Nat := (q.1.natAbs, q.2.natAbs)

/-- The nonnegative natural view of one actual normalized Semolina batch. -/
def semolinaBatchNat (state : Nat × Nat) : Nat × Nat :=
  quotientNatAbs (semolinaQuotients state.1 state.2)

/-- Shallow pair equation for consumers that must not unfold the concrete
approximation-controlled quotient computation. -/
theorem semolinaBatchNat_pair (a b : Nat) :
    semolinaBatchNat (a, b) =
      ((semolinaQuotients a b).1.natAbs, (semolinaQuotients a b).2.natAbs) := rfl

/-- In the exact approximation regime, the actual normalized batch follows the
existing exact iterator for all 31 operations. -/
theorem semolinaBatchNat_eq_exactSteps_of_max_bitLength_le_64 {a b : Nat}
    (hb : Odd b) (hsmall : max (bitLength a) (bitLength b) ≤ 64) :
    semolinaBatchNat (a, b) = exactSteps 31 (a, b) := by
  let s := approxSteps 31 (ApproxState.initial a b)
  have happ : semolinaApprox a b = (a, b) :=
    semolinaApprox_eq_of_max_bitLength_le_64 hsmall
  have hshort : semolinaShort a b = s := by
    simp [semolinaShort, happ, s]
  have hrepr := approxSteps_initial_representation 31 a b hb
  have hqA : (semolinaQuotients a b).1 = (s.a : Int) := by
    simp only [semolinaQuotients, semolinaNumerators, hshort]
    rw [← hrepr.1]
    change (2^31 : Int) * (s.a : Int) / (2^31 : Int) = (s.a : Int)
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  have hqB : (semolinaQuotients a b).2 = (s.b : Int) := by
    simp only [semolinaQuotients, semolinaNumerators, hshort]
    rw [← hrepr.2]
    change (2^31 : Int) * (s.b : Int) / (2^31 : Int) = (s.b : Int)
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  have hvalues := approxSteps_value_pair 31 (ApproxState.initial a b)
  unfold semolinaBatchNat quotientNatAbs
  rw [hqA, hqB, Int.natAbs_natCast, Int.natAbs_natCast]
  exact hvalues

/-- The first approximation control is zero when the full-width first state is
zero, independently of the size of the odd second state. -/
theorem semolinaApprox_zero_first (b : Nat) : (semolinaApprox 0 b).1 = 0 := by
  unfold semolinaApprox approximate
  dsimp only
  by_cases hsmall : bitLength b ≤ 64
  · rw [if_pos (by simpa using hsmall)]
  · rw [if_neg (by simpa using hsmall)]
    simp

/-- A zero first full-width state is absorbing for the actual signed quotient
batch; the second quotient is unchanged. -/
theorem semolinaQuotients_zero_first (b : Nat) :
    semolinaQuotients 0 b = (0, (b : Int)) := by
  let ap := semolinaApprox 0 b
  let initial := ControlledState.initial ap.1 ap.2 0 b
  let finish := controlledSteps 31 initial
  have hap : ap.1 = 0 := by simpa [ap] using semolinaApprox_zero_first b
  have hzero := controlledSteps_zero_approxA 31 (s := initial) (by
    simpa [initial] using hap)
  have hmatches := semolina_controlled_prefix 0 b 31
  have hnumA : finish.scaledRealA = (semolinaNumerators 0 b).1 := by
    simpa [finish, initial, ap, semolinaNumerators, semolinaShort] using hmatches.2.2.1
  have hnumB : finish.scaledRealB = (semolinaNumerators 0 b).2 := by
    simpa [finish, initial, ap, semolinaNumerators, semolinaShort] using hmatches.2.2.2
  have hfinishA : finish.scaledRealA = 0 := by
    simpa [finish, initial] using hzero.2.2.1
  have hfinishB : finish.scaledRealB = (2^31 : Int) * b := by
    simpa [finish, initial] using hzero.2.2.2
  apply Prod.ext
  · change (semolinaNumerators 0 b).1 / (2^31 : Int) = 0
    rw [← hnumA, hfinishA]
    simp
  · change (semolinaNumerators 0 b).2 / (2^31 : Int) = b
    rw [← hnumB, hfinishB]
    exact Int.mul_ediv_cancel_left _ (by positivity)

/-- A zero first natural state is absorbing for the normalized batch. -/
@[simp] theorem semolinaBatchNat_zero_first (b : Nat) :
    semolinaBatchNat (0, b) = (0, b) := by
  unfold semolinaBatchNat quotientNatAbs
  rw [semolinaQuotients_zero_first]
  simp

private theorem quotientNatAbs_terminal_or_length_progress {q : Int × Int} {bound : Nat}
    (h : q.1 = 0 ∨ signedLengthSum q.1 q.2 + 31 ≤ bound) :
    (quotientNatAbs q).1 = 0 ∨
      lengthSum (quotientNatAbs q).1 (quotientNatAbs q).2 + 31 ≤ bound := by
  unfold quotientNatAbs
  rcases h with hzero | hlen
  · exact Or.inl (Int.natAbs_eq_zero.mpr hzero)
  · exact Or.inr hlen

/-- Unified progress theorem for one actual 31-operation Semolina batch.  It
covers the exact (`n ≤ 64`), near-length, and far-length regimes. -/
theorem semolinaBatchNat_terminal_or_length_progress {a b : Nat}
    (ha : 0 < a) (hb : Odd b) :
    (semolinaBatchNat (a, b)).1 = 0 ∨
      lengthSum (semolinaBatchNat (a, b)).1 (semolinaBatchNat (a, b)).2 + 31 ≤
        lengthSum a b := by
  let n := max (bitLength a) (bitLength b)
  by_cases hsmall : n ≤ 64
  · have heq := semolinaBatchNat_eq_exactSteps_of_max_bitLength_le_64 hb
      (by simpa [n] using hsmall)
    have hprogress := exactSteps_terminal_or_length_progress 31 (a := a) (b := b) hb
    rw [heq]
    exact hprogress
  · have hlarge : 64 < n := by omega
    have hbPos : 0 < b := Odd.pos hb
    have hlarge' : 64 < max (bitLength a) (bitLength b) := by
      exact hlarge
    have hprogress : (semolinaQuotients a b).1 = 0 ∨
        signedLengthSum (semolinaQuotients a b).1 (semolinaQuotients a b).2 + 31 ≤
          lengthSum a b := by
      by_cases haNear : n - 32 < bitLength a
      · by_cases hbNear : n - 32 < bitLength b
        · have haNear' : max (bitLength a) (bitLength b) - 32 < bitLength a := haNear
          have hbNear' : max (bitLength a) (bitLength b) - 32 < bitLength b := hbNear
          exact semolinaNear_terminal_or_length_progress ha hbPos hb
            hlarge' haNear' hbNear'
        · have hbFar : bitLength b ≤ n - 32 := by omega
          have haMax : bitLength a = n := by
            dsimp [n]
            omega
          exact semolinaFar_terminal_or_length_progress ha hbPos hb rfl hlarge
            (Or.inl ⟨haMax, hbFar⟩)
      · have haFar : bitLength a ≤ n - 32 := by omega
        have hbMax : bitLength b = n := by
          dsimp [n]
          omega
        exact semolinaFar_terminal_or_length_progress ha hbPos hb rfl hlarge
          (Or.inr ⟨hbMax, haFar⟩)
    change (quotientNatAbs (semolinaQuotients a b)).1 = 0 ∨
      lengthSum (quotientNatAbs (semolinaQuotients a b)).1
          (quotientNatAbs (semolinaQuotients a b)).2 + 31 ≤ lengthSum a b
    exact quotientNatAbs_terminal_or_length_progress hprogress

/-- One natural normalized batch preserves GCD and oddness of the designated
second state. -/
theorem semolinaBatchNat_preserves_gcd_and_odd {a b : Nat} (hb : Odd b) :
    Nat.gcd (semolinaBatchNat (a, b)).1 (semolinaBatchNat (a, b)).2 = Nat.gcd a b ∧
      Odd (semolinaBatchNat (a, b)).2 := by
  have hqodd : Odd (semolinaQuotients a b).2 := semolinaQuotients_snd_odd hb
  have hnatOdd : Odd (semolinaQuotients a b).2.natAbs := hqodd.natAbs
  have htransition : ScaledTransition 31 (semolinaBatchMatrix a b) ⟨a, b⟩
      ⟨(semolinaQuotients a b).1.natAbs, (semolinaQuotients a b).2.natAbs⟩ := by
    simpa only [semolinaBatchState] using semolinaBatch_transition a b hb
  have hgcd : Nat.gcd (semolinaQuotients a b).1.natAbs
      (semolinaQuotients a b).2.natAbs = Nat.gcd a b :=
    scaledTransition_gcd_eq_of_det_natAbs htransition
      (semolinaBatch_det_natAbs a b) hb hnatOdd
  rw [semolinaBatchNat_pair]
  simpa only using And.intro hgcd hnatOdd

/-- Fully named arithmetic data for one normalized Semolina batch.  Concrete
ISA proofs can consume these fields without reducing the 31-step approximation
computation. -/
structure SemolinaBatchView (values : Nat × Nat) where
  raw : SignedMatrix
  numerators : Int × Int
  quotients : Int × Int
  nextState : Nat × Nat
  batchMatrix : SignedMatrix
  raw_eq : (semolinaShort values.1 values.2).matrix = raw
  raw_bounded : raw.Bounded (2^31)
  numerator_fst : numerators.1 = raw.row0.apply values.1 values.2
  numerator_snd : numerators.2 = raw.row1.apply values.1 values.2
  numerator_fst_dvd : (2^31 : Int) ∣ numerators.1
  numerator_snd_dvd : (2^31 : Int) ∣ numerators.2
  quotient_fst : quotients.1 = numerators.1 / (2^31 : Int)
  quotient_snd : quotients.2 = numerators.2 / (2^31 : Int)
  next_eq : nextState = semolinaBatchNat values
  next_fst : nextState.1 = quotients.1.natAbs
  next_snd : nextState.2 = quotients.2.natAbs
  row0_eq : batchMatrix.row0 = SignedRow.scale (orient quotients.1) raw.row0
  row1_eq : batchMatrix.row1 = SignedRow.scale (orient quotients.2) raw.row1
  matrix_bounded : batchMatrix.Bounded (2^31)
  next_odd : Odd nextState.2

/-- Opaque shared consumer interface for one actual Semolina batch.  Its
projections expose the exact arithmetic contract while its body prevents WHNF
reduction of the concrete approximation iterator in downstream ISA proofs. -/
opaque semolinaBatchView (values : Nat × Nat) (hodd : Odd values.2) :
    SemolinaBatchView values := by
  rcases values with ⟨a, b⟩
  have hdiv := semolinaShort_full_width_dvd a b hodd
  refine
    { raw := (semolinaShort a b).matrix
      numerators := semolinaNumerators a b
      quotients := semolinaQuotients a b
      nextState := semolinaBatchNat (a, b)
      batchMatrix := semolinaBatchMatrix a b
      raw_eq := rfl
      raw_bounded := semolinaShort_matrix_bounded a b
      numerator_fst := rfl
      numerator_snd := rfl
      numerator_fst_dvd := ?_
      numerator_snd_dvd := ?_
      quotient_fst := rfl
      quotient_snd := rfl
      next_eq := rfl
      next_fst := ?_
      next_snd := ?_
      row0_eq := rfl
      row1_eq := rfl
      matrix_bounded := semolinaBatch_matrix_bounded a b
      next_odd := (semolinaBatchNat_preserves_gcd_and_odd hodd).2 }
  · simpa only [semolinaNumerators] using hdiv.1
  · simpa only [semolinaNumerators] using hdiv.2
  · rw [semolinaBatchNat_pair]
  · rw [semolinaBatchNat_pair]

/-- Iterate an arbitrary state transition.  Keeping the iterator generic prevents
proofs about long schedules from reducing the concrete Semolina quotient term. -/
def iterateState (step : Nat × Nat → Nat × Nat) : Nat → Nat × Nat → Nat × Nat
  | 0, state => state
  | n + 1, state => iterateState step n (step state)

@[simp] theorem iterateState_succ (step : Nat × Nat → Nat × Nat) (n : Nat)
    (state : Nat × Nat) :
    iterateState step (n + 1) state = iterateState step n (step state) := rfl

/-- An absorbing zero-first transition remains absorbing under generic iteration. -/
theorem iterateState_zero_first {step : Nat × Nat → Nat × Nat}
    (hzero : ∀ b, step (0, b) = (0, b)) (n b : Nat) :
    iterateState step n (0, b) = (0, b) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterateState_succ, hzero, ih]

/-- A one-step GCD/oddness invariant lifts to every generic iteration prefix. -/
theorem iterateState_preserves_gcd_and_odd {step : Nat × Nat → Nat × Nat}
    (hinv : ∀ {a b}, Odd b →
      Nat.gcd (step (a, b)).1 (step (a, b)).2 = Nat.gcd a b ∧ Odd (step (a, b)).2)
    (n : Nat) {a b : Nat} (hb : Odd b) :
    Nat.gcd (iterateState step n (a, b)).1 (iterateState step n (a, b)).2 = Nat.gcd a b ∧
      Odd (iterateState step n (a, b)).2 := by
  induction n generalizing a b with
  | zero => exact ⟨rfl, hb⟩
  | succ n ih =>
      rw [iterateState_succ]
      have hone := hinv (a := a) (b := b) hb
      have htail := ih (a := (step (a, b)).1) (b := (step (a, b)).2) hone.2
      rw [Prod.eta (step (a, b))] at htail
      exact ⟨htail.1.trans hone.1, htail.2⟩

/-- Absorption, preservation of oddness, and one-step progress lift to an
accumulated `31*n` bound for a generic transition. -/
theorem iterateState_terminal_or_length_progress {step : Nat × Nat → Nat × Nat}
    (hzero : ∀ b, step (0, b) = (0, b))
    (hodd : ∀ {a b}, Odd b → Odd (step (a, b)).2)
    (hone : ∀ {a b}, 0 < a → Odd b →
      (step (a, b)).1 = 0 ∨
        lengthSum (step (a, b)).1 (step (a, b)).2 + 31 ≤ lengthSum a b)
    (n : Nat) {a b : Nat} (hb : Odd b) :
    (iterateState step n (a, b)).1 = 0 ∨
      lengthSum (iterateState step n (a, b)).1
          (iterateState step n (a, b)).2 + 31 * n ≤ lengthSum a b := by
  induction n generalizing a b with
  | zero =>
      right
      simp [iterateState]
  | succ n ih =>
      by_cases ha : a = 0
      · subst a
        left
        rw [iterateState_succ, hzero, iterateState_zero_first hzero]
      · rw [iterateState_succ]
        rcases hone (Nat.pos_of_ne_zero ha) hb with hnextZero | hnextLength
        · left
          have hnext : step (a, b) = (0, (step (a, b)).2) := Prod.ext hnextZero rfl
          rw [hnext, iterateState_zero_first hzero]
        · have htail := ih (a := (step (a, b)).1) (b := (step (a, b)).2)
              (hodd (a := a) (b := b) hb)
          rw [Prod.eta (step (a, b))] at htail
          rcases htail with htailZero | htailLength
          · exact Or.inl htailZero
          · right
            omega

/-- Iterate the actual nonnegative normalized Semolina batch. -/
def semolinaBatchesNat : Nat → Nat × Nat → Nat × Nat :=
  iterateState semolinaBatchNat

@[simp] theorem semolinaBatchesNat_succ (n : Nat) (state : Nat × Nat) :
    semolinaBatchesNat (n + 1) state = semolinaBatchesNat n (semolinaBatchNat state) := rfl

/-- Once the first state reaches zero, all later normalized batches leave the
natural state unchanged. -/
@[simp] theorem semolinaBatchesNat_zero_first (n b : Nat) :
    semolinaBatchesNat n (0, b) = (0, b) :=
  iterateState_zero_first semolinaBatchNat_zero_first n b

/-- Every prefix of actual normalized batches preserves the initial GCD and
keeps the designated second state odd. -/
theorem semolinaBatchesNat_preserves_gcd_and_odd (n : Nat) {a b : Nat} (hb : Odd b) :
    Nat.gcd (semolinaBatchesNat n (a, b)).1 (semolinaBatchesNat n (a, b)).2 =
        Nat.gcd a b ∧
      Odd (semolinaBatchesNat n (a, b)).2 :=
  iterateState_preserves_gcd_and_odd
    (fun {_ _} h => semolinaBatchNat_preserves_gcd_and_odd h) n hb

/-- Iterating `n` actual batches either reaches the absorbing zero-first state
or charges all `31*n` scheduled operations against the initial joint length. -/
theorem semolinaBatchesNat_terminal_or_length_progress (n : Nat) {a b : Nat} (hb : Odd b) :
    (semolinaBatchesNat n (a, b)).1 = 0 ∨
      lengthSum (semolinaBatchesNat n (a, b)).1
          (semolinaBatchesNat n (a, b)).2 + 31 * n ≤ lengthSum a b :=
  iterateState_terminal_or_length_progress semolinaBatchNat_zero_first
    (fun {_ _} h => (semolinaBatchNat_preserves_gcd_and_odd h).2)
    (fun {_ _} ha h => semolinaBatchNat_terminal_or_length_progress ha h) n hb

/-- Fifteen actual batches from two values below `2^255` either terminate or
leave joint bit length at most `45 = 510 - 15*31`. -/
theorem semolinaBatches15_terminal_or_length_le_45 {a b : Nat}
    (ha : a < 2^255) (hbBound : b < 2^255) (hb : Odd b) :
    (semolinaBatchesNat 15 (a, b)).1 = 0 ∨
      lengthSum (semolinaBatchesNat 15 (a, b)).1
        (semolinaBatchesNat 15 (a, b)).2 ≤ 45 := by
  have haSize : bitLength a ≤ 255 := bitLength_le_of_lt_two_pow ha
  have hbSize : bitLength b ≤ 255 := bitLength_le_of_lt_two_pow hbBound
  have hprogress := semolinaBatchesNat_terminal_or_length_progress 15
    (a := a) (b := b) hb
  rcases hprogress with hzero | hlength
  · exact Or.inl hzero
  · right
    unfold lengthSum at hlength ⊢
    omega

/-- One exact natural binary-GCD step preserves coprimality when the designated
second state is odd. -/
theorem exactStep_coprime {a b : Nat} (hb : Odd b) (hcoprime : Nat.Coprime a b) :
    Nat.Coprime (exactStep a b).1 (exactStep a b).2 := by
  unfold exactStep
  by_cases haEven : Even a
  · rw [if_pos haEven]
    have hdiv : a / 2 ∣ a := by
      refine ⟨2, ?_⟩
      exact (Nat.div_mul_cancel (even_iff_two_dvd.mp haEven)).symm
    exact hcoprime.of_dvd_left hdiv
  · rw [if_neg haEven]
    have haOdd : Odd a := Nat.not_even_iff_odd.mp haEven
    by_cases hba : b ≤ a
    · rw [if_pos hba]
      have hdiffEven : Even (a - b) := by
        rcases haOdd with ⟨qa, hqa⟩
        rcases hb with ⟨qb, hqb⟩
        use qa - qb
        omega
      have hdiv : (a - b) / 2 ∣ a - b := by
        refine ⟨2, ?_⟩
        exact (Nat.div_mul_cancel (even_iff_two_dvd.mp hdiffEven)).symm
      exact ((Nat.coprime_sub_self_left hba).mpr hcoprime).of_dvd_left hdiv
    · have hab : a ≤ b := Nat.le_of_lt (Nat.lt_of_not_ge hba)
      rw [if_neg hba]
      have hdiffEven : Even (b - a) := by
        rcases haOdd with ⟨qa, hqa⟩
        rcases hb with ⟨qb, hqb⟩
        use qb - qa
        omega
      have hdiv : (b - a) / 2 ∣ b - a := by
        refine ⟨2, ?_⟩
        exact (Nat.div_mul_cancel (even_iff_two_dvd.mp hdiffEven)).symm
      exact ((Nat.coprime_sub_self_left hab).mpr hcoprime.symm).of_dvd_left hdiv

/-- Exact iteration preserves coprimality under the standard odd-second
invariant. -/
theorem exactSteps_coprime (n : Nat) {a b : Nat} (hb : Odd b)
    (hcoprime : Nat.Coprime a b) :
    Nat.Coprime (exactSteps n (a, b)).1 (exactSteps n (a, b)).2 := by
  induction n generalizing a b with
  | zero => simpa [exactSteps] using hcoprime
  | succ n ih =>
      rw [exactSteps]
      exact ih (exactStep_second_odd_progress (a := a) hb) (exactStep_coprime hb hcoprime)

/-- Pair-form termination after 47 exact steps, avoiding eta reduction of an
opaque state. -/
theorem exactSteps_47_state_product_eq_zero (state : Nat × Nat)
    (hsmall : state.1 * state.2 < 2^47) :
    (exactSteps 47 state).1 = 0 ∨ (exactSteps 47 state).2 = 0 := by
  rw [← Prod.eta state]
  exact exactSteps_47_product_eq_zero hsmall

/-- Pair-form oddness preservation, avoiding eta reduction of an opaque state. -/
theorem exactSteps_state_second_odd (n : Nat) (state : Nat × Nat) (hodd : Odd state.2) :
    Odd (exactSteps n state).2 := by
  rw [← Prod.eta state]
  exact exactSteps_second_odd_progress n hodd

/-- Pair-form coprimality preservation, avoiding eta reduction of an opaque state. -/
theorem exactSteps_state_coprime (n : Nat) (state : Nat × Nat) (hodd : Odd state.2)
    (hcoprime : Nat.Coprime state.1 state.2) :
    Nat.Coprime (exactSteps n state).1 (exactSteps n state).2 := by
  rw [← Prod.eta state]
  exact exactSteps_coprime n hodd hcoprime

/-- The abstract Semolina schedule: after fifteen actual normalized batches,
47 exact low-state operations finish at `(0, 1)` for coprime inputs below
`2^255`.  This is a theorem about the shared arithmetic state, not an ISA
correspondence theorem. -/
theorem semolinaBatches15_exactSteps47_eq_zero_one {a b : Nat}
    (ha : a < 2^255) (hbBound : b < 2^255) (hb : Odd b)
    (hgcd : Nat.gcd a b = 1) :
    exactSteps 47 (semolinaBatchesNat 15 (a, b)) = (0, 1) := by
  have hschedule := semolinaBatches15_terminal_or_length_le_45 ha hbBound hb
  have hproduct :
      (semolinaBatchesNat 15 (a, b)).1 * (semolinaBatchesNat 15 (a, b)).2 < 2^47 := by
    rcases hschedule with hzero | hlength
    · calc
        (semolinaBatchesNat 15 (a, b)).1 * (semolinaBatchesNat 15 (a, b)).2 = 0 := by
          rw [hzero, Nat.zero_mul]
        _ < 2^47 := by positivity
    · have hlt45 := product_lt_two_pow_of_lengthSum_le hlength
      exact hlt45.trans (Nat.pow_lt_pow_right (by omega) (by omega))
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
      Nat.Coprime (semolinaBatchesNat 15 (a, b)).1 (semolinaBatchesNat 15 (a, b)).2 := by
    rw [Nat.coprime_iff_gcd_eq_one]
    exact hbatchInv.1.trans hgcd
  have hfinishCoprime :
      Nat.Coprime (exactSteps 47 (semolinaBatchesNat 15 (a, b))).1
        (exactSteps 47 (semolinaBatchesNat 15 (a, b))).2 :=
    exactSteps_state_coprime 47 (semolinaBatchesNat 15 (a, b)) hafterOdd hafterCoprime
  have hfinishSecond : (exactSteps 47 (semolinaBatchesNat 15 (a, b))).2 = 1 := by
    simpa only [Nat.coprime_zero_left, hfinishFirst] using hfinishCoprime
  exact Prod.ext hfinishFirst hfinishSecond

end PastaAsm.Spec.Invert.Convergence
