/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.InversionDivergenceBoundary

/-!
# Near-length inputs to a Semolina approximation batch

When both positive inputs have bit length within 31 bits of their joint maximum,
the concrete 31-operation batch either terminates or removes 31 bits from the
joint absolute quotient length.  Comparisons made on an even first control are
irrelevant, so the first-divergence argument below records agreement only at
odd controls.  Before the first incorrect comparison the full-width quotients
therefore follow the exact binary-GCD recurrence.
-/

namespace PastaAsm
namespace InversionConvergence

open InversionSpec

/-- Agreement of every comparison that is actually consulted before `t`. -/
private def SemolinaComparisonRegularPrefix (a b t : Nat) : Prop :=
  ∀ i, i < t →
    ¬ Even (semolinaPrefixApprox a b i).1 →
      ((semolinaPrefixApprox a b i).2 ≤ (semolinaPrefixApprox a b i).1 ↔
        (semolinaPrefixReal a b i).2 ≤ (semolinaPrefixReal a b i).1)

/-- Exact iteration can equivalently append one exact operation on the right. -/
private theorem exactSteps_succ_right_near (t : Nat) (state : Nat × Nat) :
    exactSteps (t + 1) state =
      exactStep (exactSteps t state).1 (exactSteps t state).2 := by
  induction t generalizing state with
  | zero => rfl
  | succ t ih =>
      simpa only [exactSteps] using ih (exactStep state.1 state.2)

/-- Agreement on the comparisons which are actually used is enough to identify
an entire prefix with the natural exact recurrence. -/
private theorem semolinaPrefixReal_eq_exactSteps_of_comparisonRegularPrefix
    {a b t : Nat} (hb : Odd b) (ht : t ≤ 31)
    (hregular : SemolinaComparisonRegularPrefix a b t) :
    semolinaPrefixReal a b t =
      (((exactSteps t (a, b)).1 : Int), ((exactSteps t (a, b)).2 : Int)) := by
  induction t with
  | zero =>
      simp [semolinaPrefixReal, semolinaApprox, approxSteps, ApproxState.initial,
        identityMatrix, SignedRow.apply, exactSteps]
  | succ t ih =>
      have htlt : t < 31 := by omega
      have hprefix : SemolinaComparisonRegularPrefix a b t := by
        intro i hi
        exact hregular i (by omega)
      have heq := ih (by omega) hprefix
      have hparityInt :
          (semolinaPrefixReal a b t).1 % 2 =
            ((semolinaPrefixApprox a b t).1 : Int) % 2 := by
        simpa [semolinaPrefixReal, semolinaPrefixApprox] using
          (semolina_prefix_quotient_emod_two (a := a) (b := b) (t := t) hb htlt).1
      have hparity :
          (semolinaPrefixApprox a b t).1 % 2 =
            (exactSteps t (a, b)).1 % 2 := by
        rw [heq] at hparityInt
        change ((exactSteps t (a, b)).1 : Int) % 2 =
          ((semolinaPrefixApprox a b t).1 : Int) % 2 at hparityInt
        exact_mod_cast hparityInt.symm
      by_cases hodd : ¬ Even (semolinaPrefixApprox a b t).1
      · have horderControl := hregular t (Nat.lt_succ_self t) hodd
        have horder :
            (semolinaPrefixApprox a b t).2 ≤ (semolinaPrefixApprox a b t).1 ↔
              (exactSteps t (a, b)).2 ≤ (exactSteps t (a, b)).1 := by
          rw [heq] at horderControl
          constructor
          · intro h
            have hInt : ((exactSteps t (a, b)).2 : Int) ≤
                (exactSteps t (a, b)).1 := by
              simpa using horderControl.mp h
            exact_mod_cast hInt
          · intro h
            apply horderControl.mpr
            have hInt : ((exactSteps t (a, b)).2 : Int) ≤
                (exactSteps t (a, b)).1 := by exact_mod_cast h
            simpa using hInt
        rw [semolinaPrefixReal_succ hb htlt, heq,
          signedQuotientStep_eq_exactStep hparity horder,
          exactSteps_succ_right_near]
      · have heven : Even (semolinaPrefixApprox a b t).1 := not_not.mp hodd
        have hevenReal : Even (exactSteps t (a, b)).1 := by
          rw [Nat.even_iff, ← hparity]
          exact Nat.even_iff.mp heven
        rw [semolinaPrefixReal_succ hb htlt, heq, exactSteps_succ_right_near]
        unfold signedQuotientStep exactStep
        rw [if_pos heven, if_pos hevenReal]
        apply Prod.ext
        · rw [int_ediv_two_natCast]
        · rfl

/-- A comparison-regular prefix has the usual charged exact-prefix bound. -/
private theorem comparisonRegularPrefix_terminal_or_length_progress {a b t : Nat}
    (hb : Odd b) (ht : t ≤ 31)
    (hregular : SemolinaComparisonRegularPrefix a b t) :
    (semolinaPrefixReal a b t).1 = 0 ∨
      signedLengthSum (semolinaPrefixReal a b t).1
          (semolinaPrefixReal a b t).2 + t ≤ lengthSum a b := by
  rw [semolinaPrefixReal_eq_exactSteps_of_comparisonRegularPrefix hb ht hregular]
  simpa [signedLengthSum, lengthSum] using exactSteps_terminal_or_length_progress t hb

/-- If a finite prefix is not comparison-regular, it has a least bad index. -/
private theorem exists_first_incorrect_comparison {a b : Nat}
    (hbad : ¬ SemolinaComparisonRegularPrefix a b 31) :
    ∃ t, t < 31 ∧ SemolinaComparisonRegularPrefix a b t ∧
      ¬ Even (semolinaPrefixApprox a b t).1 ∧
      ¬ ((semolinaPrefixApprox a b t).2 ≤ (semolinaPrefixApprox a b t).1 ↔
        (semolinaPrefixReal a b t).2 ≤ (semolinaPrefixReal a b t).1) := by
  classical
  let Bad : Nat → Prop := fun i => i < 31 ∧
    ¬ Even (semolinaPrefixApprox a b i).1 ∧
    ¬ ((semolinaPrefixApprox a b i).2 ≤ (semolinaPrefixApprox a b i).1 ↔
      (semolinaPrefixReal a b i).2 ≤ (semolinaPrefixReal a b i).1)
  have hexists : ∃ i, Bad i := by
    by_contra hnone
    apply hbad
    intro i hi hodd
    by_contra horder
    exact hnone ⟨i, hi, hodd, horder⟩
  let t := Nat.find hexists
  have htBad : Bad t := Nat.find_spec hexists
  refine ⟨t, htBad.1, ?_, htBad.2.1, htBad.2.2⟩
  intro i hi hodd
  by_contra horder
  exact Nat.find_min hexists hi ⟨by omega, hodd, horder⟩

/-- The initial near-length hypotheses give the lower joint-length budget used
by the small (`Q`) endpoint. -/
private theorem near_initial_length_lower {a b n : Nat}
    (hn : max (bitLength a) (bitLength b) = n)
    (haNear : n - 32 < bitLength a) (hbNear : n - 32 < bitLength b) :
    2 * n - 31 ≤ lengthSum a b := by
  unfold lengthSum
  rcases max_choice (bitLength a) (bitLength b) with hmax | hmax
  · rw [hmax] at hn
    omega
  · rw [hmax] at hn
    omega

/-- The sum of the two natural states can shrink by at most a factor of two in
one exact binary-GCD operation. -/
private theorem exactStep_sum_reverse {a b : Nat} (hb : Odd b) :
    a + b ≤ 2 * ((exactStep a b).1 + (exactStep a b).2) := by
  unfold exactStep
  by_cases haEven : Even a
  · rw [if_pos haEven]
    have hhalf := two_mul_half_of_even haEven
    omega
  · rw [if_neg haEven]
    have haOdd := Nat.not_even_iff_odd.mp haEven
    by_cases hba : b ≤ a
    · rw [if_pos hba]
      have hdiff : Even (a - b) := by
        rcases haOdd with ⟨qa, hqa⟩
        rcases hb with ⟨qb, hqb⟩
        use qa - qb
        omega
      have hhalf := two_mul_half_of_even hdiff
      omega
    · rw [if_neg hba]
      have hab : a ≤ b := Nat.le_of_not_ge hba
      have hdiff : Even (b - a) := by
        rcases haOdd with ⟨qa, hqa⟩
        rcases hb with ⟨qb, hqb⟩
        use qb - qa
        omega
      have hhalf := two_mul_half_of_even hdiff
      omega

/-- Iterating the reverse sum estimate through an exact prefix. -/
private theorem exactSteps_sum_reverse (t : Nat) {a b : Nat} (hb : Odd b) :
    a + b ≤ 2^t *
      ((exactSteps t (a, b)).1 + (exactSteps t (a, b)).2) := by
  induction t generalizing a b with
  | zero => simp [exactSteps]
  | succ t ih =>
      have hone := exactStep_sum_reverse (a := a) hb
      have hodd := exactStep_second_odd_progress (a := a) hb
      have hrest := ih (a := (exactStep a b).1) (b := (exactStep a b).2) hodd
      rw [exactSteps]
      calc
        a + b ≤ 2 * ((exactStep a b).1 + (exactStep a b).2) := hone
        _ ≤ 2 * (2^t * ((exactSteps t (exactStep a b)).1 +
            (exactSteps t (exactStep a b)).2)) := Nat.mul_le_mul_left 2 hrest
        _ = 2^(t + 1) * ((exactSteps t (exactStep a b)).1 +
            (exactSteps t (exactStep a b)).2) := by rw [pow_succ]; ring

/-- A nonzero natural at least `2^e` has bit length at least `e+1`. -/
private theorem bitLength_ge_succ_of_pow_le {x e : Nat} (h : 2^e ≤ x) :
    e + 1 ≤ bitLength x := by
  have hlt : e < bitLength x := Nat.lt_size.mpr h
  omega

/-- A sum lower bound and difference upper bound give a sharp indexed lower
bound on both components. -/
private theorem min_ge_of_sum_and_diff {x y whole err lower : Nat}
    (hsum : whole ≤ x + y) (hdiff : ((x : Int) - (y : Int)).natAbs ≤ err)
    (hbudget : 2 * lower + err ≤ whole) : lower ≤ min x y := by
  have hxy : x ≤ y + err := by
    by_contra hnot
    have hlt : y + err < x := Nat.lt_of_not_ge hnot
    have hcast : (err : Int) < (x : Int) - (y : Int) := by omega
    have hnonneg : (0 : Int) ≤ (x : Int) - (y : Int) := by omega
    have habs : (((x : Int) - (y : Int)).natAbs : Int) = (x : Int) - (y : Int) :=
      Int.ofNat_natAbs_of_nonneg hnonneg
    have hle : (((x : Int) - (y : Int)).natAbs : Int) ≤ err := by exact_mod_cast hdiff
    omega
  have hyx : y ≤ x + err := by
    by_contra hnot
    have hlt : x + err < y := Nat.lt_of_not_ge hnot
    have hcast : (err : Int) < (y : Int) - (x : Int) := by omega
    have hnonpos : (x : Int) - (y : Int) ≤ 0 := by omega
    have habs : (((x : Int) - (y : Int)).natAbs : Int) = -((x : Int) - (y : Int)) :=
      Int.ofNat_natAbs_of_nonpos hnonpos
    have hle : (((x : Int) - (y : Int)).natAbs : Int) ≤ err := by exact_mod_cast hdiff
    omega
  rw [Nat.le_min]
  constructor <;> omega

/-- Strict absolute bounds survive exact division without the rounding slack
of a generic quotient estimate. -/
private theorem natAbs_ediv_lt_of_dvd {x : Int} {d bound : Nat}
    (hd : 0 < d) (hdiv : (d : Int) ∣ x) (h : x.natAbs < d * bound) :
    (x / (d : Int)).natAbs < bound := by
  rw [natAbs_ediv_of_dvd hd hdiv]
  exact (Nat.div_lt_iff_lt_mul hd).mpr (by simpa [Nat.mul_comm] using h)

/-- If one component is retained exactly, charging the replacement against the
smaller old component gives a joint signed-length decrease. -/
private theorem signedLengthSum_progress_of_retained_component
    {oldA oldB newA newB : Int} {drop : Nat}
    (hnew : bitLength newA.natAbs + drop ≤
      min (bitLength oldA.natAbs) (bitLength oldB.natAbs))
    (hretained : newB = oldA ∨ newB = oldB) :
    signedLengthSum newA newB + drop ≤ signedLengthSum oldA oldB := by
  have hnewA := hnew.trans (Nat.min_le_left _ _)
  have hnewB := hnew.trans (Nat.min_le_right _ _)
  rcases hretained with rfl | rfl <;> unfold signedLengthSum <;> omega

/-- At a wrong comparison between odd controls, a zero next approximate first
component rules out the negative endpoint of an even error interval.  In the
no-swap case, zero forces the controls equal, so attaining the endpoint would
make the odd real first component even.  In the swap case, distinct odd
controls cannot have zero half-difference. -/
private theorem first_wrong_boundary_impossible
    {realA realB : Int} {approxA approxB scale err : Nat}
    (hrealAmod : realA % 2 = 1) (hrealBmod : realB % 2 = 1)
    (happroxAOdd : Odd approxA) (happroxBOdd : Odd approxB)
    (hscaleEven : Even scale) (herrEven : Even err)
    (herrA : (realA - (scale : Int) * approxA).natAbs ≤ err)
    (herrB : (realB - (scale : Int) * approxB).natAbs ≤ err)
    (hwrong : (approxB ≤ approxA ∧ realA < realB) ∨
      (approxA < approxB ∧ realB ≤ realA))
    (hzero : (exactStep approxA approxB).1 = 0)
    (hboundary : (signedQuotientStep (approxA, approxB) (realA, realB)).1 =
      -(err : Int)) : False := by
  have happroxAEven : ¬ Even approxA := Nat.not_even_iff_odd.mpr happroxAOdd
  rcases hwrong with hnoswap | hswap
  · have happroxEq : approxA = approxB := by
      unfold exactStep at hzero
      rw [if_neg happroxAEven, if_pos hnoswap.1] at hzero
      rcases happroxAOdd with ⟨qa, hqa⟩
      rcases happroxBOdd with ⟨qb, hqb⟩
      omega
    have hrealDiff : realA - realB = -(2 * (err : Int)) := by
      unfold signedQuotientStep at hboundary
      rw [if_neg happroxAEven, if_pos hnoswap.1] at hboundary
      have hdvd : (2 : Int) ∣ realA - realB := by
        rw [Int.dvd_iff_emod_eq_zero]
        omega
      have hmul := Int.ediv_mul_cancel hdvd
      norm_num only at hboundary
      rw [hboundary] at hmul
      omega
    have hrealAEq : realA = (scale : Int) * approxA - err := by
      have hlowerA := (int_bounds_of_natAbs_le herrA).1
      have hupperA := (int_bounds_of_natAbs_le herrA).2
      have hlowerB := (int_bounds_of_natAbs_le herrB).1
      have hupperB := (int_bounds_of_natAbs_le herrB).2
      rw [← happroxEq] at hlowerB hupperB
      omega
    rcases hscaleEven with ⟨scaleHalf, hscaleHalf⟩
    rcases herrEven with ⟨errHalf, herrHalf⟩
    have hrealAFactor : realA = 2 * ((scaleHalf : Int) * approxA - errHalf) := by
      rw [hrealAEq]
      push_cast [hscaleHalf, herrHalf]
      ring
    rw [hrealAFactor] at hrealAmod
    omega
  · unfold exactStep at hzero
    rw [if_neg happroxAEven, if_neg (Nat.not_le_of_gt hswap.1)] at hzero
    rcases happroxAOdd with ⟨qa, hqa⟩
    rcases happroxBOdd with ⟨qb, hqb⟩
    omega

/-- Iterations append on the right for the coupled controlled trace. -/
private theorem controlledSteps_add (m n : Nat) (s : ControlledState) :
    controlledSteps (m + n) s = controlledSteps n (controlledSteps m s) := by
  induction m generalizing s with
  | zero => simp [controlledSteps]
  | succ m ih =>
      rw [Nat.succ_add, controlledSteps, ih]
      rfl

/-- The coupled scaled numerator at a prefix is exactly the quotient times its
current power-of-two denominator. -/
private theorem semolina_controlled_scaled_eq {a b t : Nat} (hb : Odd b) (ht : t ≤ 31) :
    let ap := semolinaApprox a b
    let c := controlledSteps t (ControlledState.initial ap.1 ap.2 a b)
    c.scaledRealA = (2^t : Int) * (semolinaPrefixReal a b t).1 ∧
      c.scaledRealB = (2^t : Int) * (semolinaPrefixReal a b t).2 := by
  let ap := semolinaApprox a b
  let c := controlledSteps t (ControlledState.initial ap.1 ap.2 a b)
  let s := approxSteps t (ApproxState.initial ap.1 ap.2)
  have hm := semolina_controlled_prefix a b t
  have hd := semolina_prefix_full_width_dvd (a := a) (b := b) (t := t) hb ht
  have hrowA : s.matrix.row0.apply a b =
      (2^t : Int) * (s.matrix.row0.apply a b / (2^t : Int)) := by
    rw [mul_comm]
    exact (Int.ediv_mul_cancel hd.1).symm
  have hrowB : s.matrix.row1.apply a b =
      (2^t : Int) * (s.matrix.row1.apply a b / (2^t : Int)) := by
    rw [mul_comm]
    exact (Int.ediv_mul_cancel hd.2).symm
  change c.scaledRealA = (2^t : Int) * (semolinaPrefixReal a b t).1 ∧
    c.scaledRealB = (2^t : Int) * (semolinaPrefixReal a b t).2
  simpa [c, s, ap, semolinaPrefixReal] using And.intro (hm.2.2.1.trans hrowA)
    (hm.2.2.2.trans hrowB)

/-- The propagated numerator error estimate, expressed directly on the coupled
controlled state at the same concrete prefix. -/
private theorem semolina_controlled_prefix_error {a b t : Nat} (hb : Odd b)
    (hlarge : 64 < max (bitLength a) (bitLength b)) :
    let n := max (bitLength a) (bitLength b)
    let ap := semolinaApprox a b
    let c := controlledSteps t (ControlledState.initial ap.1 ap.2 a b)
    (c.scaledRealA - (2^(n - 64 + t) : Nat) * c.approxA).natAbs ≤
        2^(n - 33 + t) ∧
      (c.scaledRealB - (2^(n - 64 + t) : Nat) * c.approxB).natAbs ≤
        2^(n - 33 + t) := by
  let n := max (bitLength a) (bitLength b)
  let ap := semolinaApprox a b
  let c := controlledSteps t (ControlledState.initial ap.1 ap.2 a b)
  let s := approxSteps t (ApproxState.initial ap.1 ap.2)
  have herr := semolina_prefix_error_of_odd (a := a) (b := b) (t := t) hb hlarge
  have hm := semolina_controlled_prefix a b t
  change
    (s.matrix.row0.apply a b - (2^(n - 64 + t) : Nat) * s.a).natAbs ≤
        2^(n - 33 + t) ∧
      (s.matrix.row1.apply a b - (2^(n - 64 + t) : Nat) * s.b).natAbs ≤
        2^(n - 33 + t) at herr
  change
    (c.scaledRealA - (2^(n - 64 + t) : Nat) * c.approxA).natAbs ≤
        2^(n - 33 + t) ∧
      (c.scaledRealB - (2^(n - 64 + t) : Nat) * c.approxB).natAbs ≤
        2^(n - 33 + t)
  rw [hm.1, hm.2.1, hm.2.2.1, hm.2.2.2]
  exact herr

/-- The second actual quotient is nonzero at every prefix through operation 31. -/
private theorem semolinaPrefixReal_second_ne_zero {a b t : Nat} (hb : Odd b)
    (ht : t ≤ 31) : (semolinaPrefixReal a b t).2 ≠ 0 := by
  by_cases ht0 : t = 0
  · subst t
    simpa [semolinaPrefixReal, semolinaApprox, approxSteps, ApproxState.initial,
      identityMatrix, SignedRow.apply] using (Nat.ne_of_gt (Odd.pos hb) : b ≠ 0)
  · obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht0
    have hu : u < 31 := by omega
    rw [show Nat.succ u = u + 1 by omega, semolinaPrefixReal_succ hb hu]
    have hparity := semolina_prefix_quotient_emod_two (a := a) (b := b) (t := u) hb hu
    let ap := semolinaApprox a b
    let s := approxSteps u (ApproxState.initial ap.1 ap.2)
    have hsOdd : Odd s.b := approxSteps_second_odd u _ (semolinaApprox_snd_odd hb)
    have hcontrolBOdd : Odd (semolinaPrefixApprox a b u).2 := by
      simpa [semolinaPrefixApprox, ap, s] using hsOdd
    have hrealBmod : (semolinaPrefixReal a b u).2 % 2 = 1 := by
      have hcmod : ((semolinaPrefixApprox a b u).2 : Int) % 2 = 1 := by
        exact_mod_cast (Nat.odd_iff.mp hcontrolBOdd)
      simpa [semolinaPrefixReal, semolinaPrefixApprox] using hparity.2.trans hcmod
    have hrealAmod_of_odd (hodd : ¬ Even (semolinaPrefixApprox a b u).1) :
        (semolinaPrefixReal a b u).1 % 2 = 1 := by
      have hcOdd := Nat.not_even_iff_odd.mp hodd
      have hcmod : ((semolinaPrefixApprox a b u).1 : Int) % 2 = 1 := by
        exact_mod_cast (Nat.odd_iff.mp hcOdd)
      simpa [semolinaPrefixReal, semolinaPrefixApprox] using hparity.1.trans hcmod
    unfold signedQuotientStep
    by_cases heven : Even (semolinaPrefixApprox a b u).1
    · rw [if_pos heven]
      intro hzero
      rw [hzero] at hrealBmod
      norm_num at hrealBmod
    · rw [if_neg heven]
      by_cases horder : (semolinaPrefixApprox a b u).2 ≤
          (semolinaPrefixApprox a b u).1
      · rw [if_pos horder]
        intro hzero
        rw [hzero] at hrealBmod
        norm_num at hrealBmod
      · rw [if_neg horder]
        intro hzero
        change (semolinaPrefixReal a b u).1 = 0 at hzero
        have hmod := hrealAmod_of_odd heven
        rw [hzero] at hmod
        norm_num at hmod

/-- At the least incorrect comparison, the real state is still a positive exact
state.  The selected subtraction makes the new first quotient nonpositive and
puts its magnitude in the single-error interval.  The new second quotient is
positive, and the corresponding scaled state enters the corrected `P ∨ Q`
region. -/
private theorem first_incorrect_comparison_data {a b t : Nat}
    (hb : Odd b) (hlarge : 64 < max (bitLength a) (bitLength b))
    (hregular : SemolinaComparisonRegularPrefix a b t)
    (ht : t < 31) (hodd : ¬ Even (semolinaPrefixApprox a b t).1)
    (hwrong : ¬ ((semolinaPrefixApprox a b t).2 ≤ (semolinaPrefixApprox a b t).1 ↔
      (semolinaPrefixReal a b t).2 ≤ (semolinaPrefixReal a b t).1)) :
    let n := max (bitLength a) (bitLength b)
    let next := semolinaPrefixReal a b (t + 1)
    let ap := semolinaApprox a b
    let after := controlledSteps (t + 1) (ControlledState.initial ap.1 ap.2 a b)
    (semolinaPrefixReal a b t).1 ≠ 0 ∧
      0 < (semolinaPrefixReal a b t).1 ∧ 0 < (semolinaPrefixReal a b t).2 ∧
      next.1 ≤ 0 ∧ next.1.natAbs ≤ 2^(n - 33) ∧ 0 < next.2 ∧
      ControlledDiverged (2^(n - 32 + t)) after := by
  let n := max (bitLength a) (bitLength b)
  let current := semolinaPrefixReal a b t
  let control := semolinaPrefixApprox a b t
  let next := semolinaPrefixReal a b (t + 1)
  let ap := semolinaApprox a b
  let before := controlledSteps t (ControlledState.initial ap.1 ap.2 a b)
  let after := controlledSteps (t + 1) (ControlledState.initial ap.1 ap.2 a b)
  have hcurrentEq := semolinaPrefixReal_eq_exactSteps_of_comparisonRegularPrefix hb ht.le hregular
  have hcurrentNonneg : 0 ≤ current.1 ∧ 0 ≤ current.2 := by
    dsimp [current]
    rw [hcurrentEq]
    exact ⟨by positivity, by positivity⟩
  have hcurrentBNe : current.2 ≠ 0 := semolinaPrefixReal_second_ne_zero hb ht.le
  have hcurrentBPos : 0 < current.2 := lt_of_le_of_ne hcurrentNonneg.2 (Ne.symm hcurrentBNe)
  have hparity := semolina_prefix_quotient_emod_two (a := a) (b := b) (t := t) hb ht
  have hcontrolAOdd := Nat.not_even_iff_odd.mp hodd
  have hcontrolAmod : ((control.1 : Nat) : Int) % 2 = 1 := by
    exact_mod_cast (Nat.odd_iff.mp hcontrolAOdd)
  have hcurrentAmod : current.1 % 2 = 1 := by
    simpa [current, control, semolinaPrefixReal, semolinaPrefixApprox] using
      hparity.1.trans hcontrolAmod
  have hcurrentANe : current.1 ≠ 0 := by
    intro hz
    rw [hz] at hcurrentAmod
    norm_num at hcurrentAmod
  have hcurrentAPos : 0 < current.1 := lt_of_le_of_ne hcurrentNonneg.1 (Ne.symm hcurrentANe)
  have herrQ := semolina_prefix_quotient_error_of_odd (a := a) (b := b) (t := t)
    hb hlarge ht.le
  change
    (current.1 - (2^(n - 64) : Nat) * control.1).natAbs ≤ 2^(n - 33) ∧
      (current.2 - (2^(n - 64) : Nat) * control.2).natAbs ≤ 2^(n - 33) at herrQ
  have hscaled := semolina_controlled_scaled_eq (a := a) (b := b) (t := t) hb ht.le
  have hbeforeApprox := semolina_controlled_prefix a b t
  have hbeforeControlA : before.approxA = control.1 := by
    exact hbeforeApprox.1
  have hbeforeControlB : before.approxB = control.2 := by
    exact hbeforeApprox.2.1
  have hbeforeRealA : before.scaledRealA = (2^t : Int) * current.1 := hscaled.1
  have hbeforeRealB : before.scaledRealB = (2^t : Int) * current.2 := hscaled.2
  have herrNum := semolina_controlled_prefix_error (a := a) (b := b) (t := t) hb hlarge
  change
    (before.scaledRealA - (2^(n - 64 + t) : Nat) * before.approxA).natAbs ≤
        2^(n - 33 + t) ∧
      (before.scaledRealB - (2^(n - 64 + t) : Nat) * before.approxB).natAbs ≤
        2^(n - 33 + t) at herrNum
  have hafterStep : after = controlledStep before := by
    change controlledSteps (t + 1) (ControlledState.initial ap.1 ap.2 a b) = _
    rw [controlledSteps_add t 1]
    rfl
  have hnextStep : next = signedQuotientStep control current := by
    dsimp [next, control, current]
    rw [semolinaPrefixReal_succ hb ht]
  have hwrongCases :
      (control.2 ≤ control.1 ∧ current.1 < current.2) ∨
        (control.1 < control.2 ∧ current.2 ≤ current.1) := by
    by_cases hcontrol : control.2 ≤ control.1
    · left
      refine ⟨hcontrol, ?_⟩
      by_contra hnot
      have hreal : current.2 ≤ current.1 := le_of_not_gt hnot
      exact hwrong ⟨fun _ => hreal, fun _ => hcontrol⟩
    · right
      have hcontrol' : control.1 < control.2 := Nat.lt_of_not_ge hcontrol
      refine ⟨hcontrol', ?_⟩
      by_contra hnot
      have hreal : current.1 < current.2 := lt_of_not_ge hnot
      exact hwrong ⟨fun hc => (hcontrol hc).elim, fun hr => (not_lt_of_ge hr hreal).elim⟩
  rcases hwrongCases with hnoswap | hswap
  · have hnextEq : next = ((current.1 - current.2) / 2, current.2) := by
      rw [hnextStep]
      unfold signedQuotientStep
      rw [if_neg hodd, if_pos hnoswap.1]
    have hnextNonpos : next.1 ≤ 0 := by rw [hnextEq]; omega
    have hnextAbs : next.1.natAbs ≤ 2^(n - 33) := by
      have hdiff := opposite_order_difference_le herrQ.1 herrQ.2 hnoswap.1 hnoswap.2
      rw [hnextEq]
      change ((current.1 - current.2) / 2).natAbs ≤ 2^(n - 33)
      have hdvd : (2 : Int) ∣ current.1 - current.2 := by
        have hAodd : current.1 % 2 = 1 := hcurrentAmod
        have hBmodInt := hparity.2
        have hcontrolBOdd : Odd control.2 := by
          let s := approxSteps t (ApproxState.initial ap.1 ap.2)
          have hsOdd : Odd s.b := approxSteps_second_odd t _ (semolinaApprox_snd_odd hb)
          simpa [control, semolinaPrefixApprox, ap, s] using hsOdd
        have hcontrolBmod : ((control.2 : Nat) : Int) % 2 = 1 := by
          exact_mod_cast (Nat.odd_iff.mp hcontrolBOdd)
        have hBodd : current.2 % 2 = 1 := by
          simpa [current, control, semolinaPrefixReal, semolinaPrefixApprox] using
            hBmodInt.trans hcontrolBmod
        rw [Int.dvd_iff_emod_eq_zero]
        omega
      have habsDiv : ((current.1 - current.2) / 2).natAbs =
          (current.1 - current.2).natAbs / 2 := by
        simpa using natAbs_ediv_of_dvd (x := current.1 - current.2) (d := 2) (by omega) hdvd
      rw [habsDiv]
      have hdiv : (current.1 - current.2).natAbs / 2 ≤
          (2 * 2^(n - 33)) / 2 := Nat.div_le_div_right hdiff
      simpa [Nat.mul_comm] using hdiv
    have hinv : ControlledDiverged (2^(n - 32 + t)) after := by
      rw [hafterStep]
      have hentry := controlledStep_firstDivergence_noswap
        (s := before) (scale := 2^(n - 64 + t)) (err := 2^(n - 33 + t))
        (by positivity)
        (by simpa [hbeforeControlA] using hodd)
        (by simpa [hbeforeControlA, hbeforeControlB] using hnoswap.1)
        (by rw [hbeforeRealB]; positivity)
        (by
          rw [hbeforeRealA, hbeforeRealB]
          exact mul_lt_mul_of_pos_left hnoswap.2 (by positivity))
        herrNum.1 herrNum.2
      have herrEq : 2 * 2^(n - 33 + t) = 2^(n - 32 + t) := by
        rw [Nat.mul_comm, ← pow_succ]
        congr 1
        omega
      simpa [herrEq] using hentry
    have hnextBPos : 0 < next.2 := by rw [hnextEq]; exact hcurrentBPos
    simpa [n, current, next, after] using
      (show current.1 ≠ 0 ∧ 0 < current.1 ∧ 0 < current.2 ∧ next.1 ≤ 0 ∧
          next.1.natAbs ≤ 2^(n - 33) ∧ 0 < next.2 ∧
          ControlledDiverged (2^(n - 32 + t)) after from
        ⟨hcurrentANe, hcurrentAPos, hcurrentBPos, hnextNonpos,
          hnextAbs, hnextBPos, hinv⟩)
  · have hnextEq : next = ((current.2 - current.1) / 2, current.1) := by
      rw [hnextStep]
      unfold signedQuotientStep
      rw [if_neg hodd, if_neg (Nat.not_le_of_gt hswap.1)]
    have hnextNonpos : next.1 ≤ 0 := by rw [hnextEq]; omega
    have hnextAbs : next.1.natAbs ≤ 2^(n - 33) := by
      have hdiff := opposite_order_difference_le' herrQ.1 herrQ.2 hswap.1 hswap.2
      rw [hnextEq]
      change ((current.2 - current.1) / 2).natAbs ≤ 2^(n - 33)
      have hdvd : (2 : Int) ∣ current.2 - current.1 := by
        have hBmodInt := hparity.2
        let s := approxSteps t (ApproxState.initial ap.1 ap.2)
        have hsOdd : Odd s.b := approxSteps_second_odd t _ (semolinaApprox_snd_odd hb)
        have hcontrolBOdd : Odd control.2 := by
          simpa [control, semolinaPrefixApprox, ap, s] using hsOdd
        have hcontrolBmod : ((control.2 : Nat) : Int) % 2 = 1 := by
          exact_mod_cast (Nat.odd_iff.mp hcontrolBOdd)
        have hBodd : current.2 % 2 = 1 := by
          simpa [current, control, semolinaPrefixReal, semolinaPrefixApprox] using
            hBmodInt.trans hcontrolBmod
        rw [Int.dvd_iff_emod_eq_zero]
        omega
      have habsDiv : ((current.2 - current.1) / 2).natAbs =
          (current.2 - current.1).natAbs / 2 := by
        simpa using natAbs_ediv_of_dvd (x := current.2 - current.1) (d := 2) (by omega) hdvd
      rw [habsDiv]
      have hdiv : (current.2 - current.1).natAbs / 2 ≤
          (2 * 2^(n - 33)) / 2 := Nat.div_le_div_right hdiff
      simpa [Nat.mul_comm] using hdiv
    have hinv : ControlledDiverged (2^(n - 32 + t)) after := by
      rw [hafterStep]
      have hentry := controlledStep_firstDivergence_swap
        (s := before) (scale := 2^(n - 64 + t)) (err := 2^(n - 33 + t))
        (by positivity)
        (by simpa [hbeforeControlA] using hodd)
        (by simpa [hbeforeControlA, hbeforeControlB] using hswap.1)
        (by rw [hbeforeRealA]; positivity)
        (by
          rw [hbeforeRealA, hbeforeRealB]
          exact mul_le_mul_of_nonneg_left hswap.2 (by positivity))
        herrNum.1 herrNum.2
      have herrEq : 2 * 2^(n - 33 + t) = 2^(n - 32 + t) := by
        rw [Nat.mul_comm, ← pow_succ]
        congr 1
        omega
      simpa [herrEq] using hentry
    have hnextBPos : 0 < next.2 := by rw [hnextEq]; exact hcurrentAPos
    simpa [n, current, next, after] using
      (show current.1 ≠ 0 ∧ 0 < current.1 ∧ 0 < current.2 ∧ next.1 ≤ 0 ∧
          next.1.natAbs ≤ 2^(n - 33) ∧ 0 < next.2 ∧
          ControlledDiverged (2^(n - 32 + t)) after from
        ⟨hcurrentANe, hcurrentAPos, hcurrentBPos, hnextNonpos,
          hnextAbs, hnextBPos, hinv⟩)

/-- Concrete near-length convergence for one 31-operation Semolina batch.
Both positive inputs occupy the top 32-bit window.  The actual approximation-
controlled batch either terminates or removes all 31 scheduled bits from the
joint absolute quotient length. -/
theorem semolinaNear_terminal_or_length_progress {a b : Nat}
    (ha : 0 < a) (hbPos : 0 < b) (hb : Odd b)
    (hlarge : 64 < max (bitLength a) (bitLength b))
    (haNear : max (bitLength a) (bitLength b) - 32 < bitLength a)
    (hbNear : max (bitLength a) (bitLength b) - 32 < bitLength b) :
    (semolinaQuotients a b).1 = 0 ∨
      signedLengthSum (semolinaQuotients a b).1 (semolinaQuotients a b).2 + 31 ≤
        lengthSum a b := by
  let n := max (bitLength a) (bitLength b)
  by_cases hregular : SemolinaComparisonRegularPrefix a b 31
  · have hprogress := comparisonRegularPrefix_terminal_or_length_progress hb (by omega) hregular
    simpa [semolinaPrefixReal, semolinaQuotients, semolinaNumerators, semolinaShort] using hprogress
  · obtain ⟨t, ht, hprefix, hodd, hwrong⟩ := exists_first_incorrect_comparison hregular
    let current := semolinaPrefixReal a b t
    let next := semolinaPrefixReal a b (t + 1)
    let ap := semolinaApprox a b
    let initial := ControlledState.initial ap.1 ap.2 a b
    let after := controlledSteps (t + 1) initial
    let r := 31 - (t + 1)
    let finish := controlledSteps r after
    have hdata := first_incorrect_comparison_data hb hlarge hprefix ht hodd hwrong
    change current.1 ≠ 0 ∧ 0 < current.1 ∧ 0 < current.2 ∧ next.1 ≤ 0 ∧
      next.1.natAbs ≤ 2^(n - 33) ∧ 0 < next.2 ∧
      ControlledDiverged (2^(n - 32 + t)) after at hdata
    have hprefixCharge := comparisonRegularPrefix_terminal_or_length_progress hb ht.le hprefix
    have hcharged : signedLengthSum current.1 current.2 + t ≤ lengthSum a b := by
      rcases hprefixCharge with hzero | hlen
      · exact (hdata.1 hzero).elim
      · exact hlen
    have hsumReverse := exactSteps_sum_reverse t (a := a) hb
    have hcurrentEq := semolinaPrefixReal_eq_exactSteps_of_comparisonRegularPrefix hb ht.le hprefix
    have hsumCurrent : a + b ≤ 2^t * (current.1.natAbs + current.2.natAbs) := by
      dsimp [current]
      rw [hcurrentEq]
      simpa using hsumReverse
    have hinputPow : 2^(n - 1) ≤ a + b := by
      rcases max_choice (bitLength a) (bitLength b) with hmax | hmax
      · have hnEq : n = bitLength a := by exact hmax
        rw [hnEq]
        exact (two_pow_pred_bitLength_le ha).trans (Nat.le_add_right _ _)
      · have hnEq : n = bitLength b := by exact hmax
        rw [hnEq]
        exact (two_pow_pred_bitLength_le hbPos).trans (Nat.le_add_left _ _)
    have hcurrentSumPow : 2^(n - 1 - t) ≤ current.1.natAbs + current.2.natAbs := by
      by_contra hnot
      have hlt : current.1.natAbs + current.2.natAbs < 2^(n - 1 - t) := Nat.lt_of_not_ge hnot
      have hpowExp : t + (n - 1 - t) = n - 1 := by omega
      have hltScaled : 2^t * (current.1.natAbs + current.2.natAbs) < 2^(n - 1) := by
        calc
          2^t * (current.1.natAbs + current.2.natAbs) < 2^t * 2^(n - 1 - t) :=
            Nat.mul_lt_mul_of_pos_left hlt (by positivity)
          _ = 2^(n - 1) := by rw [← pow_add, hpowExp]
      omega
    have hcurrentMaxPow : 2^(n - 2 - t) ≤ max current.1.natAbs current.2.natAbs := by
      have hsumMax : current.1.natAbs + current.2.natAbs ≤
          2 * max current.1.natAbs current.2.natAbs := by
        omega
      by_contra hnot
      have hmaxLt : max current.1.natAbs current.2.natAbs < 2^(n - 2 - t) :=
        Nat.lt_of_not_ge hnot
      have hexp : n - 1 - t = (n - 2 - t) + 1 := by omega
      rw [hexp, pow_succ] at hcurrentSumPow
      omega
    have hcurrentMaxSize : n - 1 - t ≤
        max (bitLength current.1.natAbs) (bitLength current.2.natAbs) := by
      have hexp : n - 1 - t = (n - 2 - t) + 1 := by omega
      rcases max_choice current.1.natAbs current.2.natAbs with hmax | hmax
      · rw [hmax] at hcurrentMaxPow
        have hsize := bitLength_ge_succ_of_pow_le hcurrentMaxPow
        rw [hexp]
        exact hsize.trans (Nat.le_max_left _ _)
      · rw [hmax] at hcurrentMaxPow
        have hsize := bitLength_ge_succ_of_pow_le hcurrentMaxPow
        rw [hexp]
        exact hsize.trans (Nat.le_max_right _ _)
    have hcurrentDiff : (current.1 - current.2).natAbs ≤ 2^(n - 32) := by
      have herr := semolina_prefix_quotient_error_of_odd (a := a) (b := b) (t := t)
        hb hlarge ht.le
      change
        (current.1 - (2^(n - 64) : Nat) * (semolinaPrefixApprox a b t).1).natAbs ≤
            2^(n - 33) ∧
          (current.2 - (2^(n - 64) : Nat) * (semolinaPrefixApprox a b t).2).natAbs ≤
            2^(n - 33) at herr
      have hcases :
          ((semolinaPrefixApprox a b t).2 ≤ (semolinaPrefixApprox a b t).1 ∧
            current.1 < current.2) ∨
          ((semolinaPrefixApprox a b t).1 < (semolinaPrefixApprox a b t).2 ∧
            current.2 ≤ current.1) := by
        by_cases hcontrol : (semolinaPrefixApprox a b t).2 ≤
            (semolinaPrefixApprox a b t).1
        · left
          refine ⟨hcontrol, ?_⟩
          by_contra hnot
          have hreal : current.2 ≤ current.1 := le_of_not_gt hnot
          exact hwrong ⟨fun _ => hreal, fun _ => hcontrol⟩
        · right
          have hcontrol' : (semolinaPrefixApprox a b t).1 <
              (semolinaPrefixApprox a b t).2 := Nat.lt_of_not_ge hcontrol
          refine ⟨hcontrol', ?_⟩
          by_contra hnot
          have hreal : current.1 < current.2 := lt_of_not_ge hnot
          exact hwrong ⟨fun hc => (hcontrol hc).elim,
            fun hr => (not_lt_of_ge hr hreal).elim⟩
      have herrEq : 2 * 2^(n - 33) = 2^(n - 32) := by
        rw [Nat.mul_comm, ← pow_succ]
        congr 1
        omega
      rcases hcases with hcase | hcase
      · simpa [herrEq] using opposite_order_difference_le herr.1 herr.2 hcase.1 hcase.2
      · have hdiff := opposite_order_difference_le' herr.1 herr.2 hcase.1 hcase.2
        rw [← Int.natAbs_neg, neg_sub] at hdiff
        simpa [herrEq] using hdiff
    have hcurrentMinPow : 2^(n - 3 - t) ≤ min current.1.natAbs current.2.natAbs := by
      apply min_ge_of_sum_and_diff
        (x := current.1.natAbs) (y := current.2.natAbs)
        (whole := 2^(n - 1 - t)) (err := 2^(n - 32))
        (lower := 2^(n - 3 - t)) hcurrentSumPow
      · have hnonnegA : 0 ≤ current.1 := hdata.2.1.le
        have hnonnegB : 0 ≤ current.2 := hdata.2.2.1.le
        rw [Int.natAbs_of_nonneg hnonnegA, Int.natAbs_of_nonneg hnonnegB]
        exact hcurrentDiff
      · have hlower : 2 * 2^(n - 3 - t) = 2^(n - 2 - t) := by
          rw [Nat.mul_comm, ← pow_succ]
          congr 1
          omega
        have herrLe : 2^(n - 32) ≤ 2^(n - 2 - t) := by
          exact Nat.pow_le_pow_right (by omega) (by omega)
        have hwhole : 2 * 2^(n - 2 - t) = 2^(n - 1 - t) := by
          rw [Nat.mul_comm, ← pow_succ]
          congr 1
          omega
        rw [hlower, ← hwhole]
        omega
    have hcurrentMinSize : n - 2 - t ≤
        min (bitLength current.1.natAbs) (bitLength current.2.natAbs) := by
      have hA : 2^(n - 3 - t) ≤ current.1.natAbs :=
        hcurrentMinPow.trans (Nat.min_le_left _ _)
      have hB : 2^(n - 3 - t) ≤ current.2.natAbs :=
        hcurrentMinPow.trans (Nat.min_le_right _ _)
      have hexp : n - 2 - t = (n - 3 - t) + 1 := by omega
      rw [Nat.le_min, hexp]
      exact ⟨bitLength_ge_succ_of_pow_le hA, bitLength_ge_succ_of_pow_le hB⟩
    have hafterMatches := semolina_controlled_scaled_eq (a := a) (b := b) (t := t + 1) hb
      (by omega)
    have hafterRealA : after.scaledRealA = (2^(t + 1) : Int) * next.1 := hafterMatches.1
    have hafterRealB : after.scaledRealB = (2^(t + 1) : Int) * next.2 := hafterMatches.2
    have hclose : ∀ u, u < r →
        let st := controlledSteps u after
        (st.scaledRealA - (((2^(n - 64 + t + 1)) * 2^u : Nat) : Int) * st.approxA).natAbs ≤
            2^u * 2^(n - 32 + t) ∧
        (st.scaledRealB - (((2^(n - 64 + t + 1)) * 2^u : Nat) : Int) * st.approxB).natAbs ≤
            2^u * 2^(n - 32 + t) := by
      intro u hu
      let st := controlledSteps u after
      have htotal : t + 1 + u ≤ 31 := by dsimp [r] at hu; omega
      have hsplit : controlledSteps u after = controlledSteps (t + 1 + u) initial := by
        dsimp [after]
        rw [← controlledSteps_add]
      have herr := semolina_controlled_prefix_error (a := a) (b := b)
        (t := t + 1 + u) hb hlarge
      change
        ((controlledSteps (t + 1 + u) initial).scaledRealA -
          (2^(n - 64 + (t + 1 + u)) : Nat) *
            (controlledSteps (t + 1 + u) initial).approxA).natAbs ≤
              2^(n - 33 + (t + 1 + u)) ∧
        ((controlledSteps (t + 1 + u) initial).scaledRealB -
          (2^(n - 64 + (t + 1 + u)) : Nat) *
            (controlledSteps (t + 1 + u) initial).approxB).natAbs ≤
              2^(n - 33 + (t + 1 + u)) at herr
      rw [hsplit]
      have hscaleExp : n - 64 + (t + 1 + u) = (n - 64 + t + 1) + u := by omega
      have herrExp : n - 33 + (t + 1 + u) = u + (n - 32 + t) := by omega
      simpa [hscaleExp, herrExp, pow_add, Nat.mul_assoc, Nat.mul_left_comm,
        Nat.mul_comm] using herr
    have hfinishResult := controlledSteps_small_or_signedLengthSum_le
      (s := after) (scale := 2^(n - 64 + t + 1)) (err := 2^(n - 32 + t))
      (bound := signedLengthSum after.scaledRealA after.scaledRealB) r
      (by positivity) hclose hdata.2.2.2.2.2.2 (le_rfl)
    have hfinishEq : finish = controlledSteps 31 initial := by
      dsimp [finish, r, after]
      rw [← controlledSteps_add]
      congr 1
      omega
    have hfinalMatches := semolina_controlled_prefix a b 31
    have hfinalNumsA : finish.scaledRealA = (semolinaNumerators a b).1 := by
      rw [hfinishEq]
      simpa [initial, ap, semolinaNumerators, semolinaShort] using hfinalMatches.2.2.1
    have hfinalNumsB : finish.scaledRealB = (semolinaNumerators a b).2 := by
      rw [hfinishEq]
      simpa [initial, ap, semolinaNumerators, semolinaShort] using hfinalMatches.2.2.2
    have hdiv := semolinaShort_full_width_dvd a b hb
    have hquotA : (semolinaQuotients a b).1 = finish.scaledRealA / (2^31 : Int) := by
      simp only [semolinaQuotients]
      rw [hfinalNumsA]
    have hquotB : (semolinaQuotients a b).2 = finish.scaledRealB / (2^31 : Int) := by
      simp only [semolinaQuotients]
      rw [hfinalNumsB]
    have hfinishDivA : (2^31 : Int) ∣ finish.scaledRealA := by
      rw [hfinalNumsA]
      exact hdiv.1
    have hfinishDivB : (2^31 : Int) ∣ finish.scaledRealB := by
      rw [hfinalNumsB]
      exact hdiv.2
    rcases hfinishResult with hsmall | hlen
    · right
      have herrExp : r + (n - 32 + t) = n - 2 := by
        dsimp [r]
        omega
      have herrFinal : 2^r * 2^(n - 32 + t) = 2^(n - 2) := by
        rw [← pow_add, herrExp]
      rw [herrFinal] at hsmall
      have hleftExp : 2 + (n - 2) = n := by omega
      have hrightExp : 31 + (n - 31) = n := by omega
      have hfactor : 4 * 2^(n - 2) = 2^31 * 2^(n - 31) := by
        rw [show 4 = 2^2 by norm_num, ← pow_add, ← pow_add, hleftExp, hrightExp]
      have hboundA : (semolinaQuotients a b).1.natAbs < 2^(n - 31) := by
        rw [hquotA]
        apply natAbs_ediv_lt_of_dvd (by positivity) hfinishDivA
        simpa [hfactor] using hsmall.1
      have hboundB : (semolinaQuotients a b).2.natAbs < 2^(n - 31) := by
        rw [hquotB]
        apply natAbs_ediv_lt_of_dvd (by positivity) hfinishDivB
        simpa [hfactor] using hsmall.2
      have hsizeA := bitLength_natAbs_le_of_lt_two_pow hboundA
      have hsizeB := bitLength_natAbs_le_of_lt_two_pow hboundB
      have hinitialLower := near_initial_length_lower (a := a) (b := b) (n := n)
        rfl haNear hbNear
      unfold signedLengthSum
      omega
    · change signedLengthSum finish.scaledRealA finish.scaledRealB ≤
          signedLengthSum after.scaledRealA after.scaledRealB + 2 * r at hlen
      have hquotProgress :
          (semolinaQuotients a b).1 = 0 ∨ (semolinaQuotients a b).2 = 0 ∨
            signedLengthSum (semolinaQuotients a b).1 (semolinaQuotients a b).2 + 62 =
              signedLengthSum finish.scaledRealA finish.scaledRealB := by
        simpa [hquotA, hquotB] using
          signedLengthSum_ediv_pow_terminal_or_eq hfinishDivA hfinishDivB
      rcases hquotProgress with hzeroA | hzeroB | hlenDiv
      · exact Or.inl hzeroA
      · right
        have hqBNe : (semolinaQuotients a b).2 ≠ 0 := by
          simpa [semolinaPrefixReal, semolinaQuotients, semolinaNumerators, semolinaShort] using
            (semolinaPrefixReal_second_ne_zero (a := a) (b := b) (t := 31) hb
              (show 31 ≤ 31 by omega))
        exact (hqBNe hzeroB).elim
      · right
        have hafterSize : signedLengthSum after.scaledRealA after.scaledRealB ≤
            signedLengthSum next.1 next.2 + 2 * (t + 1) := by
          have hnextBNe : next.2 ≠ 0 := ne_of_gt hdata.2.2.2.2.2.1
          have hafterQuotB : after.scaledRealB / (2^(t + 1) : Int) = next.2 := by
            rw [hafterRealB]
            exact Int.mul_ediv_cancel_left _ (by positivity)
          have hsizeB := bitLength_natAbs_ediv_pow_add_eq
            (x := after.scaledRealB) (bits := t + 1)
            (by rw [hafterRealB]; exact dvd_mul_right _ _)
            (by simpa [hafterQuotB] using hnextBNe)
          rw [hafterQuotB] at hsizeB
          by_cases hnextA : next.1 = 0
          · have hafterAZero : after.scaledRealA = 0 := by simp [hafterRealA, hnextA]
            unfold signedLengthSum
            rw [hafterAZero, hnextA]
            simp only [Int.natAbs_zero, bitLength_zero, zero_add]
            omega
          · have hafterQuotA : after.scaledRealA / (2^(t + 1) : Int) = next.1 := by
              rw [hafterRealA]
              exact Int.mul_ediv_cancel_left _ (by positivity)
            have hsizeA := bitLength_natAbs_ediv_pow_add_eq
                (x := after.scaledRealA) (bits := t + 1)
                (by rw [hafterRealA]; exact dvd_mul_right _ _)
                (by simpa [hafterQuotA] using hnextA)
            rw [hafterQuotA] at hsizeA
            unfold signedLengthSum
            omega
        have hnextAUpper : bitLength next.1.natAbs ≤ n - 32 := by
          have hbound := bitLength_le_succ_of_le_two_pow hdata.2.2.2.2.1
          have hn : 33 ≤ n := by dsimp [n]; omega
          omega
        have hwrongCases :
            ((semolinaPrefixApprox a b t).2 ≤ (semolinaPrefixApprox a b t).1 ∧
              current.1 < current.2) ∨
            ((semolinaPrefixApprox a b t).1 < (semolinaPrefixApprox a b t).2 ∧
              current.2 ≤ current.1) := by
          by_cases hcontrol :
              (semolinaPrefixApprox a b t).2 ≤ (semolinaPrefixApprox a b t).1
          · left
            refine ⟨hcontrol, ?_⟩
            by_contra hnot
            have hreal : current.2 ≤ current.1 := le_of_not_gt hnot
            exact hwrong ⟨fun _ => hreal, fun _ => hcontrol⟩
          · right
            have hcontrol' :
                (semolinaPrefixApprox a b t).1 < (semolinaPrefixApprox a b t).2 :=
              Nat.lt_of_not_ge hcontrol
            refine ⟨hcontrol', ?_⟩
            by_contra hnot
            have hreal : current.1 < current.2 := lt_of_not_ge hnot
            exact hwrong ⟨fun hc => (hcontrol hc).elim,
              fun hr => (not_lt_of_ge hr hreal).elim⟩
        have hnextStep : next = signedQuotientStep (semolinaPrefixApprox a b t) current := by
          dsimp [next, current]
          rw [semolinaPrefixReal_succ hb ht]
        have hnextBRetained : next.2 = current.1 ∨ next.2 = current.2 := by
          rcases hwrongCases with h | h
          · rw [hnextStep]
            unfold signedQuotientStep
            rw [if_neg hodd, if_pos h.1]
            exact Or.inr rfl
          · rw [hnextStep]
            unfold signedQuotientStep
            rw [if_neg hodd, if_neg (Nat.not_le_of_gt h.1)]
            exact Or.inl rfl
        have hnotBoundary : next.1 ≠ -(2^(n - 33) : Nat) := by
          intro hboundary
          have hzeroPrefix : (semolinaPrefixApprox a b (t + 1)).1 = 0 := by
            apply semolina_prefix_boundary_zero hb hlarge (by omega)
            simpa [next, n] using hboundary
          have hcontrolStep : semolinaPrefixApprox a b (t + 1) =
              exactStep (semolinaPrefixApprox a b t).1
                (semolinaPrefixApprox a b t).2 := by
            let ap := semolinaApprox a b
            let s := approxSteps t (ApproxState.initial ap.1 ap.2)
            change ((approxSteps (t + 1) (ApproxState.initial ap.1 ap.2)).a,
              (approxSteps (t + 1) (ApproxState.initial ap.1 ap.2)).b) =
                exactStep s.a s.b
            rw [show t + 1 = Nat.succ t by omega, approxSteps_succ_right_progress]
            unfold approxStep exactStep
            split_ifs <;> rfl
          have hzeroStep :
              (exactStep (semolinaPrefixApprox a b t).1
                (semolinaPrefixApprox a b t).2).1 = 0 := by
            rw [← hcontrolStep]
            exact hzeroPrefix
          have hcontrolAOdd : Odd (semolinaPrefixApprox a b t).1 :=
            Nat.not_even_iff_odd.mp hodd
          have hcontrolBOdd : Odd (semolinaPrefixApprox a b t).2 := by
            let s := approxSteps t
              (ApproxState.initial (semolinaApprox a b).1 (semolinaApprox a b).2)
            have hsOdd : Odd s.b := approxSteps_second_odd t _ (semolinaApprox_snd_odd hb)
            simpa [semolinaPrefixApprox, s] using hsOdd
          have hparity := semolina_prefix_quotient_emod_two
            (a := a) (b := b) (t := t) hb ht
          have hcontrolAmod : (((semolinaPrefixApprox a b t).1 : Nat) : Int) % 2 = 1 := by
            exact_mod_cast (Nat.odd_iff.mp hcontrolAOdd)
          have hcontrolBmod : (((semolinaPrefixApprox a b t).2 : Nat) : Int) % 2 = 1 := by
            exact_mod_cast (Nat.odd_iff.mp hcontrolBOdd)
          have hrealAmod : current.1 % 2 = 1 := by
            simpa [current, semolinaPrefixReal, semolinaPrefixApprox] using
              hparity.1.trans hcontrolAmod
          have hrealBmod : current.2 % 2 = 1 := by
            simpa [current, semolinaPrefixReal, semolinaPrefixApprox] using
              hparity.2.trans hcontrolBmod
          have herr := semolina_prefix_quotient_error_of_odd
            (a := a) (b := b) (t := t) hb hlarge ht.le
          change
            (current.1 - (2^(n - 64) : Nat) * (semolinaPrefixApprox a b t).1).natAbs ≤
                2^(n - 33) ∧
              (current.2 - (2^(n - 64) : Nat) * (semolinaPrefixApprox a b t).2).natAbs ≤
                2^(n - 33) at herr
          have hscaleEven : Even (2^(n - 64)) := by
            rw [even_iff_two_dvd]
            exact pow_dvd_pow 2 (show 1 ≤ n - 64 by omega)
          have herrEven : Even (2^(n - 33)) := by
            rw [even_iff_two_dvd]
            exact pow_dvd_pow 2 (show 1 ≤ n - 33 by omega)
          apply first_wrong_boundary_impossible hrealAmod hrealBmod hcontrolAOdd hcontrolBOdd
            hscaleEven herrEven herr.1 herr.2 hwrongCases hzeroStep
          rw [← hnextStep]
          exact hboundary
        have hnextAStrict : next.1.natAbs < 2^(n - 33) := by
          have hnonpos := hdata.2.2.2.1
          have hle := hdata.2.2.2.2.1
          have hnotEq : next.1.natAbs ≠ 2^(n - 33) := by
            intro heq
            have hcast : (next.1.natAbs : Int) = 2^(n - 33) := by exact_mod_cast heq
            have hneg : (next.1.natAbs : Int) = -next.1 :=
              Int.ofNat_natAbs_of_nonpos hnonpos
            apply hnotBoundary
            omega
          omega
        have hnextASize : bitLength next.1.natAbs ≤ n - 33 :=
          bitLength_natAbs_le_of_lt_two_pow hnextAStrict
        have hnextACharge : bitLength next.1.natAbs + (31 - t) ≤
            min (bitLength current.1.natAbs) (bitLength current.2.natAbs) := by
          omega
        have hnextLen : signedLengthSum next.1 next.2 + (31 - t) ≤
            signedLengthSum current.1 current.2 :=
          signedLengthSum_progress_of_retained_component hnextACharge hnextBRetained
        have hquotientBound :
            signedLengthSum (semolinaQuotients a b).1 (semolinaQuotients a b).2 + 62 ≤
              (signedLengthSum next.1 next.2 + 2 * (t + 1)) + 2 * r := by
          calc
            _ = signedLengthSum finish.scaledRealA finish.scaledRealB := hlenDiv
            _ ≤ signedLengthSum after.scaledRealA after.scaledRealB + 2 * r := hlen
            _ ≤ (signedLengthSum next.1 next.2 + 2 * (t + 1)) + 2 * r :=
              Nat.add_le_add_right hafterSize _
        dsimp [r] at hquotientBound
        omega

end InversionConvergence
end PastaAsm
