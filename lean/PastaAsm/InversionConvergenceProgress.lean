/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.InversionConvergence

/-!
# Progress of the approximate inversion batches

This module builds the charged bit-length argument on top of the stable
approximation-error and corrected `P ∨ Q` infrastructure.  It remains separate
while the convergence bridge is under development so architecture proofs that
import `InversionConvergence` keep a stable dependency.
-/

namespace PastaAsm
namespace InversionConvergence

/-- Componentwise absolute-value bounds imply a signed joint bit-length bound. -/
theorem signedLengthSum_le_of_natAbs_le {a b c d : Int}
    (ha : a.natAbs ≤ c.natAbs) (hb : b.natAbs ≤ d.natAbs) :
    signedLengthSum a b ≤ signedLengthSum c d := by
  unfold signedLengthSum
  exact Nat.add_le_add (Nat.size_le_size ha) (Nat.size_le_size hb)

/-- Doubling an integer increases the bit length of its absolute value by at
most one. -/
theorem bitLength_natAbs_two_mul_le (x : Int) :
    bitLength (2 * x).natAbs ≤ bitLength x.natAbs + 1 := by
  by_cases hx : x = 0
  · subst x
    simp
  · rw [Int.natAbs_mul]
    norm_num
    have habs : x.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hx
    have heq := bitLength_div_two_of_even (x := 2 * x.natAbs)
      (Nat.mul_ne_zero (by norm_num) habs) (by simp)
    norm_num at heq ⊢
    omega

/-- The bit length of a sum is at most one more than the larger input bit
length. -/
theorem bitLength_add_le_max_add_one (a b : Nat) :
    bitLength (a + b) ≤ max (bitLength a) (bitLength b) + 1 := by
  have ha : a < 2^(max (bitLength a) (bitLength b)) :=
    (lt_two_pow_bitLength a).trans_le
      (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _))
  have hb : b < 2^(max (bitLength a) (bitLength b)) :=
    (lt_two_pow_bitLength b).trans_le
      (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _))
  apply bitLength_le_of_lt_two_pow
  rw [pow_succ]
  omega

/-- The small side of `P` is dominated in absolute value by its large side. -/
theorem divergedSmall_natAbs_le_large_natAbs {large small : Int} {err : Nat}
    (hlarge : (4 * err : Int) ≤ large) (hsmall : small.natAbs < 2 * err) :
    small.natAbs ≤ large.natAbs := by
  have hnonneg : 0 ≤ large := by
    have herrNonneg : (0 : Int) ≤ err := by positivity
    omega
  have hlargeInt : (4 * err : Int) ≤ (large.natAbs : Nat) := by
    rw [Int.natAbs_of_nonneg hnonneg]
    exact hlarge
  have hlargeNat : 4 * err ≤ large.natAbs := by exact_mod_cast hlargeInt
  omega

/-- Subtracting an integer of no larger magnitude costs at most one bit. -/
theorem bitLength_natAbs_sub_le_left_add_one {a b : Int} (h : b.natAbs ≤ a.natAbs) :
    bitLength (a - b).natAbs ≤ bitLength a.natAbs + 1 := by
  have hsub : bitLength (a - b).natAbs ≤ bitLength (a.natAbs + b.natAbs) :=
    Nat.size_le_size (Int.natAbs_sub_le _ _)
  have hsize : bitLength b.natAbs ≤ bitLength a.natAbs := Nat.size_le_size h
  have hadd := bitLength_add_le_max_add_one a.natAbs b.natAbs
  rw [max_eq_left hsize] at hadd
  exact hsub.trans hadd

/-- From the first orientation of `P`, a controlled step increases the raw
scaled joint length by at most two.  The approximation-error hypotheses are
used only to force the synchronous control order. -/
theorem controlledStep_signedLengthSum_le_add_two_first {s : ControlledState}
    {scale err : Nat} (hscale : 0 < scale)
    (hlarge : (4 * err : Int) ≤ s.scaledRealA)
    (hsmallNonpos : s.scaledRealB ≤ 0)
    (hsmallAbs : s.scaledRealB.natAbs < 2 * err)
    (herrA : (s.scaledRealA - (scale : Int) * s.approxA).natAbs ≤ err)
    (herrB : (s.scaledRealB - (scale : Int) * s.approxB).natAbs ≤ err) :
    signedLengthSum (controlledStep s).scaledRealA (controlledStep s).scaledRealB ≤
      signedLengthSum s.scaledRealA s.scaledRealB + 2 := by
  have horder := divergedLarge_first_control hscale hlarge hsmallNonpos herrA herrB
  have hdom := divergedSmall_natAbs_le_large_natAbs hlarge hsmallAbs
  have hsub := bitLength_natAbs_sub_le_left_add_one hdom
  have hdouble := bitLength_natAbs_two_mul_le s.scaledRealB
  by_cases heven : Even s.approxA
  · rw [controlledStep, if_pos heven]
    change bitLength s.scaledRealA.natAbs + bitLength (2 * s.scaledRealB).natAbs ≤
      bitLength s.scaledRealA.natAbs + bitLength s.scaledRealB.natAbs + 2
    omega
  · rw [controlledStep, if_neg heven, if_pos horder]
    change bitLength (s.scaledRealA - s.scaledRealB).natAbs +
      bitLength (2 * s.scaledRealB).natAbs ≤
      bitLength s.scaledRealA.natAbs + bitLength s.scaledRealB.natAbs + 2
    omega

/-- From the second orientation of `P`, a controlled step increases the raw
scaled joint length by at most two. -/
theorem controlledStep_signedLengthSum_le_add_two_second {s : ControlledState}
    {scale err : Nat} (hscale : 0 < scale)
    (hlarge : (4 * err : Int) ≤ s.scaledRealB)
    (hsmallNonpos : s.scaledRealA ≤ 0)
    (hsmallAbs : s.scaledRealA.natAbs < 2 * err)
    (herrA : (s.scaledRealA - (scale : Int) * s.approxA).natAbs ≤ err)
    (herrB : (s.scaledRealB - (scale : Int) * s.approxB).natAbs ≤ err) :
    signedLengthSum (controlledStep s).scaledRealA (controlledStep s).scaledRealB ≤
      signedLengthSum s.scaledRealA s.scaledRealB + 2 := by
  have horder := divergedLarge_second_control hscale hlarge hsmallNonpos hsmallAbs herrA herrB
  have hdom := divergedSmall_natAbs_le_large_natAbs hlarge hsmallAbs
  have hsub := bitLength_natAbs_sub_le_left_add_one hdom
  have hdoubleA := bitLength_natAbs_two_mul_le s.scaledRealA
  have hdoubleB := bitLength_natAbs_two_mul_le s.scaledRealB
  by_cases heven : Even s.approxA
  · rw [controlledStep, if_pos heven]
    change bitLength s.scaledRealA.natAbs + bitLength (2 * s.scaledRealB).natAbs ≤
      bitLength s.scaledRealA.natAbs + bitLength s.scaledRealB.natAbs + 2
    omega
  · rw [controlledStep, if_neg heven, if_neg (Nat.not_le_of_gt horder)]
    change bitLength (s.scaledRealB - s.scaledRealA).natAbs +
      bitLength (2 * s.scaledRealA).natAbs ≤
      bitLength s.scaledRealA.natAbs + bitLength s.scaledRealB.natAbs + 2
    omega

/-- Unified raw charged-size estimate from `P`. -/
theorem controlledStep_signedLengthSum_le_add_two_of_large {s : ControlledState}
    {scale err : Nat} (hscale : 0 < scale)
    (herrA : (s.scaledRealA - (scale : Int) * s.approxA).natAbs ≤ err)
    (herrB : (s.scaledRealB - (scale : Int) * s.approxB).natAbs ≤ err)
    (h : ControlledDivergedLarge err s) :
    signedLengthSum (controlledStep s).scaledRealA (controlledStep s).scaledRealB ≤
      signedLengthSum s.scaledRealA s.scaledRealB + 2 := by
  rcases h with hfirst | hsecond
  · exact controlledStep_signedLengthSum_le_add_two_first hscale hfirst.1 hfirst.2.1
      hfirst.2.2 herrA herrB
  · exact controlledStep_signedLengthSum_le_add_two_second hscale hsecond.1 hsecond.2.1
      hsecond.2.2 herrA herrB

/-- After `n` remaining steps from the corrected invariant, either `Q` bounds
the final state or the scaled raw joint length has grown by at most `2*n`.
This is the mechanized form of lasting goodness. -/
theorem controlledSteps_small_or_signedLengthSum_le {s : ControlledState}
    {scale err bound : Nat} (n : Nat)
    (hscale : 0 < scale)
    (hclose : ∀ t, t < n →
      let st := controlledSteps t s
      (st.scaledRealA - ((scale * 2^t : Nat) : Int) * st.approxA).natAbs ≤ 2^t * err ∧
      (st.scaledRealB - ((scale * 2^t : Nat) : Int) * st.approxB).natAbs ≤ 2^t * err)
    (hinv : ControlledDiverged err s)
    (hbound : signedLengthSum s.scaledRealA s.scaledRealB ≤ bound) :
    ControlledDivergedSmall (2^n * err) (controlledSteps n s) ∨
      signedLengthSum (controlledSteps n s).scaledRealA
        (controlledSteps n s).scaledRealB ≤ bound + 2 * n := by
  induction n generalizing s scale err bound with
  | zero =>
      right
      simpa [controlledSteps] using hbound
  | succ n ih =>
      have hclose0 := hclose 0 (by omega)
      simp only [controlledSteps, pow_zero, Nat.one_mul, Nat.mul_one] at hclose0
      have hinvStep := controlledStep_diverged hscale hclose0.1 hclose0.2 hinv
      rcases hinv with hlarge | hsmall
      · have hlenStep := controlledStep_signedLengthSum_le_add_two_of_large
          hscale hclose0.1 hclose0.2 hlarge
        have hclose' : ∀ t, t < n →
            let st := controlledSteps t (controlledStep s)
            (st.scaledRealA - (((2 * scale) * 2^t : Nat) : Int) * st.approxA).natAbs ≤
                2^t * (2 * err) ∧
            (st.scaledRealB - (((2 * scale) * 2^t : Nat) : Int) * st.approxB).natAbs ≤
                2^t * (2 * err) := by
          intro t ht
          have hc := hclose (t + 1) (by omega)
          simpa [controlledSteps, pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hc
        have hrest := ih (s := controlledStep s) (scale := 2 * scale) (err := 2 * err)
          (bound := bound + 2) (by positivity) hclose' hinvStep (by omega)
        rw [controlledSteps]
        rcases hrest with hrestSmall | hrestLen
        · left
          simpa [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hrestSmall
        · right
          exact hrestLen.trans (by omega)
      · left
        have hsmallStep := controlledStep_divergedSmall hsmall
        have hscaled : ControlledScaledSmall (4 * (2 * err)) 0 (controlledStep s) := by
          simpa [ControlledDivergedSmall, ControlledScaledSmall] using hsmallStep
        have hrest := controlledSteps_scaledSmall n hscaled
        rw [controlledSteps]
        rcases hrest with ⟨hrestA, hrestB⟩
        constructor
        · exact hrestA.trans_le (by
            rw [pow_succ]
            ring_nf
            omega)
        · exact hrestB.trans_le (by
            rw [pow_succ]
            ring_nf
            omega)

/-- A first divergent no-swap subtraction enters the corrected `P ∨ Q`
region.  The retained positive component decides which disjunct applies. -/
theorem controlledStep_firstDivergence_noswap {s : ControlledState} {scale err : Nat}
    (herrPos : 0 < err)
    (hodd : ¬ Even s.approxA)
    (happrox : s.approxB ≤ s.approxA)
    (hrealPosB : 0 < s.scaledRealB)
    (hrealOrder : s.scaledRealA < s.scaledRealB)
    (herrA : (s.scaledRealA - (scale : Int) * s.approxA).natAbs ≤ err)
    (herrB : (s.scaledRealB - (scale : Int) * s.approxB).natAbs ≤ err) :
    ControlledDiverged (2 * err) (controlledStep s) := by
  have hbranch := controlledStep_divergent_noswap hodd happrox hrealOrder herrA herrB
  have hnextNonpos : (controlledStep s).scaledRealA ≤ 0 := by
    unfold controlledStep
    rw [if_neg hodd, if_pos happrox]
    exact sub_nonpos.mpr hrealOrder.le
  have hnextPos : 0 < (controlledStep s).scaledRealB := by
    rw [hbranch.2]
    positivity
  have hsmallP : (controlledStep s).scaledRealA.natAbs < 2 * (2 * err) := by
    omega
  by_cases hlarge : (4 * (2 * err) : Int) ≤ (controlledStep s).scaledRealB
  · left
    right
    exact ⟨hlarge, hnextNonpos, hsmallP⟩
  · right
    constructor
    · exact hsmallP.trans (by omega)
    · have habs : (((controlledStep s).scaledRealB.natAbs : Nat) : Int) =
          (controlledStep s).scaledRealB := Int.ofNat_natAbs_of_nonneg hnextPos.le
      have hltInt : (((controlledStep s).scaledRealB.natAbs : Nat) : Int) <
          (4 * (2 * err) : Nat) := by
        rw [habs]
        push_cast
        exact lt_of_not_ge hlarge
      exact_mod_cast hltInt

/-- Symmetric first-divergence entry for the swap-subtract branch. -/
theorem controlledStep_firstDivergence_swap {s : ControlledState} {scale err : Nat}
    (herrPos : 0 < err)
    (hodd : ¬ Even s.approxA)
    (happrox : s.approxA < s.approxB)
    (hrealPosA : 0 < s.scaledRealA)
    (hrealOrder : s.scaledRealB ≤ s.scaledRealA)
    (herrA : (s.scaledRealA - (scale : Int) * s.approxA).natAbs ≤ err)
    (herrB : (s.scaledRealB - (scale : Int) * s.approxB).natAbs ≤ err) :
    ControlledDiverged (2 * err) (controlledStep s) := by
  have hbranch := controlledStep_divergent_swap hodd happrox hrealOrder herrA herrB
  have hnextNonpos : (controlledStep s).scaledRealA ≤ 0 := by
    unfold controlledStep
    rw [if_neg hodd, if_neg (Nat.not_le_of_gt happrox)]
    exact sub_nonpos.mpr hrealOrder
  have hnextPos : 0 < (controlledStep s).scaledRealB := by
    rw [hbranch.2]
    positivity
  have hsmallP : (controlledStep s).scaledRealA.natAbs < 2 * (2 * err) := by
    omega
  by_cases hlarge : (4 * (2 * err) : Int) ≤ (controlledStep s).scaledRealB
  · left
    right
    exact ⟨hlarge, hnextNonpos, hsmallP⟩
  · right
    constructor
    · exact hsmallP.trans (by omega)
    · have habs : (((controlledStep s).scaledRealB.natAbs : Nat) : Int) =
          (controlledStep s).scaledRealB := Int.ofNat_natAbs_of_nonneg hnextPos.le
      have hltInt : (((controlledStep s).scaledRealB.natAbs : Nat) : Int) <
          (4 * (2 * err) : Nat) := by
        rw [habs]
        push_cast
        exact lt_of_not_ge hlarge
      exact_mod_cast hltInt

/-- Cancel a common power of two from an integer congruence. -/
theorem Int.ModEq.cancel_pow_two {x y : Int} {kept removed : Nat}
    (h : x ≡ y [ZMOD (2^(kept + removed) : Nat)])
    (hx : (2^removed : Int) ∣ x) (hy : (2^removed : Int) ∣ y) :
    x / (2^removed : Int) ≡ y / (2^removed : Int) [ZMOD (2^kept : Nat)] := by
  rcases hx with ⟨qx, rfl⟩
  rcases hy with ⟨qy, rfl⟩
  rw [Int.mul_ediv_cancel_left _ (by positivity), Int.mul_ediv_cancel_left _ (by positivity)]
  rw [Int.modEq_iff_dvd] at h ⊢
  have hmod : ((2^(kept + removed) : Nat) : Int) =
      (2^removed : Int) * (2^kept : Int) := by
    push_cast
    rw [pow_add]
    ring
  rw [hmod] at h
  have hdiff : (2^removed : Int) * qy - (2^removed : Int) * qx =
      (2^removed : Int) * (qy - qx) := by ring
  rw [hdiff] at h
  have hmul : (2^removed : Int) * (2^kept : Int) ∣
      (2^removed : Int) * (qy - qx) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  have hpowNe : (2^removed : Int) ≠ 0 := by exact_mod_cast (by positivity : (2^removed : Nat) ≠ 0)
  exact Int.dvd_of_mul_dvd_mul_left hpowNe hmul

/-- A row congruence and its exact approximate representation give a congruence
between the signed real quotient and the nonnegative approximate value. -/
theorem quotient_modEq_approx_of_row {realRow approxRow : Int} {approx kept t : Nat}
    (hcongr : realRow ≡ approxRow [ZMOD (2^(kept + t) : Nat)])
    (hdiv : (2^t : Int) ∣ realRow)
    (happrox : approxRow = (2^t : Int) * approx) :
    realRow / (2^t : Int) ≡ (approx : Int) [ZMOD (2^kept : Nat)] := by
  have hdivApprox : (2^t : Int) ∣ approxRow := ⟨approx, happrox⟩
  have hcancel := Int.ModEq.cancel_pow_two hcongr hdiv hdivApprox
  have hquotApprox : approxRow / (2^t : Int) = approx := by
    rw [happrox, Int.mul_ediv_cancel_left _ (by positivity)]
  simpa [hquotApprox] using hcancel

/-- Congruence modulo an even power of two transfers the low parity bit. -/
theorem emod_two_eq_of_modEq_pow_two {x : Int} {a kept : Nat} (hkept : 0 < kept)
    (h : x ≡ (a : Int) [ZMOD (2^kept : Nat)]) :
    x % 2 = (a : Int) % 2 := by
  have htwoNat : 2 ∣ 2^kept := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkept)
    exact ⟨2^r, by rw [pow_succ]; ring⟩
  have htwoInt : (2 : Int) ∣ ((2^kept : Nat) : Int) := by
    rcases htwoNat with ⟨q, hq⟩
    use q
    exact_mod_cast hq
  have hmod2 : x ≡ (a : Int) [ZMOD (2 : Int)] := h.of_dvd htwoInt
  exact hmod2

/-- Every actual Semolina prefix row applied to the full inputs is divisible
by its current denominator `2^t`, for `t ≤ 31`. -/
theorem semolina_prefix_full_width_dvd {a b t : Nat} (hb : Odd b) (ht : t ≤ 31) :
    let ap := semolinaApprox a b
    let s := approxSteps t (ApproxState.initial ap.1 ap.2)
    (2^t : Int) ∣ s.matrix.row0.apply a b ∧
    (2^t : Int) ∣ s.matrix.row1.apply a b := by
  let ap := semolinaApprox a b
  let s := approxSteps t (ApproxState.initial ap.1 ap.2)
  have hapodd : Odd ap.2 := by simpa [ap] using semolinaApprox_snd_odd (a := a) hb
  have hrepr := approxSteps_initial_representation t ap.1 ap.2 hapodd
  have hpowDvd : 2^t ∣ 2^31 := pow_dvd_pow 2 ht
  have hx31 : Nat.ModEq (2^31) a ap.1 := by
    change a % 2^31 = ap.1 % 2^31
    simpa [ap, semolinaApprox] using (approximate_fst_mod 32 a b).symm
  have hy31 : Nat.ModEq (2^31) b ap.2 := by
    change b % 2^31 = ap.2 % 2^31
    simpa [ap, semolinaApprox] using (approximate_snd_mod 32 a b).symm
  have hx : Nat.ModEq (2^t) a ap.1 := hx31.of_dvd hpowDvd
  have hy : Nat.ModEq (2^t) b ap.2 := hy31.of_dvd hpowDvd
  have hrow0 := SignedRow.apply_modEq s.matrix.row0 hx hy
  have hrow1 := SignedRow.apply_modEq s.matrix.row1 hx hy
  have hdiv0Approx : (2^t : Int) ∣ s.matrix.row0.apply ap.1 ap.2 := by
    refine ⟨s.a, ?_⟩
    simpa [s] using hrepr.1.symm
  have hdiv1Approx : (2^t : Int) ∣ s.matrix.row1.apply ap.1 ap.2 := by
    refine ⟨s.b, ?_⟩
    simpa [s] using hrepr.2.symm
  constructor
  · exact Int.modEq_zero_iff_dvd.mp (hrow0.trans hdiv0Approx.modEq_zero_int)
  · exact Int.modEq_zero_iff_dvd.mp (hrow1.trans hdiv1Approx.modEq_zero_int)

/-- Right-associated successor equation for the short-loop iterator. -/
theorem approxSteps_succ_right_progress (n : Nat) (s : ApproxState) :
    approxSteps (Nat.succ n) s = approxStep (approxSteps n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [approxSteps, ih]
      rfl

/-- Signed Euclidean division is associative when the first divisor is positive. -/
theorem ediv_mul_of_pos (x d e : Int) (hd : 0 < d) :
    x / (d * e) = (x / d) / e := by
  have h := Int.ediv_ediv (x := x) (y := d) (z := e)
  have hnot : ¬d < 0 := not_lt.mpr hd.le
  simp only [hnot, false_and, if_false, sub_zero] at h
  exact h.symm

/-- Division by the next power of two is division by the current power followed
by division by two. -/
theorem ediv_pow_succ (x : Int) (t : Nat) :
    x / (2^(t + 1) : Int) = (x / (2^t : Int)) / 2 := by
  rw [pow_succ]
  exact ediv_mul_of_pos x (2^t) 2 (by positivity)

/-- Cancel the current positive natural denominator, leaving division by two. -/
theorem nat_factor_ediv_double (d : Nat) (q : Int) (hd : 0 < d) :
    (d : Int) * q / ((2 * d : Nat) : Int) = q / 2 := by
  have hden : (((2 * d : Nat) : Int)) = (d : Int) * 2 := by
    push_cast
    ring
  rw [hden, ediv_mul_of_pos _ _ _ (by exact_mod_cast hd)]
  rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast Nat.ne_of_gt hd)]

/-- A doubled exact multiple divided by its doubled denominator recovers the
quotient. -/
theorem two_mul_nat_factor_ediv (d : Nat) (q : Int) (hd : 0 < d) :
    2 * ((d : Int) * q) / ((2 * d : Nat) : Int) = q := by
  apply Int.ediv_eq_of_eq_mul_right
  · exact_mod_cast (Nat.mul_ne_zero (by norm_num) (Nat.ne_of_gt hd))
  · push_cast
    ring

/-- Signed quotient recurrence driven by an approximate control pair. -/
def signedQuotientStep (approx : Nat × Nat) (real : Int × Int) : Int × Int :=
  if Even approx.1 then
    (real.1 / 2, real.2)
  else if approx.2 ≤ approx.1 then
    ((real.1 - real.2) / 2, real.2)
  else
    ((real.2 - real.1) / 2, real.1)

/-- Applying one short-loop row recurrence and dividing by the doubled exact
common denominator gives `signedQuotientStep` on the current quotients. -/
theorem approxStep_quotient_recurrence (s : ApproxState) (x y d : Nat)
    (hd : 0 < d)
    (hdiv0 : (d : Int) ∣ s.matrix.row0.apply x y)
    (hdiv1 : (d : Int) ∣ s.matrix.row1.apply x y) :
    let next := approxStep s
    (next.matrix.row0.apply x y / ((2 * d : Nat) : Int),
      next.matrix.row1.apply x y / ((2 * d : Nat) : Int)) =
    signedQuotientStep (s.a, s.b)
      (s.matrix.row0.apply x y / (d : Int), s.matrix.row1.apply x y / (d : Int)) := by
  rcases hdiv0 with ⟨q0, hq0⟩
  rcases hdiv1 with ⟨q1, hq1⟩
  have hdInt : (d : Int) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hcur0 : s.matrix.row0.apply x y / (d : Int) = q0 := by
    rw [hq0, Int.mul_ediv_cancel_left _ hdInt]
  have hcur1 : s.matrix.row1.apply x y / (d : Int) = q1 := by
    rw [hq1, Int.mul_ediv_cancel_left _ hdInt]
  unfold approxStep signedQuotientStep
  split_ifs <;>
    simp only [SignedRow.apply_sub, SignedRow.apply_double] <;>
    rw [hq0, hq1] <;>
    simp only [Int.mul_ediv_cancel_left _ hdInt] <;>
    apply Prod.ext
  · exact nat_factor_ediv_double d q0 hd
  · exact two_mul_nat_factor_ediv d q1 hd
  · have hfactor : (d : Int) * q0 - (d : Int) * q1 = d * (q0 - q1) := by ring
    rw [hfactor]
    exact nat_factor_ediv_double d (q0 - q1) hd
  · exact two_mul_nat_factor_ediv d q1 hd
  · have hfactor : (d : Int) * q1 - (d : Int) * q0 = d * (q1 - q0) := by ring
    rw [hfactor]
    exact nat_factor_ediv_double d (q1 - q0) hd
  · exact two_mul_nat_factor_ediv d q0 hd

/-- The two unscaled signed real values at a Semolina inner-loop prefix. -/
def semolinaPrefixReal (a b t : Nat) : Int × Int :=
  let ap := semolinaApprox a b
  let s := approxSteps t (ApproxState.initial ap.1 ap.2)
  (s.matrix.row0.apply a b / (2^t : Int),
   s.matrix.row1.apply a b / (2^t : Int))

/-- The approximate controls at a Semolina inner-loop prefix. -/
def semolinaPrefixApprox (a b t : Nat) : Nat × Nat :=
  let ap := semolinaApprox a b
  let s := approxSteps t (ApproxState.initial ap.1 ap.2)
  (s.a, s.b)

/-- Successive actual full-width prefix quotients obey the operation selected by
the approximate control state. -/
theorem semolinaPrefixReal_succ {a b t : Nat} (hb : Odd b) (ht : t < 31) :
    semolinaPrefixReal a b (t + 1) =
      signedQuotientStep (semolinaPrefixApprox a b t) (semolinaPrefixReal a b t) := by
  let ap := semolinaApprox a b
  let s := approxSteps t (ApproxState.initial ap.1 ap.2)
  have hdiv := semolina_prefix_full_width_dvd (a := a) (b := b) (t := t) hb ht.le
  have hrec := approxStep_quotient_recurrence s a b (2^t) (by positivity) hdiv.1 hdiv.2
  unfold semolinaPrefixReal semolinaPrefixApprox
  dsimp only
  rw [show t + 1 = Nat.succ t by omega, approxSteps_succ_right_progress]
  dsimp [ap, s] at hrec
  have hden : (2^(Nat.succ t) : Int) = ((2 * 2^t : Nat) : Int) := by
    push_cast
    rw [pow_succ]
    ring
  rw [hden]
  exact hrec

/-- Integer Euclidean division of a nonnegative natural cast agrees with
natural division. -/
theorem int_ediv_two_natCast (n : Nat) : (n : Int) / 2 = (n / 2 : Nat) := by
  norm_cast

/-- In a regular nonnegative state, parity agreement and comparison agreement
make the approximate-controlled signed recurrence exactly the binary-GCD
recurrence. -/
theorem signedQuotientStep_eq_exactStep {controlA controlB realA realB : Nat}
    (hparity : controlA % 2 = realA % 2)
    (horder : controlB ≤ controlA ↔ realB ≤ realA) :
    signedQuotientStep (controlA, controlB) ((realA : Int), (realB : Int)) =
      (((InversionSpec.exactStep realA realB).1 : Int),
        ((InversionSpec.exactStep realA realB).2 : Int)) := by
  have heven : Even controlA ↔ Even realA := by
    rw [Nat.even_iff, Nat.even_iff]
    omega
  unfold signedQuotientStep InversionSpec.exactStep
  by_cases hca : Even controlA
  · rw [if_pos hca, if_pos (heven.mp hca)]
    apply Prod.ext
    · exact int_ediv_two_natCast realA
    · rfl
  · have hra : ¬Even realA := fun h => hca (heven.mpr h)
    rw [if_neg hca, if_neg hra]
    by_cases horderC : controlB ≤ controlA
    · have horderR := horder.mp horderC
      rw [if_pos horderC, if_pos horderR]
      apply Prod.ext
      · rw [← Int.ofNat_sub horderR]
        exact int_ediv_two_natCast (realA - realB)
      · rfl
    · have horderR : ¬ realB ≤ realA := fun h => horderC (horder.mpr h)
      rw [if_neg horderC, if_neg horderR]
      apply Prod.ext
      · rw [← Int.ofNat_sub (Nat.le_of_not_ge horderR)]
        exact int_ediv_two_natCast (realB - realA)
      · rfl

/-- Every regular nonterminal approximate-controlled quotient operation loses
at least one joint bit, because it is exactly a binary-GCD operation. -/
theorem signedQuotientStep_regular_length {controlA controlB realA realB : Nat}
    (hparity : controlA % 2 = realA % 2)
    (horder : controlB ≤ controlA ↔ realB ≤ realA)
    (hne : realA ≠ 0) (hodd : Odd realB) :
    signedLengthSum (signedQuotientStep (controlA, controlB)
        ((realA : Int), (realB : Int))).1
      (signedQuotientStep (controlA, controlB)
        ((realA : Int), (realB : Int))).2 + 1 ≤
      signedLengthSum realA realB := by
  rw [signedQuotientStep_eq_exactStep hparity horder]
  simpa [signedLengthSum, lengthSum] using exactStep_lengthSum hne hodd

/-- At every prefix before the final operation, each signed real quotient has
the same parity bit as its approximate control component. -/
theorem semolina_prefix_quotient_emod_two {a b t : Nat} (hb : Odd b) (ht : t < 31) :
    let ap := semolinaApprox a b
    let s := approxSteps t (ApproxState.initial ap.1 ap.2)
    (s.matrix.row0.apply a b / (2^t : Int)) % 2 = (s.a : Int) % 2 ∧
    (s.matrix.row1.apply a b / (2^t : Int)) % 2 = (s.b : Int) % 2 := by
  let ap := semolinaApprox a b
  let s := approxSteps t (ApproxState.initial ap.1 ap.2)
  have hapodd : Odd ap.2 := by simpa [ap] using semolinaApprox_snd_odd (a := a) hb
  have hrepr := approxSteps_initial_representation t ap.1 ap.2 hapodd
  have hdiv := semolina_prefix_full_width_dvd (a := a) (b := b) (t := t) hb ht.le
  have hx31 : Nat.ModEq (2^31) a ap.1 := by
    change a % 2^31 = ap.1 % 2^31
    simpa [ap, semolinaApprox] using (approximate_fst_mod 32 a b).symm
  have hy31 : Nat.ModEq (2^31) b ap.2 := by
    change b % 2^31 = ap.2 % 2^31
    simpa [ap, semolinaApprox] using (approximate_snd_mod 32 a b).symm
  have hrow0 := SignedRow.apply_modEq s.matrix.row0 hx31 hy31
  have hrow1 := SignedRow.apply_modEq s.matrix.row1 hx31 hy31
  have hsum : 31 - t + t = 31 := by omega
  have hcongr0 : s.matrix.row0.apply a b / (2^t : Int) ≡ (s.a : Int)
      [ZMOD (2^(31 - t) : Nat)] := by
    apply quotient_modEq_approx_of_row (t := t)
    · simpa [hsum] using hrow0
    · exact hdiv.1
    · simpa [s] using hrepr.1.symm
  have hcongr1 : s.matrix.row1.apply a b / (2^t : Int) ≡ (s.b : Int)
      [ZMOD (2^(31 - t) : Nat)] := by
    apply quotient_modEq_approx_of_row (t := t)
    · simpa [hsum] using hrow1
    · exact hdiv.2
    · simpa [s] using hrepr.2.symm
  constructor
  · exact emod_two_eq_of_modEq_pow_two (by omega) hcongr0
  · exact emod_two_eq_of_modEq_pow_two (by omega) hcongr1

/-- Exact division by a positive natural divisor commutes with absolute value. -/
theorem natAbs_ediv_of_dvd {x : Int} {d : Nat} (hdpos : 0 < d) (hdiv : (d : Int) ∣ x) :
    (x / (d : Int)).natAbs = x.natAbs / d := by
  rcases hdiv with ⟨q, rfl⟩
  rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast Nat.ne_of_gt hdpos)]
  rw [Int.natAbs_mul]
  norm_num
  rw [Nat.mul_comm d q.natAbs, Nat.mul_div_left q.natAbs hdpos]

/-- Exact division by `2^bits` removes exactly `bits` from the
absolute-value bit length of a nonzero quotient. -/
theorem bitLength_natAbs_ediv_pow_add_eq {x : Int} {bits : Nat}
    (hdiv : (2^bits : Int) ∣ x) (hne : x / (2^bits : Int) ≠ 0) :
    bitLength (x / (2^bits : Int)).natAbs + bits = bitLength x.natAbs := by
  let q := x / (2^bits : Int)
  have hx : x = (2^bits : Int) * q := by
    have hcancel := Int.ediv_mul_cancel hdiv
    dsimp [q]
    rw [mul_comm]
    exact hcancel.symm
  rw [hx, Int.natAbs_mul]
  norm_num
  have hqabs : q.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hne
  have hshift : 2^bits * q.natAbs = q.natAbs <<< bits := by
    simp [Nat.shiftLeft_eq, Nat.mul_comm]
  rw [hshift]
  unfold bitLength
  rw [Nat.size_shiftLeft hqabs]

/-- Exact common division either reaches a terminal zero or removes twice the
exponent from joint signed length. -/
theorem signedLengthSum_ediv_pow_terminal_or_eq {a b : Int} {bits : Nat}
    (hdivA : (2^bits : Int) ∣ a) (hdivB : (2^bits : Int) ∣ b) :
    a / (2^bits : Int) = 0 ∨ b / (2^bits : Int) = 0 ∨
      signedLengthSum (a / (2^bits : Int)) (b / (2^bits : Int)) + 2 * bits =
        signedLengthSum a b := by
  by_cases ha : a / (2^bits : Int) = 0
  · exact Or.inl ha
  · by_cases hb : b / (2^bits : Int) = 0
    · exact Or.inr (Or.inl hb)
    · right
      right
      have hsizeA := bitLength_natAbs_ediv_pow_add_eq hdivA ha
      have hsizeB := bitLength_natAbs_ediv_pow_add_eq hdivB hb
      unfold signedLengthSum
      omega

/-- Dividing a strict natural product bound by its positive left factor removes
that factor. -/
theorem div_lt_of_lt_mul_left {x d bound : Nat} (hd : 0 < d) (h : x < d * bound) :
    x / d < bound := by
  exact (Nat.div_lt_iff_lt_mul hd).mpr (by simpa [Nat.mul_comm] using h)

/-- The `Q` endpoint directly bounds both exact batch quotients. -/
theorem divergedSmall_quotients_lt {s : ControlledState} {err divisor : Nat}
    (hdivisor : 0 < divisor)
    (hdivA : (divisor : Int) ∣ s.scaledRealA)
    (hdivB : (divisor : Int) ∣ s.scaledRealB)
    (hsmall : ControlledDivergedSmall err s) :
    (s.scaledRealA / (divisor : Int)).natAbs < (4 * err) / divisor + 1 ∧
    (s.scaledRealB / (divisor : Int)).natAbs < (4 * err) / divisor + 1 := by
  rw [natAbs_ediv_of_dvd hdivisor hdivA, natAbs_ediv_of_dvd hdivisor hdivB]
  constructor
  · exact Nat.lt_succ_of_le (Nat.div_le_div_right hsmall.1.le)
  · exact Nat.lt_succ_of_le (Nat.div_le_div_right hsmall.2.le)

/-- At the end of a 31-step Semolina prefix, entering `Q` with the concrete
propagated error gives two quotients below `2^(n-29) + 1`. -/
theorem semolina_final_small_quotients {n : Nat} {s : ControlledState}
    (hdivA : (2^31 : Int) ∣ s.scaledRealA)
    (hdivB : (2^31 : Int) ∣ s.scaledRealB)
    (hsmall : ControlledDivergedSmall (2^(n - 2)) s) :
    (s.scaledRealA / (2^31 : Int)).natAbs < (4 * 2^(n - 2)) / 2^31 + 1 ∧
    (s.scaledRealB / (2^31 : Int)).natAbs < (4 * 2^(n - 2)) / 2^31 + 1 :=
  divergedSmall_quotients_lt (by positivity) hdivA hdivB hsmall

/-- The designated odd second component remains odd under an exact binary-GCD
operation. -/
theorem exactStep_second_odd_progress {a b : Nat} (hb : Odd b) :
    Odd (InversionSpec.exactStep a b).2 := by
  unfold InversionSpec.exactStep
  split_ifs with ha hab
  · exact hb
  · exact hb
  · exact Nat.not_even_iff_odd.mp ha

/-- The designated odd second component remains odd under exact iteration. -/
theorem exactSteps_second_odd_progress (t : Nat) {a b : Nat} (hb : Odd b) :
    Odd (InversionSpec.exactSteps t (a, b)).2 := by
  induction t generalizing a b with
  | zero => simpa [InversionSpec.exactSteps] using hb
  | succ t ih =>
      rw [InversionSpec.exactSteps]
      exact ih (exactStep_second_odd_progress (a := a) hb)

/-- A zero first component stays zero under exact iteration. -/
theorem exactSteps_zero_first_progress (t b : Nat) :
    (InversionSpec.exactSteps t (0, b)).1 = 0 := by
  induction t generalizing b with
  | zero => rfl
  | succ t ih =>
      rw [InversionSpec.exactSteps]
      simpa [InversionSpec.exactStep] using ih b

/-- Exact iteration either terminates or charges one joint bit per operation. -/
theorem exactSteps_terminal_or_length_progress (t : Nat) {a b : Nat} (hb : Odd b) :
    (InversionSpec.exactSteps t (a, b)).1 = 0 ∨
      lengthSum (InversionSpec.exactSteps t (a, b)).1
          (InversionSpec.exactSteps t (a, b)).2 + t ≤ lengthSum a b := by
  induction t generalizing a b with
  | zero =>
      right
      simp [InversionSpec.exactSteps]
  | succ t ih =>
      by_cases ha : a = 0
      · left
        subst a
        simpa [InversionSpec.exactSteps, InversionSpec.exactStep] using
          exactSteps_zero_first_progress t b
      · have hone := exactStep_lengthSum ha hb
        have hodd := exactStep_second_odd_progress (a := a) hb
        have hrest := ih (a := (InversionSpec.exactStep a b).1)
          (b := (InversionSpec.exactStep a b).2) hodd
        rw [InversionSpec.exactSteps]
        rcases hrest with hzero | hlen
        · exact Or.inl hzero
        · right
          have htail : InversionSpec.exactSteps t
                ((InversionSpec.exactStep a b).1, (InversionSpec.exactStep a b).2) =
              InversionSpec.exactSteps t (InversionSpec.exactStep a b) := by rw [Prod.eta]
          rw [htail] at hlen
          change lengthSum
              (InversionSpec.exactSteps t (InversionSpec.exactStep a b)).1
              (InversionSpec.exactSteps t (InversionSpec.exactStep a b)).2 + (t + 1) ≤
            lengthSum a b
          omega

/-- A power-of-two upper bound, including equality at the power, gives the
corresponding successor bit-length bound. -/
theorem bitLength_le_succ_of_le_two_pow {x e : Nat} (h : x ≤ 2^e) :
    bitLength x ≤ e + 1 := by
  exact (Nat.size_le_size h).trans_eq Nat.size_pow

/-- A positive natural is at least the power indexed one below its bit length. -/
theorem two_pow_pred_bitLength_le {x : Nat} (hx : 0 < x) :
    2^(bitLength x - 1) ≤ x := by
  change 2^(Nat.size x - 1) ≤ x
  exact (Nat.lt_size).mp (by
    have hsize : 0 < Nat.size x := Nat.size_pos.mpr hx
    omega)

/-- If the first approximate control is zero, every remaining controlled
operation is a halving of the first real quotient: its scaled numerator stays
fixed while the second scaled numerator acquires the whole remaining power of
two.  This is the exact absorbing behavior needed in the boundary case
`realA = -2^(n-33)`, where the divergent subtraction also makes `approxA = 0`. -/
theorem controlledSteps_zero_approxA (r : Nat) {s : ControlledState}
    (hzero : s.approxA = 0) :
    let finish := controlledSteps r s
    finish.approxA = 0 ∧ finish.approxB = s.approxB ∧
      finish.scaledRealA = s.scaledRealA ∧
      finish.scaledRealB = (2^r : Int) * s.scaledRealB := by
  induction r generalizing s with
  | zero => simp [controlledSteps, hzero]
  | succ r ih =>
      rw [controlledSteps]
      have hstepA : (controlledStep s).approxA = 0 := by
        simp [controlledStep, hzero]
      have hrest := ih (s := controlledStep s) hstepA
      rcases hrest with ⟨ha, hb, hrealA, hrealB⟩
      refine ⟨ha, ?_, ?_, ?_⟩
      · simpa [controlledStep, hzero] using hb
      · simpa [controlledStep, hzero] using hrealA
      · rw [hrealB]
        simp [controlledStep, hzero, pow_succ]
        ring

/-- The coupled execution exposes the exact concrete approximation state and
both full-width row numerators at an arbitrary Semolina prefix. -/
theorem semolina_controlled_prefix (a b t : Nat) :
    let ap := semolinaApprox a b
    let c := controlledSteps t (ControlledState.initial ap.1 ap.2 a b)
    let s := approxSteps t (ApproxState.initial ap.1 ap.2)
    c.approxA = s.a ∧ c.approxB = s.b ∧
      c.scaledRealA = s.matrix.row0.apply a b ∧
      c.scaledRealB = s.matrix.row1.apply a b := by
  exact controlledSteps_initial_matches t (semolinaApprox a b).1
    (semolinaApprox a b).2 a b

end InversionConvergence
end PastaAsm
