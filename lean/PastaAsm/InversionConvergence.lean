/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.InversionSpec
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring

/-!
# Convergence of the approximate inversion batches

This file models the arithmetic algorithm implemented by Semolina's
`__ab_approximation_31_256`, `__inner_loop_31_256`, and full-width signed
multiply-and-shift update.  In particular, the approximate inner-loop trace is
*not* identified with the exact full-width binary-GCD trace.  Its low bits are
exact, while its high bits have a quantified error; the full-width row update
may become negative when a comparison diverges, and the implementation resolves
that error by taking an absolute value.

The generic definitions use Pornin's parameter `k`: a `2*k`-bit approximation
keeps `k-1` low bits and `k+1` high bits, then performs `k-1` inner operations.
The assembly instantiates `k = 32`, hence 31 operations in each batch.
-/

namespace PastaAsm
namespace InversionConvergence

open InversionSpec

/-- Bit length, with the conventional value zero for zero. -/
abbrev bitLength (x : Nat) : Nat := Nat.size x

/-- Joint progress measure of the nonnegative GCD state. -/
def lengthSum (a b : Nat) : Nat := bitLength a + bitLength b

@[simp] theorem bitLength_zero : bitLength 0 = 0 := Nat.size_zero

@[simp] theorem bitLength_one : bitLength 1 = 1 := Nat.size_one

/-- A natural is strictly below the power indexed by its bit length. -/
theorem lt_two_pow_bitLength (x : Nat) : x < 2^(bitLength x) := Nat.lt_size_self x

/-- Conversely, an upper power-of-two bound bounds bit length. -/
theorem bitLength_le_of_lt_two_pow {x n : Nat} (h : x < 2^n) : bitLength x ≤ n :=
  Nat.size_le.mpr h

/-- If a joint length bound is below `n`, then the product is below `2^n`. -/
theorem product_lt_two_pow_of_lengthSum_le {a b n : Nat} (h : lengthSum a b ≤ n) :
    a * b < 2^n := by
  calc
    a * b < 2^(bitLength a) * 2^(bitLength b) :=
      Nat.mul_lt_mul_of_lt_of_lt (lt_two_pow_bitLength a) (lt_two_pow_bitLength b)
    _ = 2^(lengthSum a b) := by rw [lengthSum, pow_add]
    _ ≤ 2^n := Nat.pow_le_pow_right (by omega) h

/-- Joint bit length for the signed row numerators used while reasoning about
approximation-controlled steps. -/
def signedLengthSum (a b : Int) : Nat := bitLength a.natAbs + bitLength b.natAbs

/-- An absolute power-of-two bound gives the corresponding signed bit-length
bound. -/
theorem bitLength_natAbs_le_of_lt_two_pow {x : Int} {n : Nat}
    (h : x.natAbs < 2^n) : bitLength x.natAbs ≤ n :=
  bitLength_le_of_lt_two_pow h

/-- The bit length of an integer's absolute value is monotone under an absolute
value bound. -/
theorem bitLength_natAbs_le_of_natAbs_le {x y : Int} (h : x.natAbs ≤ y.natAbs) :
    bitLength x.natAbs ≤ bitLength y.natAbs :=
  Nat.size_le_size h

/-- Convert a natural absolute-value upper bound into two linear integer
inequalities.  Keeping this isolated avoids sending nonlinear `natAbs` terms to
later arithmetic automation. -/
theorem int_bounds_of_natAbs_le {x : Int} {bound : Nat} (h : x.natAbs ≤ bound) :
    -(bound : Int) ≤ x ∧ x ≤ bound := by
  rcases Int.natAbs_eq x with hx | hx
  · constructor <;> omega
  · constructor <;> omega

/-- Strict counterpart of `int_bounds_of_natAbs_le`. -/
theorem int_bounds_of_natAbs_lt {x : Int} {bound : Nat} (h : x.natAbs < bound) :
    -(bound : Int) < x ∧ x < bound := by
  rcases Int.natAbs_eq x with hx | hx
  · constructor <;> omega
  · constructor <;> omega

/-- Two strict linear bounds imply the corresponding natural absolute-value
bound. -/
theorem natAbs_lt_of_int_bounds {x : Int} {bound : Nat}
    (hlower : -(bound : Int) < x) (hupper : x < bound) : x.natAbs < bound := by
  rcases Int.natAbs_eq x with hx | hx
  · omega
  · omega

/-- Dividing a positive even natural by two removes exactly one bit from its
bit length. -/
theorem bitLength_div_two_of_even {x : Nat} (hx : x ≠ 0) (heven : Even x) :
    bitLength (x / 2) + 1 = bitLength x := by
  have htwo : 2 ∣ x := even_iff_two_dvd.mp heven
  have hpos : 0 < x / 2 := Nat.div_pos (by omega) (by omega)
  have hdecomp : x = Nat.bit false (x / 2) := by
    simp only [Nat.bit_false]
    rw [Nat.mul_comm]
    exact (Nat.div_mul_cancel htwo).symm
  change Nat.size (x / 2) + 1 = Nat.size x
  rw [show Nat.size x = Nat.size (Nat.bit false (x / 2)) by rw [← hdecomp]]
  have hbit : Nat.bit false (x / 2) ≠ 0 := by
    simp only [Nat.bit_false]
    exact Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hpos)
  simpa [Nat.succ_eq_add_one] using (Nat.size_bit hbit).symm

/-- One nonterminal exact binary-GCD operation decreases the joint bit length
by at least one. -/
theorem exactStep_lengthSum {a b : Nat} (ha : a ≠ 0) (hbodd : Odd b) :
    lengthSum (exactStep a b).1 (exactStep a b).2 + 1 ≤ lengthSum a b := by
  unfold exactStep
  split_ifs with haeven hab
  · have hhalf := bitLength_div_two_of_even ha haeven
    change bitLength (a / 2) + bitLength b + 1 ≤ bitLength a + bitLength b
    calc
      bitLength (a / 2) + bitLength b + 1 =
          (bitLength (a / 2) + 1) + bitLength b := by omega
      _ = bitLength a + bitLength b := by rw [hhalf]
      _ ≤ bitLength a + bitLength b := le_rfl
  · have haodd : Odd a := Nat.not_even_iff_odd.mp haeven
    have hdiff : Even (a - b) := by
      rcases haodd with ⟨qa, hqa⟩
      rcases hbodd with ⟨qb, hqb⟩
      use qa - qb
      omega
    by_cases hd : a - b = 0
    · change bitLength ((a - b) / 2) + bitLength b + 1 ≤ bitLength a + bitLength b
      rw [hd]
      simp only [Nat.zero_div, bitLength_zero, Nat.zero_add]
      have hsizene : bitLength a ≠ 0 := by
        intro hzero
        exact ha (Nat.size_eq_zero.mp hzero)
      calc
        bitLength b + 1 = 1 + bitLength b := Nat.add_comm _ _
        _ ≤ bitLength a + bitLength b :=
          Nat.add_le_add_right (Nat.one_le_iff_ne_zero.mpr hsizene) _
    · have hhalf := bitLength_div_two_of_even hd hdiff
      change bitLength ((a - b) / 2) + bitLength b + 1 ≤ bitLength a + bitLength b
      calc
        bitLength ((a - b) / 2) + bitLength b + 1 =
            (bitLength ((a - b) / 2) + 1) + bitLength b := by omega
        _ = bitLength (a - b) + bitLength b := by rw [hhalf]
        _ ≤ bitLength a + bitLength b :=
          Nat.add_le_add_right (Nat.size_le_size (Nat.sub_le a b)) _
  · have hlt : a < b := Nat.lt_of_not_ge hab
    have haodd : Odd a := Nat.not_even_iff_odd.mp haeven
    have hdiff : Even (b - a) := by
      rcases haodd with ⟨qa, hqa⟩
      rcases hbodd with ⟨qb, hqb⟩
      use qb - qa
      omega
    have hd : b - a ≠ 0 := Nat.sub_ne_zero_iff_lt.mpr hlt
    have hhalf := bitLength_div_two_of_even hd hdiff
    change bitLength ((b - a) / 2) + bitLength a + 1 ≤ bitLength a + bitLength b
    calc
      bitLength ((b - a) / 2) + bitLength a + 1 =
          bitLength a + (bitLength ((b - a) / 2) + 1) := by omega
      _ = bitLength a + bitLength (b - a) := by rw [hhalf]
      _ ≤ bitLength a + bitLength b :=
        Nat.add_le_add_left (Nat.size_le_size (Nat.sub_le b a)) _

/-- Approximate values together with signed full-width row numerators evolved
under the same controls.  After `t` steps, each real component has the common
scale `2^t`; this avoids signed-division semantics while still exposing the
first-divergence sign behavior. -/
structure ControlledState where
  approxA : Nat
  approxB : Nat
  scaledRealA : Int
  scaledRealB : Int
  deriving DecidableEq, Repr

/-- One inner operation whose parity and comparison come from the approximate
components and whose corresponding row recurrence is applied to the scaled
signed real components. -/
def controlledStep (s : ControlledState) : ControlledState :=
  if Even s.approxA then
    ⟨s.approxA / 2, s.approxB, s.scaledRealA, 2 * s.scaledRealB⟩
  else if s.approxB ≤ s.approxA then
    ⟨(s.approxA - s.approxB) / 2, s.approxB,
      s.scaledRealA - s.scaledRealB, 2 * s.scaledRealB⟩
  else
    ⟨(s.approxB - s.approxA) / 2, s.approxA,
      s.scaledRealB - s.scaledRealA, 2 * s.scaledRealA⟩

/-- Iterate the coupled approximate-control/scaled-real trace. -/
def controlledSteps : Nat → ControlledState → ControlledState
  | 0, s => s
  | n + 1, s => controlledSteps n (controlledStep s)

/-- Both signed real numerators are below a common threshold at prefix `t`.
The factor `2^t` accounts for their accumulated common denominator.  This is
the corrected form of the absorbing small-value region: both absolute
components are bounded, rather than only an ordered minimum and maximum. -/
def ControlledScaledSmall (threshold t : Nat) (s : ControlledState) : Prop :=
  s.scaledRealA.natAbs < 2^t * threshold ∧
  s.scaledRealB.natAbs < 2^t * threshold

/-- Corrected large/small post-divergence region, expressed in units of the
current propagated approximation error.  One signed numerator is large and
positive; the other is nonpositive and has magnitude below twice the error.
The disjunction records which row currently carries the large component. -/
def ControlledDivergedLarge (err : Nat) (s : ControlledState) : Prop :=
  (4 * err ≤ s.scaledRealA ∧ s.scaledRealB ≤ 0 ∧
      s.scaledRealB.natAbs < 2 * err) ∨
  (4 * err ≤ s.scaledRealB ∧ s.scaledRealA ≤ 0 ∧
      s.scaledRealA.natAbs < 2 * err)

/-- Corrected `Q` region in units of the current propagated error.  Bounding
both absolute components is essential for persistence. -/
def ControlledDivergedSmall (err : Nat) (s : ControlledState) : Prop :=
  s.scaledRealA.natAbs < 4 * err ∧ s.scaledRealB.natAbs < 4 * err

/-- The corrected post-divergence disjunctive invariant. -/
def ControlledDiverged (err : Nat) (s : ControlledState) : Prop :=
  ControlledDivergedLarge err s ∨ ControlledDivergedSmall err s

/-- Once both signed real components enter the scaled small-value region, every
possible approximation-controlled operation keeps them there.  This statement
is trace-independent and remains valid after a divergent comparison. -/
theorem controlledStep_scaledSmall {threshold t : Nat} {s : ControlledState}
    (h : ControlledScaledSmall threshold t s) :
    ControlledScaledSmall threshold (t + 1) (controlledStep s) := by
  rcases h with ⟨ha, hb⟩
  have hdouble : 2^(t + 1) * threshold =
      (2^t * threshold) + (2^t * threshold) := by
    rw [pow_succ]
    ring
  have ha' : s.scaledRealA.natAbs < 2^(t + 1) * threshold := by
    rw [hdouble]
    exact ha.trans_le (Nat.le_add_right _ _)
  have hbdoubled : 2 * s.scaledRealB.natAbs < 2^(t + 1) * threshold := by
    rw [hdouble, two_mul]
    exact Nat.add_lt_add hb hb
  have hadoubled : 2 * s.scaledRealA.natAbs < 2^(t + 1) * threshold := by
    rw [hdouble, two_mul]
    exact Nat.add_lt_add ha ha
  unfold ControlledScaledSmall controlledStep
  split_ifs
  · constructor
    · exact ha'
    · simpa [Int.natAbs_mul, Nat.mul_comm] using hbdoubled
  · constructor
    · exact (Int.natAbs_sub_le _ _).trans_lt (by
        rw [hdouble]
        exact Nat.add_lt_add ha hb)
    · simpa [Int.natAbs_mul, Nat.mul_comm] using hbdoubled
  · constructor
    · exact (Int.natAbs_sub_le _ _).trans_lt (by
        rw [hdouble]
        exact Nat.add_lt_add hb ha)
    · simpa [Int.natAbs_mul, Nat.mul_comm] using hadoubled

/-- The corrected small-value region is absorbing through any number of
remaining approximation-controlled operations. -/
theorem controlledSteps_scaledSmall {threshold t : Nat} (n : Nat) {s : ControlledState}
    (h : ControlledScaledSmall threshold t s) :
    ControlledScaledSmall threshold (t + n) (controlledSteps n s) := by
  induction n generalizing t s with
  | zero => simpa [controlledSteps] using h
  | succ n ih =>
      rw [controlledSteps]
      have hstep := controlledStep_scaledSmall (t := t) h
      have hrest := ih (t := t + 1) hstep
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest

/-- The corrected `Q` region persists when the error unit doubles with one
controlled operation. -/
theorem controlledStep_divergedSmall {err : Nat} {s : ControlledState}
    (h : ControlledDivergedSmall err s) :
    ControlledDivergedSmall (2 * err) (controlledStep s) := by
  have hsmall : ControlledScaledSmall (4 * err) 0 s := by
    simpa [ControlledDivergedSmall, ControlledScaledSmall] using h
  have hnext := controlledStep_scaledSmall hsmall
  simpa [ControlledDivergedSmall, ControlledScaledSmall, Nat.mul_assoc,
    Nat.mul_left_comm, Nat.mul_comm] using hnext

/-- Prefix closeness to nonnegative approximate values supplies the lower bound
needed by the corrected post-divergence invariant. -/
theorem real_ge_neg_error {real : Int} {scale approx err : Nat}
    (h : (real - (scale : Int) * approx).natAbs ≤ err) : -(err : Int) ≤ real := by
  have hb := (int_bounds_of_natAbs_le h).1
  have hnonneg : (0 : Int) ≤ scale * approx := by positivity
  omega

/-- Doubling the small nonpositive component gives exactly the next
`P` bound.  The same estimate is stronger than the corresponding `Q` bound. -/
theorem natAbs_two_mul_lt_nextLargeSmall {x : Int} {err : Nat}
    (h : x.natAbs < 2 * err) : (2 * x).natAbs < 2 * (2 * err) := by
  rw [Int.natAbs_mul]
  norm_num
  omega

/-- A nonnegative integer below `8 * err` has exactly the natural absolute
value bound used by the next `Q` region. -/
theorem natAbs_lt_nextSmall {x : Int} {err : Nat}
    (hlower : 0 ≤ x) (hupper : x < 8 * (err : Int)) :
    x.natAbs < 4 * (2 * err) := by
  apply natAbs_lt_of_int_bounds
  · norm_num [Nat.cast_mul]
    omega
  · norm_num [Nat.cast_mul] at *
    omega

/-- If the first real numerator is in the large-positive side of `P` and the
second in its small-nonpositive side, closeness forces the approximate order
needed by the actual control step. -/
theorem divergedLarge_first_control {s : ControlledState} {scale err : Nat}
    (hscale : 0 < scale)
    (hlarge : (4 * err : Int) ≤ s.scaledRealA)
    (hsmall : s.scaledRealB ≤ 0)
    (herrA : (s.scaledRealA - (scale : Int) * s.approxA).natAbs ≤ err)
    (herrB : (s.scaledRealB - (scale : Int) * s.approxB).natAbs ≤ err) :
    s.approxB ≤ s.approxA := by
  have haUpper := (int_bounds_of_natAbs_le herrA).2
  have hbLower := (int_bounds_of_natAbs_le herrB).1
  have hscaleA : (3 * err : Int) ≤ scale * s.approxA := by omega
  have hscaleB : (scale : Int) * s.approxB ≤ err := by omega
  by_contra hnot
  have hlt : s.approxA < s.approxB := Nat.lt_of_not_ge hnot
  have hmul : (scale : Int) * s.approxA < scale * s.approxB :=
    mul_lt_mul_of_pos_left (by exact_mod_cast hlt) (by exact_mod_cast hscale)
  have herrNonneg : (0 : Int) ≤ err := by positivity
  omega

/-- One controlled operation preserves corrected `P ∨ Q` from the orientation
where the first row is large.  The closeness hypotheses are exactly the
propagated prefix-error facts used to exclude a wrong swap. -/
theorem controlledStep_divergedLarge_first {s : ControlledState} {scale err : Nat}
    (hscale : 0 < scale)
    (hlarge : (4 * err : Int) ≤ s.scaledRealA)
    (hsmallNonpos : s.scaledRealB ≤ 0)
    (hsmallAbs : s.scaledRealB.natAbs < 2 * err)
    (herrA : (s.scaledRealA - (scale : Int) * s.approxA).natAbs ≤ err)
    (herrB : (s.scaledRealB - (scale : Int) * s.approxB).natAbs ≤ err) :
    ControlledDiverged (2 * err) (controlledStep s) := by
  have horder := divergedLarge_first_control hscale hlarge hsmallNonpos herrA herrB
  have hBnextP : (2 * s.scaledRealB).natAbs < 2 * (2 * err) :=
    natAbs_two_mul_lt_nextLargeSmall hsmallAbs
  have hBnextQ : (2 * s.scaledRealB).natAbs < 4 * (2 * err) := by omega
  have hAnonneg : (0 : Int) ≤ s.scaledRealA := by
    have herrNonneg : (0 : Int) ≤ err := by positivity
    omega
  unfold controlledStep
  by_cases heven : Even s.approxA
  · rw [if_pos heven]
    by_cases hnextLarge : (8 * err : Int) ≤ s.scaledRealA
    · left
      left
      change 4 * ((2 * err : Nat) : Int) ≤ s.scaledRealA ∧
        2 * s.scaledRealB ≤ 0 ∧ (2 * s.scaledRealB).natAbs < 2 * (2 * err)
      refine ⟨?_, ?_, hBnextP⟩
      · push_cast
        omega
      · exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) hsmallNonpos
    · right
      change s.scaledRealA.natAbs < 4 * (2 * err) ∧
        (2 * s.scaledRealB).natAbs < 4 * (2 * err)
      refine ⟨?_, hBnextQ⟩
      apply natAbs_lt_nextSmall hAnonneg
      exact lt_of_not_ge hnextLarge
  · rw [if_neg heven, if_pos horder]
    by_cases hnextLarge : (8 * err : Int) ≤ s.scaledRealA - s.scaledRealB
    · left
      left
      change 4 * ((2 * err : Nat) : Int) ≤ s.scaledRealA - s.scaledRealB ∧
        2 * s.scaledRealB ≤ 0 ∧ (2 * s.scaledRealB).natAbs < 2 * (2 * err)
      refine ⟨?_, ?_, hBnextP⟩
      · push_cast
        omega
      · exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) hsmallNonpos
    · right
      change (s.scaledRealA - s.scaledRealB).natAbs < 4 * (2 * err) ∧
        (2 * s.scaledRealB).natAbs < 4 * (2 * err)
      refine ⟨?_, hBnextQ⟩
      apply natAbs_lt_nextSmall
      · omega
      · exact lt_of_not_ge hnextLarge

/-- In the second orientation of `P`, an odd first approximation must be
strictly below the second approximation.  Positivity of the error follows from
the strict small-component bound, so the separated real components cannot have
equal approximations. -/
theorem divergedLarge_second_control {s : ControlledState} {scale err : Nat}
    (hscale : 0 < scale)
    (hlarge : (4 * err : Int) ≤ s.scaledRealB)
    (hsmall : s.scaledRealA ≤ 0)
    (hsmallAbs : s.scaledRealA.natAbs < 2 * err)
    (herrA : (s.scaledRealA - (scale : Int) * s.approxA).natAbs ≤ err)
    (herrB : (s.scaledRealB - (scale : Int) * s.approxB).natAbs ≤ err) :
    s.approxA < s.approxB := by
  have haLower := (int_bounds_of_natAbs_le herrA).1
  have hbUpper := (int_bounds_of_natAbs_le herrB).2
  have herrPos : 0 < err := by omega
  have hscaleA : (scale : Int) * s.approxA ≤ err := by omega
  have hscaleB : (3 * err : Int) ≤ scale * s.approxB := by omega
  by_contra hnot
  have horder : s.approxB ≤ s.approxA := Nat.le_of_not_gt hnot
  have hmul : (scale : Int) * s.approxB ≤ scale * s.approxA :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast horder) (by positivity)
  omega

/-- One controlled operation preserves corrected `P ∨ Q` from the orientation
where the second row is large.  Unlike the first orientation, the even branch
retains that orientation, while the odd branch necessarily swaps into the
first orientation. -/
theorem controlledStep_divergedLarge_second {s : ControlledState} {scale err : Nat}
    (hscale : 0 < scale)
    (hlarge : (4 * err : Int) ≤ s.scaledRealB)
    (hsmallNonpos : s.scaledRealA ≤ 0)
    (hsmallAbs : s.scaledRealA.natAbs < 2 * err)
    (herrA : (s.scaledRealA - (scale : Int) * s.approxA).natAbs ≤ err)
    (herrB : (s.scaledRealB - (scale : Int) * s.approxB).natAbs ≤ err) :
    ControlledDiverged (2 * err) (controlledStep s) := by
  have horder := divergedLarge_second_control hscale hlarge hsmallNonpos hsmallAbs herrA herrB
  have hAnextP : (2 * s.scaledRealA).natAbs < 2 * (2 * err) :=
    natAbs_two_mul_lt_nextLargeSmall hsmallAbs
  have hAnextQ : (2 * s.scaledRealA).natAbs < 4 * (2 * err) := by omega
  unfold controlledStep
  by_cases heven : Even s.approxA
  · rw [if_pos heven]
    left
    right
    change 4 * ((2 * err : Nat) : Int) ≤ 2 * s.scaledRealB ∧
      s.scaledRealA ≤ 0 ∧ s.scaledRealA.natAbs < 2 * (2 * err)
    refine ⟨?_, hsmallNonpos, ?_⟩
    · push_cast
      omega
    · omega
  · rw [if_neg heven, if_neg (Nat.not_le_of_gt horder)]
    by_cases hnextLarge : (8 * err : Int) ≤ s.scaledRealB - s.scaledRealA
    · left
      left
      change 4 * ((2 * err : Nat) : Int) ≤ s.scaledRealB - s.scaledRealA ∧
        2 * s.scaledRealA ≤ 0 ∧ (2 * s.scaledRealA).natAbs < 2 * (2 * err)
      refine ⟨?_, ?_, hAnextP⟩
      · push_cast
        omega
      · exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) hsmallNonpos
    · right
      change (s.scaledRealB - s.scaledRealA).natAbs < 4 * (2 * err) ∧
        (2 * s.scaledRealA).natAbs < 4 * (2 * err)
      refine ⟨?_, hAnextQ⟩
      apply natAbs_lt_nextSmall
      · omega
      · exact lt_of_not_ge hnextLarge

/-- The corrected `P ∨ Q` invariant persists for one operation whenever the
current signed numerators satisfy their propagated prefix-error bounds. -/
theorem controlledStep_diverged {s : ControlledState} {scale err : Nat}
    (hscale : 0 < scale)
    (herrA : (s.scaledRealA - (scale : Int) * s.approxA).natAbs ≤ err)
    (herrB : (s.scaledRealB - (scale : Int) * s.approxB).natAbs ≤ err)
    (h : ControlledDiverged err s) :
    ControlledDiverged (2 * err) (controlledStep s) := by
  rcases h with hlarge | hsmall
  · rcases hlarge with hfirst | hsecond
    · exact controlledStep_divergedLarge_first hscale hfirst.1 hfirst.2.1 hfirst.2.2
        herrA herrB
    · exact controlledStep_divergedLarge_second hscale hsecond.1 hsecond.2.1 hsecond.2.2
        herrA herrB
  · exact Or.inr (controlledStep_divergedSmall hsmall)

/-- Iterated corrected persistence.  Prefix closeness is an explicit input at
each operation; in the concrete application it is discharged by
`semolina_prefix_error_of_odd`, independently of any exact-trace agreement. -/
theorem controlledSteps_diverged {s : ControlledState} {scale err : Nat} (n : Nat)
    (hscale : 0 < scale)
    (hclose : ∀ t, t < n →
      let st := controlledSteps t s
      (st.scaledRealA - ((scale * 2^t : Nat) : Int) * st.approxA).natAbs ≤ 2^t * err ∧
      (st.scaledRealB - ((scale * 2^t : Nat) : Int) * st.approxB).natAbs ≤ 2^t * err)
    (h : ControlledDiverged err s) :
    ControlledDiverged (2^n * err) (controlledSteps n s) := by
  induction n generalizing s scale err with
  | zero => simpa [controlledSteps] using h
  | succ n ih =>
      have hclose0 := hclose 0 (by omega)
      simp only [controlledSteps, pow_zero, Nat.one_mul, Nat.mul_one] at hclose0
      have hstep := controlledStep_diverged hscale hclose0.1 hclose0.2 h
      have hscale' : 0 < 2 * scale := by positivity
      have hclose' : ∀ t, t < n →
          let st := controlledSteps t (controlledStep s)
          (st.scaledRealA - (((2 * scale) * 2^t : Nat) : Int) * st.approxA).natAbs ≤
              2^t * (2 * err) ∧
          (st.scaledRealB - (((2 * scale) * 2^t : Nat) : Int) * st.approxB).natAbs ≤
              2^t * (2 * err) := by
        intro t ht
        have hc := hclose (t + 1) (by omega)
        simpa [controlledSteps, pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hc
      have hrest := ih hscale' hclose' hstep
      simpa [controlledSteps, pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hrest

/-- Matrix plus approximate state maintained by the short inner loop. -/
structure ApproxState where
  a : Nat
  b : Nat
  matrix : SignedMatrix
  deriving DecidableEq, Repr

/-- Initial short-loop state. -/
def ApproxState.initial (a b : Nat) : ApproxState := ⟨a, b, identityMatrix⟩

/-- One operation of Semolina's short inner loop.

`b` is odd in all reachable states.  If `a` is even it is halved; otherwise the
states and rows are conditionally swapped, the odd states are subtracted, and
the difference is halved.  The row not divided by two is doubled to retain the
common denominator. -/
def approxStep (s : ApproxState) : ApproxState :=
  if Even s.a then
    ⟨s.a / 2, s.b, ⟨s.matrix.row0, s.matrix.row1.double⟩⟩
  else if s.b ≤ s.a then
    ⟨(s.a - s.b) / 2, s.b, ⟨s.matrix.row0.sub s.matrix.row1, s.matrix.row1.double⟩⟩
  else
    ⟨(s.b - s.a) / 2, s.a, ⟨s.matrix.row1.sub s.matrix.row0, s.matrix.row0.double⟩⟩

/-- Iterate the short inner loop. -/
def approxSteps : Nat → ApproxState → ApproxState
  | 0, s => s
  | n + 1, s => approxSteps n (approxStep s)

/-- Forgetting scaled real values gives the approximate control pair. -/
def ControlledState.approxPair (s : ControlledState) : Nat × Nat :=
  (s.approxA, s.approxB)

/-- View a controlled state as an approximation state with identity rows; used
only for the one-step value recurrence. -/
def ControlledState.toApproxState (s : ControlledState) : ApproxState :=
  ⟨s.approxA, s.approxB, identityMatrix⟩

/-- Initialize the coupled trace from approximate controls and full-width
values. -/
def ControlledState.initial (approxA approxB realA realB : Nat) : ControlledState :=
  ⟨approxA, approxB, realA, realB⟩

/-- The approximate components of one coupled step agree with `approxStep`. -/
theorem controlledStep_approx (s : ControlledState) :
    (controlledStep s).approxA = (approxStep s.toApproxState).a ∧
    (controlledStep s).approxB = (approxStep s.toApproxState).b := by
  unfold controlledStep ControlledState.toApproxState approxStep
  split_ifs <;> exact ⟨rfl, rfl⟩

/-- A coupled state and matrix state describe the same approximate values and
scaled full-width row applications. -/
def ControlledMatches (x y : Nat) (c : ControlledState) (s : ApproxState) : Prop :=
  c.approxA = s.a ∧ c.approxB = s.b ∧
  c.scaledRealA = s.matrix.row0.apply x y ∧
  c.scaledRealB = s.matrix.row1.apply x y

/-- Lockstep is preserved by one approximation-controlled operation. -/
theorem controlledMatches_step {x y : Nat} {c : ControlledState} {s : ApproxState}
    (h : ControlledMatches x y c s) :
    ControlledMatches x y (controlledStep c) (approxStep s) := by
  rcases h with ⟨ha, hb, hrealA, hrealB⟩
  unfold ControlledMatches controlledStep approxStep
  rw [ha, hb]
  split_ifs
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · exact hrealA
    · rw [hrealB]
      simp [SignedRow.apply, SignedRow.double]
      ring
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · rw [hrealA, hrealB]
      simp [SignedRow.apply, SignedRow.sub]
      ring
    · rw [hrealB]
      simp [SignedRow.apply, SignedRow.double]
      ring
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · rw [hrealA, hrealB]
      simp [SignedRow.apply, SignedRow.sub]
      ring
    · rw [hrealA]
      simp [SignedRow.apply, SignedRow.double]
      ring

/-- Lockstep is preserved through every operation. -/
theorem controlledMatches_steps {x y : Nat} (n : Nat) {c : ControlledState} {s : ApproxState}
    (h : ControlledMatches x y c s) :
    ControlledMatches x y (controlledSteps n c) (approxSteps n s) := by
  induction n generalizing c s with
  | zero => simpa [controlledSteps, approxSteps] using h
  | succ n ih =>
      rw [controlledSteps, approxSteps]
      exact ih (controlledMatches_step h)

/-- Coupled execution from identity rows exactly exposes both the approximate
trace and the signed full-width row numerators at every prefix length. -/
theorem controlledSteps_initial_matches (n approxA approxB realA realB : Nat) :
    ControlledMatches realA realB
      (controlledSteps n (ControlledState.initial approxA approxB realA realB))
      (approxSteps n (ApproxState.initial approxA approxB)) := by
  apply controlledMatches_steps n
  simp [ControlledMatches, ControlledState.initial, ApproxState.initial,
    identityMatrix, SignedRow.apply]

/-- The inner loop performs one of the three coefficient recurrences already
bounded in `InversionSpec`. -/
theorem approxStep_coeffStep (s : ApproxState) :
    CoeffStep s.matrix (approxStep s).matrix := by
  unfold approxStep
  split_ifs <;> constructor

/-- The matrix emitted after `n` actual approximation-controlled operations has
the shared `2^n` row bound. -/
theorem approxSteps_coeffSteps (n : Nat) (s : ApproxState) :
    CoeffSteps n s.matrix (approxSteps n s).matrix := by
  induction n generalizing s with
  | zero => exact CoeffSteps.zero _
  | succ n ih =>
      rw [approxSteps]
      exact CoeffSteps.succ (approxStep_coeffStep s) (ih (approxStep s))

/-- The matrix emitted after `n` actual approximation-controlled operations has
the shared `2^n` row bound. -/
theorem approxSteps_matrix_bounded (n a b : Nat) :
    (approxSteps n (ApproxState.initial a b)).matrix.Bounded (2^n) :=
  inner_loop_matrix_bounded (approxSteps_coeffSteps n (ApproxState.initial a b))

/-- `b` remains odd through one short-loop operation. -/
theorem approxStep_second_odd (s : ApproxState) (hb : Odd s.b) : Odd (approxStep s).b := by
  unfold approxStep
  split_ifs with ha hab
  · exact hb
  · exact hb
  · exact Nat.not_even_iff_odd.mp ha

/-- `b` remains odd through every short-loop operation. -/
theorem approxSteps_second_odd (n : Nat) (s : ApproxState) (hb : Odd s.b) :
    Odd (approxSteps n s).b := by
  induction n generalizing s with
  | zero => simpa [approxSteps] using hb
  | succ n ih =>
      rw [approxSteps]
      exact ih _ (approxStep_second_odd s hb)

@[simp] theorem SignedRow.apply_double (r : SignedRow) (x y : Int) :
    r.double.apply x y = 2 * r.apply x y := by
  simp [SignedRow.apply, SignedRow.double]
  ring

@[simp] theorem SignedRow.apply_sub (r s : SignedRow) (x y : Int) :
    (r.sub s).apply x y = r.apply x y - s.apply x y := by
  simp [SignedRow.apply, SignedRow.sub]
  ring

/-- A row amplifies componentwise approximation error by at most its `ℓ₁`
norm. -/
theorem SignedRow.approx_error_le (r : SignedRow) (x y ax ay scale : Int) (err : Nat)
    (hx : (x - scale * ax).natAbs ≤ err)
    (hy : (y - scale * ay).natAbs ≤ err) :
    (r.apply x y - scale * r.apply ax ay).natAbs ≤ r.norm * err := by
  have happly := r.natAbs_apply_le (x - scale * ax) (y - scale * ay) err hx hy
  have heq : r.apply x y - scale * r.apply ax ay =
      r.apply (x - scale * ax) (y - scale * ay) := by
    unfold SignedRow.apply
    ring
  rw [heq]
  exact happly

theorem two_mul_half_of_even {n : Nat} (h : Even n) : 2 * (n / 2) = n := by
  rw [Nat.mul_comm]
  exact Nat.div_mul_cancel (even_iff_two_dvd.mp h)

/-- Integer-scaled form of exact halving, convenient after casting update rows. -/
theorem scaled_half_of_even (scale n : Nat) (h : Even n) :
    (2 : Int) * scale * (n / 2) = scale * n := by
  have hn : (2 : Int) * (n / 2) = n := by exact_mod_cast two_mul_half_of_even h
  calc
    (2 : Int) * scale * (n / 2) = (scale : Int) * (2 * (n / 2)) := by ring
    _ = (scale : Int) * n := by rw [hn]

/-- One step advances the exact common-denominator row representation of the
nonnegative short-loop values.  Signs are retained here; absolute values enter
only when the resulting matrix is applied to the full-width state. -/
theorem approxStep_representation {scale : Nat} (s : ApproxState) (x y : Nat)
    (ha : (scale : Int) * s.a = s.matrix.row0.apply x y)
    (hb : (scale : Int) * s.b = s.matrix.row1.apply x y)
    (hodd : Odd s.b) :
    ((2 * scale : Nat) : Int) * (approxStep s).a =
        (approxStep s).matrix.row0.apply x y ∧
    ((2 * scale : Nat) : Int) * (approxStep s).b =
        (approxStep s).matrix.row1.apply x y := by
  unfold approxStep
  split_ifs with hea hab
  · have hhalf : 2 * (s.a / 2) = s.a := two_mul_half_of_even hea
    simp only [SignedRow.apply_double]
    constructor
    · rw [← ha]
      push_cast
      exact scaled_half_of_even scale s.a hea
    · rw [← hb]
      push_cast
      ring
  · have haodd : Odd s.a := Nat.not_even_iff_odd.mp hea
    have hdiff : Even (s.a - s.b) := by
      rcases haodd with ⟨qa, hqa⟩
      rcases hodd with ⟨qb, hqb⟩
      use qa - qb
      omega
    have hhalf : 2 * ((s.a - s.b) / 2) = s.a - s.b := two_mul_half_of_even hdiff
    simp only [SignedRow.apply_sub, SignedRow.apply_double]
    constructor
    · rw [← ha, ← hb]
      change (2 : Int) * (scale : Int) * (((s.a - s.b) / 2 : Nat) : Int) =
        (scale : Int) * s.a - (scale : Int) * s.b
      calc
        (2 : Int) * scale * (((s.a - s.b) / 2 : Nat) : Int) =
            scale * ((s.a - s.b : Nat) : Int) := scaled_half_of_even scale (s.a - s.b) hdiff
        _ = (scale : Int) * s.a - scale * s.b := by
          rw [Int.ofNat_sub hab]
          ring
    · rw [← hb]
      push_cast
      ring
  · have haodd : Odd s.a := Nat.not_even_iff_odd.mp hea
    have hlt : s.a < s.b := Nat.lt_of_not_ge hab
    have hdiff : Even (s.b - s.a) := by
      rcases haodd with ⟨qa, hqa⟩
      rcases hodd with ⟨qb, hqb⟩
      use qb - qa
      omega
    have hhalf : 2 * ((s.b - s.a) / 2) = s.b - s.a := two_mul_half_of_even hdiff
    simp only [SignedRow.apply_sub, SignedRow.apply_double]
    constructor
    · rw [← ha, ← hb]
      change (2 : Int) * (scale : Int) * (((s.b - s.a) / 2 : Nat) : Int) =
        (scale : Int) * s.b - (scale : Int) * s.a
      calc
        (2 : Int) * scale * (((s.b - s.a) / 2 : Nat) : Int) =
            scale * ((s.b - s.a : Nat) : Int) := scaled_half_of_even scale (s.b - s.a) hdiff
        _ = (scale : Int) * s.b - scale * s.a := by
          rw [Int.ofNat_sub hlt.le]
          ring
    · rw [← ha]
      push_cast
      ring

/-- Iterating the short loop advances the common denominator by `2^n` while
preserving the exact signed row representation. -/
theorem approxSteps_representation {scale : Nat} (n : Nat) (s : ApproxState) (x y : Nat)
    (ha : (scale : Int) * s.a = s.matrix.row0.apply x y)
    (hb : (scale : Int) * s.b = s.matrix.row1.apply x y)
    (hodd : Odd s.b) :
    ((scale * 2^n : Nat) : Int) * (approxSteps n s).a =
        (approxSteps n s).matrix.row0.apply x y ∧
    ((scale * 2^n : Nat) : Int) * (approxSteps n s).b =
        (approxSteps n s).matrix.row1.apply x y := by
  induction n generalizing s scale with
  | zero => simpa [approxSteps] using And.intro ha hb
  | succ n ih =>
      rw [approxSteps]
      rcases approxStep_representation s x y ha hb hodd with ⟨ha', hb'⟩
      have hrest := ih (s := approxStep s) (scale := 2 * scale) ha' hb'
        (approxStep_second_odd s hodd)
      simpa [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hrest

/-- In particular, the final short-loop rows applied to the approximated inputs
are exactly divisible by the accumulated denominator. -/
theorem approxSteps_initial_representation (n a b : Nat) (hb : Odd b) :
    ((2^n : Nat) : Int) * (approxSteps n (ApproxState.initial a b)).a =
        (approxSteps n (ApproxState.initial a b)).matrix.row0.apply a b ∧
    ((2^n : Nat) : Int) * (approxSteps n (ApproxState.initial a b)).b =
        (approxSteps n (ApproxState.initial a b)).matrix.row1.apply a b := by
  have h := approxSteps_representation (scale := 1) n (ApproxState.initial a b) a b
    (by simp [ApproxState.initial, identityMatrix, SignedRow.apply])
    (by simp [ApproxState.initial, identityMatrix, SignedRow.apply]) hb
  simpa using h

/-- Determinant of the signed transition matrix. -/
def matrixDet (m : SignedMatrix) : Int :=
  m.row0.left * m.row1.right - m.row0.right * m.row1.left

@[simp] theorem identityMatrix_det : matrixDet identityMatrix = 1 := by
  simp [matrixDet, identityMatrix]

/-- Every short-loop row operation doubles the determinant in absolute value;
a subtraction branch may also change its sign because of a row swap. -/
theorem approxStep_det_natAbs (s : ApproxState) :
    (matrixDet (approxStep s).matrix).natAbs = 2 * (matrixDet s.matrix).natAbs := by
  unfold approxStep
  split_ifs
  · have hdet : matrixDet { row0 := s.matrix.row0, row1 := s.matrix.row1.double } =
        2 * matrixDet s.matrix := by simp [matrixDet, SignedRow.double]; ring
    rw [hdet, Int.natAbs_mul]
    norm_num
  · have hdet : matrixDet
        { row0 := s.matrix.row0.sub s.matrix.row1, row1 := s.matrix.row1.double } =
        2 * matrixDet s.matrix := by simp [matrixDet, SignedRow.double, SignedRow.sub]; ring
    rw [hdet, Int.natAbs_mul]
    norm_num
  · have hdet : matrixDet
        { row0 := s.matrix.row1.sub s.matrix.row0, row1 := s.matrix.row0.double } =
        -(2 * matrixDet s.matrix) := by simp [matrixDet, SignedRow.double, SignedRow.sub]; ring
    rw [hdet, Int.natAbs_neg, Int.natAbs_mul]
    norm_num

/-- Determinant growth from an arbitrary short-loop state. -/
theorem approxSteps_det_natAbs_from (n : Nat) (s : ApproxState) :
    (matrixDet (approxSteps n s).matrix).natAbs = 2^n * (matrixDet s.matrix).natAbs := by
  induction n generalizing s with
  | zero => simp [approxSteps]
  | succ n ih =>
      rw [approxSteps, ih, approxStep_det_natAbs, pow_succ]
      ring

/-- After `n` approximation-controlled operations from identity rows, the
transition determinant has magnitude exactly `2^n`. -/
theorem approxSteps_det_natAbs (n a b : Nat) :
    (matrixDet (approxSteps n (ApproxState.initial a b)).matrix).natAbs = 2^n := by
  rw [approxSteps_det_natAbs_from]
  simp [ApproxState.initial]

/-- Cramer's-rule identity for a scaled two-row transition whose second output
is one and whose first output is zero.  This is the algebraic source of the
sharp final-coefficient bound: the selected input coefficient is the initial
modulus times the opposite entry, not an arbitrary `2^scheduleBits` value. -/
theorem terminal_second_cramer {m : SignedMatrix} {input modulus scale : Int}
    (hfirst : m.row0.apply input modulus = 0)
    (hsecond : m.row1.apply input modulus = scale) :
    matrixDet m * modulus = m.row0.left * scale ∧
    matrixDet m * input = -(m.row0.right * scale) := by
  constructor
  · unfold matrixDet SignedRow.apply at *
    calc
      (m.row0.left * m.row1.right - m.row0.right * m.row1.left) * modulus =
          -(m.row1.left * (m.row0.left * input + m.row0.right * modulus)) +
          m.row0.left * (m.row1.left * input + m.row1.right * modulus) := by ring
      _ = m.row0.left * scale := by rw [hfirst, hsecond]; ring
  · unfold matrixDet SignedRow.apply at *
    calc
      (m.row0.left * m.row1.right - m.row0.right * m.row1.left) * input =
          m.row1.right * (m.row0.left * input + m.row0.right * modulus) -
          m.row0.right * (m.row1.left * input + m.row1.right * modulus) := by ring
      _ = -(m.row0.right * scale) := by rw [hfirst, hsecond]; ring

/-- Symmetric Cramer's-rule identity when the first terminal state is one and
the second is zero. -/
theorem terminal_first_cramer {m : SignedMatrix} {input modulus scale : Int}
    (hfirst : m.row0.apply input modulus = scale)
    (hsecond : m.row1.apply input modulus = 0) :
    matrixDet m * modulus = -(m.row1.left * scale) ∧
    matrixDet m * input = m.row1.right * scale := by
  constructor
  · unfold matrixDet SignedRow.apply at *
    calc
      (m.row0.left * m.row1.right - m.row0.right * m.row1.left) * modulus =
          -(m.row1.left * (m.row0.left * input + m.row0.right * modulus)) +
          m.row0.left * (m.row1.left * input + m.row1.right * modulus) := by ring
      _ = -(m.row1.left * scale) := by rw [hfirst, hsecond]; ring
  · unfold matrixDet SignedRow.apply at *
    calc
      (m.row0.left * m.row1.right - m.row0.right * m.row1.left) * input =
          m.row1.right * (m.row0.left * input + m.row0.right * modulus) -
          m.row0.right * (m.row1.left * input + m.row1.right * modulus) := by ring
      _ = m.row1.right * scale := by rw [hfirst, hsecond]; ring

/-- Splice `lowBits` low bits with the high quotient beginning `d` bits
above them.  Semolina uses `lowBits = 31` and `d = n - 64`. -/
def spliceApprox (lowBits d x : Nat) : Nat :=
  x % 2^lowBits + 2^lowBits * (x / 2^(d + lowBits))

/-- Scaling a spliced approximation back to the full-width alignment incurs
strictly less error than one omitted middle window. -/
theorem spliceApprox_error (lowBits d x : Nat) :
    ((x : Int) - (2^d : Nat) * (spliceApprox lowBits d x : Nat)).natAbs <
      2^(d + lowBits) := by
  let window := 2^(d + lowBits)
  let scaledLow := 2^d * (x % 2^lowBits)
  have hwindow : 0 < window := by positivity
  have hrem : x % window < window := Nat.mod_lt _ hwindow
  have hlow : x % 2^lowBits < 2^lowBits := Nat.mod_lt _ (by positivity)
  have hscaledLow : scaledLow < window := by
    dsimp [scaledLow, window]
    calc
      2^d * (x % 2^lowBits) < 2^d * 2^lowBits :=
        Nat.mul_lt_mul_of_pos_left hlow (by positivity)
      _ = 2^(d + lowBits) := by rw [pow_add]
  have hdecomp : x = x % window + window * (x / window) := by
    simpa [Nat.mul_comm] using (Nat.mod_add_div x window).symm
  have herr :
      (x : Int) - (2^d : Nat) * (spliceApprox lowBits d x : Nat) =
        (x % window : Nat) - (scaledLow : Nat) := by
    calc
      (x : Int) - (2^d : Nat) * (spliceApprox lowBits d x : Nat) =
          ((x % window + window * (x / window) : Nat) : Int) -
            (2^d : Nat) * (spliceApprox lowBits d x : Nat) := by rw [← hdecomp]
      _ = (x % window : Nat) - (scaledLow : Nat) := by
        dsimp [spliceApprox, window, scaledLow]
        rw [pow_add]
        ring
  rw [herr]
  exact Int.natAbs_coe_sub_coe_lt_of_lt hrem hscaledLow

/-- The top-and-bottom-bit approximation used by the implementation.

When both values fit in `2*k` bits it is exact.  Otherwise it retains `k-1`
low bits and the `k+1` bits beginning at the common top alignment. -/
def approximate (k a b : Nat) : Nat × Nat :=
  let n := max (bitLength a) (bitLength b)
  if n ≤ 2 * k then (a, b)
  else
    let shift := n - k - 1
    let low := 2^(k - 1)
    (a % low + low * (a / 2^shift), b % low + low * (b / 2^shift))

/-- In the non-exact branch, each extracted value has the paper's strict
high-window error bound. -/
theorem approximate_error {k a b : Nat} (hkgt : 1 < k)
    (hlarge : 2 * k < max (bitLength a) (bitLength b)) :
    let n := max (bitLength a) (bitLength b)
    ((a : Int) - (2^(n - 2*k) : Nat) * (approximate k a b).1).natAbs <
        2^(n - k - 1) ∧
    ((b : Int) - (2^(n - 2*k) : Nat) * (approximate k a b).2).natAbs <
        2^(n - k - 1) := by
  let n := max (bitLength a) (bitLength b)
  have hk : k ≤ n := by dsimp [n]; omega
  have h2k : 2 * k ≤ n := by dsimp [n]; omega
  have hshift : n - k - 1 = (n - 2*k) + (k - 1) := by omega
  have hfst := spliceApprox_error (k - 1) (n - 2*k) a
  have hsnd := spliceApprox_error (k - 1) (n - 2*k) b
  have happ : approximate k a b =
      (spliceApprox (k - 1) (n - 2*k) a,
       spliceApprox (k - 1) (n - 2*k) b) := by
    simp only [approximate]
    rw [if_neg (Nat.not_le_of_gt hlarge)]
    dsimp [n, spliceApprox]
    rw [hshift]
  change
    ((a : Int) - (2^(n - 2*k) : Nat) * (approximate k a b).1).natAbs <
        2^(n - k - 1) ∧
    ((b : Int) - (2^(n - 2*k) : Nat) * (approximate k a b).2).natAbs <
        2^(n - k - 1)
  rw [happ]
  simpa [hshift] using And.intro hfst hsnd

/-- The approximation preserves exactly the low `k-1` bits. -/
theorem approximate_fst_mod (k a b : Nat) :
    (approximate k a b).1 % 2^(k - 1) = a % 2^(k - 1) := by
  simp only [approximate]
  split_ifs
  · rfl
  · simp [Nat.add_mod]

/-- The approximation preserves exactly the low `k-1` bits of the second state. -/
theorem approximate_snd_mod (k a b : Nat) :
    (approximate k a b).2 % 2^(k - 1) = b % 2^(k - 1) := by
  simp only [approximate]
  split_ifs
  · rfl
  · simp [Nat.add_mod]

/-- The concrete Semolina top-and-bottom approximation. -/
def semolinaApprox (a b : Nat) : Nat × Nat := approximate 32 a b

/-- Semolina's concrete approximation preserves oddness of the designated
second state. -/
theorem semolinaApprox_snd_odd {a b : Nat} (hb : Odd b) : Odd (semolinaApprox a b).2 := by
  rw [Nat.odd_iff] at hb ⊢
  have hlow : (semolinaApprox a b).2 % 2^31 = b % 2^31 := by
    simpa [semolinaApprox] using approximate_snd_mod 32 a b
  change (semolinaApprox a b).2 % 2 = 1
  calc
    (semolinaApprox a b).2 % 2 = ((semolinaApprox a b).2 % 2^31) % 2 := by
      symm
      exact Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 2^31)
    _ = (b % 2^31) % 2 := by rw [hlow]
    _ = b % 2 := Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 2^31)
    _ = 1 := hb

/-- Signed linear combinations preserve componentwise congruence. -/
theorem SignedRow.apply_modEq {modulus x x' y y' : Nat} (r : SignedRow)
    (hx : Nat.ModEq modulus x x') (hy : Nat.ModEq modulus y y') :
    Int.ModEq modulus (r.apply x y) (r.apply x' y') := by
  unfold SignedRow.apply
  have hleft := (Int.natCast_modEq_iff.mpr hx).mul_left r.left
  have hright := (Int.natCast_modEq_iff.mpr hy).mul_left r.right
  exact hleft.add hright

/-- At every prefix, the signed full-width row applications remain close to the
corresponding scaled approximate values.  This is Appendix A.1's propagated
error estimate, stated without assuming that controls match the full-width
trace. -/
theorem approxSteps_error_bound {t approxA approxB realA realB scale err : Nat}
    (hodd : Odd approxB)
    (herrA : ((realA : Int) - scale * approxA).natAbs < err)
    (herrB : ((realB : Int) - scale * approxB).natAbs < err) :
    let s := approxSteps t (ApproxState.initial approxA approxB)
    (s.matrix.row0.apply realA realB -
        (scale : Int) * (2^t : Nat) * s.a).natAbs ≤ 2^t * err ∧
    (s.matrix.row1.apply realA realB -
        (scale : Int) * (2^t : Nat) * s.b).natAbs ≤ 2^t * err := by
  let s := approxSteps t (ApproxState.initial approxA approxB)
  change
    (s.matrix.row0.apply realA realB -
        (scale : Int) * (2^t : Nat) * s.a).natAbs ≤ 2^t * err ∧
    (s.matrix.row1.apply realA realB -
        (scale : Int) * (2^t : Nat) * s.b).natAbs ≤ 2^t * err
  have hrepr := approxSteps_initial_representation t approxA approxB hodd
  have hrepr0 : (2^t : Int) * s.a = s.matrix.row0.apply approxA approxB := by
    simpa [s] using hrepr.1
  have hrepr1 : (2^t : Int) * s.b = s.matrix.row1.apply approxA approxB := by
    simpa [s] using hrepr.2
  have hbound : s.matrix.Bounded (2^t) := by
    simpa [s] using approxSteps_matrix_bounded t approxA approxB
  have herrAle : ((realA : Int) - scale * approxA).natAbs ≤ err := herrA.le
  have herrBle : ((realB : Int) - scale * approxB).natAbs ≤ err := herrB.le
  have hrow0 := SignedRow.approx_error_le s.matrix.row0
    realA realB approxA approxB scale err herrAle herrBle
  have hrow1 := SignedRow.approx_error_le s.matrix.row1
    realA realB approxA approxB scale err herrAle herrBle
  have hscale0 : (scale : Int) * (2^t : Nat) * s.a =
      scale * s.matrix.row0.apply approxA approxB := by
    calc
      (scale : Int) * (2^t : Nat) * s.a = scale * ((2^t : Int) * s.a) := by
        norm_num
        ring
      _ = scale * s.matrix.row0.apply approxA approxB := by rw [hrepr0]
  have hscale1 : (scale : Int) * (2^t : Nat) * s.b =
      scale * s.matrix.row1.apply approxA approxB := by
    calc
      (scale : Int) * (2^t : Nat) * s.b = scale * ((2^t : Int) * s.b) := by
        norm_num
        ring
      _ = scale * s.matrix.row1.apply approxA approxB := by rw [hrepr1]
  constructor
  · rw [hscale0]
    exact hrow0.trans (Nat.mul_le_mul_right err hbound.1)
  · rw [hscale1]
    exact hrow1.trans (Nat.mul_le_mul_right err hbound.2)

/-- Concrete Appendix-A error estimate for Semolina's 33-high/31-low-bit
approximation.  At every short-loop prefix, the full-width signed numerator is
within `2^(n - 33 + t)` of the aligned approximate value.  Oddness of the
full-width second state transfers to the approximation; no claim is made that
the approximate comparison trace equals the full-width trace. -/
theorem semolina_prefix_error_of_odd {a b t : Nat} (hb : Odd b)
    (hlarge : 64 < max (bitLength a) (bitLength b)) :
    let n := max (bitLength a) (bitLength b)
    let ap := semolinaApprox a b
    let s := approxSteps t (ApproxState.initial ap.1 ap.2)
    (s.matrix.row0.apply a b - (2^(n - 64 + t) : Nat) * s.a).natAbs ≤
        2^(n - 33 + t) ∧
    (s.matrix.row1.apply a b - (2^(n - 64 + t) : Nat) * s.b).natAbs ≤
        2^(n - 33 + t) := by
  let n := max (bitLength a) (bitLength b)
  let ap := semolinaApprox a b
  let s := approxSteps t (ApproxState.initial ap.1 ap.2)
  have herr := approximate_error (k := 32) (a := a) (b := b) (by omega) hlarge
  have hapodd : Odd ap.2 := by simpa [ap] using semolinaApprox_snd_odd (a := a) hb
  have hprefix := approxSteps_error_bound (t := t) (approxA := ap.1) (approxB := ap.2)
    (realA := a) (realB := b) (scale := 2^(n - 64)) (err := 2^(n - 33))
    hapodd (by simpa [n, ap, semolinaApprox] using herr.1)
    (by simpa [n, ap, semolinaApprox] using herr.2)
  have hscale : (2^(n - 64 + t) : Int) = 2^(n - 64) * 2^t := by
    rw [pow_add]
  have herrscale : 2^(n - 33 + t) = 2^t * 2^(n - 33) := by
    rw [pow_add, Nat.mul_comm]
  change
    (s.matrix.row0.apply a b - (2^(n - 64 + t) : Nat) * s.a).natAbs ≤
        2^(n - 33 + t) ∧
    (s.matrix.row1.apply a b - (2^(n - 64 + t) : Nat) * s.b).natAbs ≤
        2^(n - 33 + t)
  rw [herrscale]
  push_cast [hscale]
  simpa [s, ap, Nat.mul_assoc] using hprefix

/-- If the approximate and signed full-width orders disagree at a prefix, the
full-width difference is bounded by twice the component approximation error.
This is the quantitative first-divergence bridge, stated for scaled numerators
so it does not rely on signed division semantics. -/
theorem opposite_order_difference_le {realA realB : Int} {approxA approxB scale err : Nat}
    (herrA : (realA - (scale : Int) * approxA).natAbs ≤ err)
    (herrB : (realB - (scale : Int) * approxB).natAbs ≤ err)
    (happrox : approxB ≤ approxA) (hreal : realA < realB) :
    (realA - realB).natAbs ≤ 2 * err := by
  have happroxInt : (approxB : Int) ≤ approxA := by exact_mod_cast happrox
  have happdiff : (0 : Int) ≤ (approxA : Int) - approxB := by omega
  have hscaled : (0 : Int) ≤ scale * ((approxA : Int) - approxB) :=
    mul_nonneg (by positivity) happdiff
  have hneg : realA - realB < 0 := by omega
  have hid : (scale : Int) * (approxA - approxB) - (realA - realB) =
      - (realA - scale * approxA) + (realB - scale * approxB) := by
    ring
  have htriangle :
      ((scale : Int) * (approxA - approxB) - (realA - realB)).natAbs ≤ 2 * err := by
    rw [hid]
    calc
      (- (realA - scale * approxA) + (realB - scale * approxB)).natAbs ≤
          (realA - scale * approxA).natAbs +
            (realB - scale * approxB).natAbs := by
              have hadd := Int.natAbs_add_le (-(realA - scale * approxA))
                (realB - scale * approxB)
              simpa only [Int.natAbs_neg] using hadd
      _ ≤ err + err := Nat.add_le_add herrA herrB
      _ = 2 * err := by omega
  have hdom : (realA - realB).natAbs ≤
      ((scale : Int) * (approxA - approxB) - (realA - realB)).natAbs := by
    have hnonpos : realA - realB ≤ 0 := hneg.le
    have hnonneg : 0 ≤ (scale : Int) * (approxA - approxB) - (realA - realB) := by omega
    have habsLeft : ((realA - realB).natAbs : Int) = -(realA - realB) :=
      Int.ofNat_natAbs_of_nonpos hnonpos
    have habsRight :
        ((((scale : Int) * (approxA - approxB) - (realA - realB)).natAbs : Nat) : Int) =
          (scale : Int) * (approxA - approxB) - (realA - realB) :=
      Int.ofNat_natAbs_of_nonneg hnonneg
    have hcast : ((realA - realB).natAbs : Int) ≤
        (((scale : Int) * (approxA - approxB) - (realA - realB)).natAbs : Int) := by
      rw [habsLeft, habsRight]
      omega
    exact_mod_cast hcast
  exact hdom.trans htriangle

/-- Symmetric first-divergence bridge when the approximation orders the second
component above the first while the signed real order is reversed. -/
theorem opposite_order_difference_le' {realA realB : Int} {approxA approxB scale err : Nat}
    (herrA : (realA - (scale : Int) * approxA).natAbs ≤ err)
    (herrB : (realB - (scale : Int) * approxB).natAbs ≤ err)
    (happrox : approxA < approxB) (hreal : realB ≤ realA) :
    (realB - realA).natAbs ≤ 2 * err := by
  have herrA' : (realB - (scale : Int) * approxB).natAbs ≤ err := herrB
  have herrB' : (realA - (scale : Int) * approxA).natAbs ≤ err := herrA
  by_cases heq : realA = realB
  · subst realA
    simp
  · have hstrict : realB < realA := by omega
    exact opposite_order_difference_le herrA' herrB' happrox.le hstrict

/-- On the subtract-without-swap branch, an opposite signed-real order puts the
new first numerator in the twice-error band. -/
theorem controlledStep_divergent_noswap {s : ControlledState} {scale err : Nat}
    (hodd : ¬ Even s.approxA)
    (happrox : s.approxB ≤ s.approxA)
    (hreal : s.scaledRealA < s.scaledRealB)
    (herrA : (s.scaledRealA - (scale : Int) * s.approxA).natAbs ≤ err)
    (herrB : (s.scaledRealB - (scale : Int) * s.approxB).natAbs ≤ err) :
    (controlledStep s).scaledRealA.natAbs ≤ 2 * err ∧
    (controlledStep s).scaledRealB = 2 * s.scaledRealB := by
  have hdiff := opposite_order_difference_le herrA herrB happrox hreal
  unfold controlledStep
  rw [if_neg hodd, if_pos happrox]
  exact ⟨hdiff, rfl⟩

/-- On the swap-subtract branch, an opposite signed-real order puts the new
first numerator in the twice-error band. -/
theorem controlledStep_divergent_swap {s : ControlledState} {scale err : Nat}
    (hodd : ¬ Even s.approxA)
    (happrox : s.approxA < s.approxB)
    (hreal : s.scaledRealB ≤ s.scaledRealA)
    (herrA : (s.scaledRealA - (scale : Int) * s.approxA).natAbs ≤ err)
    (herrB : (s.scaledRealB - (scale : Int) * s.approxB).natAbs ≤ err) :
    (controlledStep s).scaledRealA.natAbs ≤ 2 * err ∧
    (controlledStep s).scaledRealB = 2 * s.scaledRealA := by
  have hdiff := opposite_order_difference_le' herrA herrB happrox hreal
  unfold controlledStep
  rw [if_neg hodd, if_neg (Nat.not_le_of_gt happrox)]
  exact ⟨hdiff, rfl⟩

/-- The concrete Semolina 31-operation short loop. -/
def semolinaShort (a b : Nat) : ApproxState :=
  let ap := semolinaApprox a b
  approxSteps 31 (ApproxState.initial ap.1 ap.2)

/-- Although the short-loop control trace comes from the approximation, each
resulting row applied to the full-width inputs is exactly divisible by `2^31`.
This is the arithmetic contract required by the assembly's signed
multiply-and-shift update. -/
theorem semolinaShort_full_width_dvd (a b : Nat) (hb : Odd b) :
    (2^31 : Int) ∣ (semolinaShort a b).matrix.row0.apply a b ∧
    (2^31 : Int) ∣ (semolinaShort a b).matrix.row1.apply a b := by
  let ap := semolinaApprox a b
  have hapodd : Odd ap.2 := semolinaApprox_snd_odd hb
  have hrepr := approxSteps_initial_representation 31 ap.1 ap.2 hapodd
  have hx : Nat.ModEq (2^31) a ap.1 := by
    change a % 2^31 = ap.1 % 2^31
    simpa [ap, semolinaApprox] using (approximate_fst_mod 32 a b).symm
  have hy : Nat.ModEq (2^31) b ap.2 := by
    change b % 2^31 = ap.2 % 2^31
    simpa [ap, semolinaApprox] using (approximate_snd_mod 32 a b).symm
  have hrow0 := SignedRow.apply_modEq (semolinaShort a b).matrix.row0 hx hy
  have hrow1 := SignedRow.apply_modEq (semolinaShort a b).matrix.row1 hx hy
  have hdiv0 : (2^31 : Int) ∣ (semolinaShort a b).matrix.row0.apply ap.1 ap.2 := by
    refine ⟨(semolinaShort a b).a, ?_⟩
    simpa [semolinaShort, ap] using hrepr.1.symm
  have hdiv1 : (2^31 : Int) ∣ (semolinaShort a b).matrix.row1.apply ap.1 ap.2 := by
    refine ⟨(semolinaShort a b).b, ?_⟩
    simpa [semolinaShort, ap] using hrepr.2.symm
  constructor
  · exact Int.modEq_zero_iff_dvd.mp (hrow0.trans hdiv0.modEq_zero_int)
  · exact Int.modEq_zero_iff_dvd.mp (hrow1.trans hdiv1.modEq_zero_int)

/-- The sign correction used after a full-width row update: zero and positive
quotients keep their row, while negative quotients negate it. -/
def orient (q : Int) : Int := if q < 0 then -1 else 1

@[simp] theorem orient_mul_self (q : Int) : orient q * q = q.natAbs := by
  unfold orient
  split_ifs with h
  · rw [neg_one_mul]
    rcases Int.natAbs_eq q with hq | hq
    · omega
    · omega
  · rw [one_mul, Int.natAbs_of_nonneg (Int.not_lt.mp h)]

/-- Scale a signed row, used to model the update block's conditional negation. -/
def SignedRow.scale (c : Int) (r : SignedRow) : SignedRow :=
  ⟨c * r.left, c * r.right⟩

@[simp] theorem SignedRow.apply_scale (c : Int) (r : SignedRow) (x y : Int) :
    (SignedRow.scale c r).apply x y = c * r.apply x y := by
  simp [SignedRow.scale, SignedRow.apply]
  ring

@[simp] theorem SignedRow.norm_scale_orient (q : Int) (r : SignedRow) :
    (SignedRow.scale (orient q) r).norm = r.norm := by
  unfold orient
  split_ifs <;> simp [SignedRow.scale, SignedRow.norm]

/-- Full-width signed numerators produced by the approximation-controlled rows. -/
def semolinaNumerators (a b : Nat) : Int × Int :=
  let m := (semolinaShort a b).matrix
  (m.row0.apply a b, m.row1.apply a b)

/-- Exact signed quotients obtained by the assembly's 31-bit shift. -/
def semolinaQuotients (a b : Nat) : Int × Int :=
  let nums := semolinaNumerators a b
  (nums.1 / 2^31, nums.2 / 2^31)

/-- Nonnegative state after the assembly conditionally negates negative rows. -/
def semolinaBatchState (a b : Nat) : GCDState :=
  let q := semolinaQuotients a b
  ⟨q.1.natAbs, q.2.natAbs⟩

/-- Matrix after applying the same conditional row negations as the full-width
update block. -/
def semolinaBatchMatrix (a b : Nat) : SignedMatrix :=
  let q := semolinaQuotients a b
  let m := (semolinaShort a b).matrix
  ⟨SignedRow.scale (orient q.1) m.row0, SignedRow.scale (orient q.2) m.row1⟩

/-- One actual Semolina approximation batch, including exact signed division
and conditional absolute value, is a `ScaledTransition`. -/
theorem semolinaBatch_transition (a b : Nat) (hb : Odd b) :
    ScaledTransition 31 (semolinaBatchMatrix a b) ⟨a, b⟩ (semolinaBatchState a b) := by
  rcases semolinaShort_full_width_dvd a b hb with ⟨hdiv0, hdiv1⟩
  let nums := semolinaNumerators a b
  let q := semolinaQuotients a b
  have hq0 : q.1 * (2^31 : Int) = nums.1 := by
    exact Int.ediv_mul_cancel hdiv0
  have hq1 : q.2 * (2^31 : Int) = nums.2 := by
    exact Int.ediv_mul_cancel hdiv1
  constructor
  · simp only [semolinaBatchState, semolinaBatchMatrix, SignedRow.apply_scale]
    change (2^31 : Int) * q.1.natAbs = orient q.1 * nums.1
    rw [← hq0]
    calc
      (2^31 : Int) * q.1.natAbs = q.1.natAbs * 2^31 := by ring
      _ = (orient q.1 * q.1) * 2^31 := by rw [orient_mul_self]
      _ = orient q.1 * (q.1 * 2^31) := by ring
  · simp only [semolinaBatchState, semolinaBatchMatrix, SignedRow.apply_scale]
    change (2^31 : Int) * q.2.natAbs = orient q.2 * nums.2
    rw [← hq1]
    calc
      (2^31 : Int) * q.2.natAbs = q.2.natAbs * 2^31 := by ring
      _ = (orient q.2 * q.2) * 2^31 := by rw [orient_mul_self]
      _ = orient q.2 * (q.2 * 2^31) := by ring

/-- The concrete short-loop matrix has determinant magnitude `2^31`. -/
theorem semolinaShort_det_natAbs (a b : Nat) :
    (matrixDet (semolinaShort a b).matrix).natAbs = 2^31 := by
  unfold semolinaShort
  exact approxSteps_det_natAbs 31 _ _

/-- The concrete short-loop matrix has the row bound consumed by instruction
proofs of the packed 32-bit coefficient implementation. -/
theorem semolinaShort_matrix_bounded (a b : Nat) :
    (semolinaShort a b).matrix.Bounded (2^31) := by
  unfold semolinaShort
  exact approxSteps_matrix_bounded 31 _ _

/-- Conditional row negation preserves the short-loop coefficient bounds. -/
theorem semolinaBatch_matrix_bounded (a b : Nat) :
    (semolinaBatchMatrix a b).Bounded (2^31) := by
  rcases semolinaShort_matrix_bounded a b with ⟨hrow0, hrow1⟩
  constructor
  · change (SignedRow.scale (orient (semolinaQuotients a b).1)
        (semolinaShort a b).matrix.row0).norm ≤ 2^31
    rw [SignedRow.norm_scale_orient]
    exact hrow0
  · change (SignedRow.scale (orient (semolinaQuotients a b).2)
        (semolinaShort a b).matrix.row1).norm ≤ 2^31
    rw [SignedRow.norm_scale_orient]
    exact hrow1

end InversionConvergence
end PastaAsm
