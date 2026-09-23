/-
Copyright Supranational LLC (the routines, transcribed from Semolina v0.1.4).
Copyright (c) 2026 the pasta-asm contributors (the transcription and the proofs).
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.AArch64.Spec.Invert.Arithmetic
import PastaAsm.AArch64.Spec.Invert.Divsteps.Steps31
import PastaAsm.Spec.Invert.Batch

/-!
# Correctness of the AArch64 full-width GCD-state update

The block computes a signed row numerator and divides its absolute value by
`2^31`.  Its fixed-width negation has one genuine edge case: negating zero with
a negative coefficient bitpattern does not manufacture the missing carry above
the four input words.  The arithmetic theorem therefore states the exact
necessary reachability condition explicitly: when the first input is zero, its
selected coefficient is nonnegative.

The actual `semolinaShort` rows satisfy that condition.  If the first state is
zero, every short-loop operation takes the even branch; the first row remains
`(1, 0)` and the second row is doubled at every operation.
-/

set_option exponentiation.threshold 400

namespace PastaAsm.AArch64

open Spec.Invert Spec.Invert.Convergence

/-- Iterating the approximation loop from a zero first state preserves the
first row and doubles the second row at every operation. -/
theorem approxSteps_zero_first (n b : Nat) (row0 row1 : SignedRow) :
    approxSteps n ⟨0, b, ⟨row0, row1⟩⟩ =
      ⟨0, b, ⟨row0,
        ⟨(2^n : Nat) * row1.left, (2^n : Nat) * row1.right⟩⟩⟩ := by
  induction n generalizing b row0 row1 with
  | zero => simp [approxSteps]
  | succ n ih =>
      rw [approxSteps]
      have hstep : approxStep (⟨0, b, ⟨row0, row1⟩⟩ : ApproxState) =
          ⟨0, b, ⟨row0, row1.double⟩⟩ := by
        simp [approxStep]
      rw [hstep, ih]
      simp [SignedRow.double, pow_succ]
      constructor <;> ring

/-- Specialization to the identity rows used by `semolinaShort`. -/
theorem approxSteps_zero_first_rows (n b : Nat) :
    let state := approxSteps n (ApproxState.initial 0 b)
    state.a = 0 ∧ state.b = b ∧
      state.matrix.row0 = ⟨1, 0⟩ ∧ state.matrix.row1 = ⟨0, (2^n : Nat)⟩ := by
  rw [show ApproxState.initial 0 b = ⟨0, b, identityMatrix⟩ from rfl,
    show identityMatrix = ⟨⟨1, 0⟩, ⟨0, 1⟩⟩ from rfl,
    approxSteps_zero_first]
  simp

/-- The two actual short-loop rows in the zero-first case.  This is a raw
coefficient fact, stronger than the normalized quotient theorem. -/
theorem semolinaShort_zero_first_rows (b : Nat) :
    (semolinaShort 0 b).matrix.row0 = ⟨1, 0⟩ ∧
      (semolinaShort 0 b).matrix.row1 = ⟨0, (2^31 : Nat)⟩ := by
  have hzero := semolinaApprox_zero_first b
  have hrows := (approxSteps_zero_first_rows 31 (semolinaApprox 0 b).2).2.2
  simpa only [semolinaShort, hzero] using hrows

/-- In particular, either coefficient selected to multiply a zero first input
by an actual `semolinaShort` row is nonnegative. -/
theorem semolinaShort_zero_first_left_nonneg (b : Nat) (i : Fin 2) :
    0 ≤ (if i = 0 then (semolinaShort 0 b).matrix.row0
      else (semolinaShort 0 b).matrix.row1).left := by
  rcases semolinaShort_zero_first_rows b with ⟨hrow0, hrow1⟩
  fin_cases i <;> simp [hrow0, hrow1]

/-- Both actual `semolinaShort` rows satisfy the update helper's exceptional
zero-first premise. -/
theorem semolinaShort_left_nonneg_if_zero (a b : Nat) :
    (a = 0 → 0 ≤ (semolinaShort a b).matrix.row0.left) ∧
      (a = 0 → 0 ≤ (semolinaShort a b).matrix.row1.left) := by
  by_cases ha : a = 0
  · subst a
    rcases semolinaShort_zero_first_rows b with ⟨hrow0, hrow1⟩
    constructor <;> intro <;> simp [hrow0, hrow1]
  · exact ⟨fun h => (ha h).elim, fun h => (ha h).elim⟩

/-- The natural five-word value produced by the helper's signed-magnitude
preparation before its unsigned multiply.  The negative case contains the
four-word two's-complement operand and the signed fifth word. -/
def signedProductValue (value : Nat) (x : Int) : Nat :=
  if x < 0 then
    (2^256 - value) * x.natAbs + 2^256 * (2^64 - x.natAbs)
  else
    value * x.toNat

/-- The prepared five-word product is the canonical `2^320` representative of
`value * x`.  The explicit zero condition is necessary: if `value = 0` and
`x < 0`, four-word negation loses its carry and the helper instead prepares
`2^320 - 2^256 * |x|`. -/
theorem signedProductValue_exact (value : Nat) (x : Int)
    (hvalue : value < 2^256) (hx : x.natAbs < 2^63)
    (hzero : value = 0 → 0 ≤ x) :
    signedProductValue value x =
      if x < 0 then 2^320 - value * x.natAbs else value * x.toNat := by
  unfold signedProductValue
  by_cases hneg : x < 0
  · rw [if_pos hneg, if_pos hneg]
    have hvaluePos : 0 < value := by
      by_contra hnot
      have : value = 0 := Nat.eq_zero_of_not_pos hnot
      exact (not_le_of_gt hneg) (hzero this)
    have hvalueLe : value ≤ 2^256 := hvalue.le
    have hxLe : x.natAbs ≤ 2^64 := hx.le.trans (by norm_num)
    rw [Nat.sub_mul, Nat.mul_sub_left_distrib]
    have hleft : value * x.natAbs ≤ 2^256 * x.natAbs :=
      Nat.mul_le_mul_right x.natAbs hvalueLe
    have hright : 2^256 * x.natAbs ≤ 2^256 * 2^64 :=
      Nat.mul_le_mul_left (2^256) hxLe
    have hpow : 2^256 * 2^64 = 2^320 := by ring
    omega
  · rw [if_neg hneg, if_neg hneg]

/-- A bounded word representing a signed coefficient has its canonical
64-bit two's-complement value. -/
private theorem signedProductValue_modEq (value : Nat) (x : Int)
    (hvalue : value < 2^256) (hx : x.natAbs < 2^63)
    (hzero : value = 0 → 0 ≤ x) :
    (signedProductValue value x : Int) ≡ (value : Int) * x [ZMOD (2^320 : Nat)] := by
  have hexact := signedProductValue_exact value x hvalue hx hzero
  by_cases hneg : x < 0
  · rw [hexact, if_pos hneg]
    have hvaluePos : 0 < value := by
      by_contra hnot
      exact (not_le_of_gt hneg) (hzero (by omega))
    have habsPos : 0 < x.natAbs := Int.natAbs_pos.mpr hneg.ne
    have hprodLt : value * x.natAbs < 2^320 := by
      have hmul := Nat.mul_lt_mul'' hvalue hx
      norm_num at hmul ⊢
      exact hmul.trans (by norm_num)
    rw [Int.natCast_sub hprodLt.le]
    have hxEq : x = -(x.natAbs : Int) := by
      have habs := Int.ofNat_natAbs_of_nonpos (Int.le_of_lt hneg)
      omega
    have hxMul : (value : Int) * x = -((value * x.natAbs : Nat) : Int) := by
      calc
        (value : Int) * x = (value : Int) * (-(x.natAbs : Int)) := congrArg ((value : Int) * ·) hxEq
        _ = -((value * x.natAbs : Nat) : Int) := by push_cast; ring
    rw [hxMul, Int.modEq_iff_dvd]
    refine ⟨-1, ?_⟩
    push_cast
    ring
  · rw [hexact, if_neg hneg]
    have hnonneg : 0 ≤ x := Int.not_lt.mp hneg
    rw [Int.natCast_mul, Int.toNat_of_nonneg hnonneg]

private theorem wordRep_cases {w : Nat} {z : Int}
    (hw : w < 2^64) (hrep : WordRep w z) (hz : z.natAbs < 2^63) :
    (0 ≤ z ∧ w = z.toNat) ∨ (z < 0 ∧ w = 2^64 - z.natAbs) := by
  change (w : Int) ≡ z [ZMOD (2^64 : Nat)] at hrep
  have hrep' : z ≡ (w : Int) [ZMOD (2^64 : Nat)] := hrep.symm
  rw [Int.modEq_iff_dvd] at hrep'
  rcases hrep' with ⟨k, hk⟩
  by_cases hneg : z < 0
  · right
    refine ⟨hneg, ?_⟩
    have habs : (z.natAbs : Int) = -z :=
      Int.ofNat_natAbs_of_nonpos (Int.le_of_lt hneg)
    have habsLt : z.natAbs < 2^64 := hz.trans (by norm_num)
    have hw' : (w : Int) < 2^64 := by exact_mod_cast hw
    have habsLt' : (z.natAbs : Int) < 2^64 := by exact_mod_cast habsLt
    have habs0 : (0 : Int) < z.natAbs := by
      exact_mod_cast (Int.natAbs_pos.mpr hneg.ne)
    have hkOne : k = 1 := by
      norm_num at hk
      omega
    norm_num at hk
    have heq : (w : Int) = (2^64 : Int) - z.natAbs := by omega
    omega
  · left
    have hnonneg : 0 ≤ z := Int.not_lt.mp hneg
    refine ⟨hnonneg, ?_⟩
    have hto : (z.toNat : Int) = z := Int.toNat_of_nonneg hnonneg
    have htoLt : z.toNat < 2^63 := by
      rw [← Int.natAbs_of_nonneg hnonneg]
      exact hz
    have hw' : (w : Int) < 2^64 := by exact_mod_cast hw
    have htoLt' : (z.toNat : Int) < 2^63 := by exact_mod_cast htoLt
    have hkZero : k = 0 := by
      norm_num at hk
      omega
    norm_num at hk
    have heq : (w : Int) = z.toNat := by omega
    exact_mod_cast heq

private theorem fiveWord_cases {value : Nat} {z : Int}
    (hvalue : value < 2^320)
    (hrep : (value : Int) ≡ z [ZMOD (2^320 : Nat)])
    (hz : z.natAbs < 2^287) :
    (0 ≤ z ∧ value = z.toNat) ∨
      (z < 0 ∧ value = 2^320 - z.natAbs) := by
  rw [Int.modEq_iff_dvd] at hrep
  rcases hrep with ⟨k, hk⟩
  by_cases hneg : z < 0
  · right
    refine ⟨hneg, ?_⟩
    have habs : (z.natAbs : Int) = -z :=
      Int.ofNat_natAbs_of_nonpos (Int.le_of_lt hneg)
    have habsLt : z.natAbs < 2^320 := hz.trans (by norm_num)
    have habsPos : 0 < z.natAbs := Int.natAbs_pos.mpr hneg.ne
    norm_num at hk
    have hkNeg : k < 0 := by
      have hvalueNonneg : (0 : Int) ≤ value := by positivity
      have hleftNeg : z - (value : Int) < 0 := by omega
      rw [hk] at hleftNeg
      by_contra hnot
      have hkNonneg : 0 ≤ k := le_of_not_gt hnot
      have hmulNonneg : 0 ≤ (2^320 : Int) * k := mul_nonneg (by positivity) hkNonneg
      exact (not_lt_of_ge hmulNonneg hleftNeg).elim
    have hkGtNegTwo : (-2 : Int) < k := by
      by_contra hnot
      have hkle : k ≤ -2 := le_of_not_gt hnot
      have hmulLe : (2^320 : Int) * k ≤ 2^320 * (-2) :=
        mul_le_mul_of_nonneg_left hkle (by positivity)
      have hvalueInt : (value : Int) < 2^320 := by exact_mod_cast hvalue
      have habsInt : (z.natAbs : Int) < 2^320 := by exact_mod_cast habsLt
      omega
    have hkNegOne : k = -1 := by omega
    omega
  · left
    have hnonneg : 0 ≤ z := Int.not_lt.mp hneg
    refine ⟨hnonneg, ?_⟩
    have hto : (z.toNat : Int) = z := Int.toNat_of_nonneg hnonneg
    have htoLt : z.toNat < 2^320 := by
      rw [← Int.natAbs_of_nonneg hnonneg]
      exact hz.trans (by norm_num)
    norm_num at hk
    have hkZero : k = 0 := by omega
    omega

private theorem add_mul_pow_div_31 (lo hi : Nat) :
    (lo + 2^64 * hi) / 2^31 = lo / 2^31 + 2^33 * hi := by
  have hfactor : 2^64 * hi = 2^31 * (2^33 * hi) := by ring
  rw [hfactor, Nat.add_mul_div_left _ _ (by positivity)]

private theorem extr31_eq {lo hi : Nat} (hlo : lo < 2^64) :
    extr hi lo 31 = lo / 2^31 + 2^33 * (hi % 2^31) := by
  unfold extr lsr lsl
  norm_num only [Nat.reducePow, Nat.reduceMod, Nat.reduceLeDiff]
  have hmul : hi * 8589934592 % 18446744073709551616 =
      8589934592 * (hi % 2147483648) := by
    have hsplit := Nat.mod_add_div hi 2147483648
    rw [show hi = hi % 2147483648 + 2147483648 * (hi / 2147483648) by omega]
    rw [show (hi % 2147483648 + 2147483648 * (hi / 2147483648)) * 8589934592 =
      8589934592 * (hi % 2147483648) +
        18446744073709551616 * (hi / 2147483648) by ring]
    rw [hsplit, Nat.mul_comm 18446744073709551616, Nat.add_mul_mod_self_right]
    apply Nat.mod_eq_of_lt
    have hr := Nat.mod_lt hi (by norm_num : 0 < 2147483648)
    omega
  rw [hmul]
  apply word_eq_of_lt
  have hloDiv : lo / 2147483648 < 8589934592 := by
    apply Nat.div_lt_of_lt_mul
    norm_num
    simpa only [Nat.reducePow] using hlo
  have hr := Nat.mod_lt hi (by norm_num : 0 < 2147483648)
  have hloDivLe : lo / 2147483648 ≤ 8589934591 := by omega
  have hrLe : hi % 2147483648 ≤ 2147483647 := by omega
  calc
    lo / 2147483648 + 8589934592 * (hi % 2147483648)
        ≤ 8589934591 + 8589934592 * 2147483647 := by gcongr
    _ < regMod := by norm_num [regMod]

private theorem extrChain31 (w0 w1 w2 w3 w4 : Nat)
    (h0 : w0 < 2^64) (h1 : w1 < 2^64) (h2 : w2 < 2^64)
    (h3 : w3 < 2^64) :
    extr w1 w0 31 + 2^64 * extr w2 w1 31 +
        2^128 * extr w3 w2 31 + 2^192 * extr w4 w3 31 +
        2^256 * (w4 / 2^31) =
      (w0 + 2^64 * w1 + 2^128 * w2 + 2^192 * w3 + 2^256 * w4) / 2^31 := by
  rw [extr31_eq h0, extr31_eq h1, extr31_eq h2, extr31_eq h3]
  have h1' := Nat.mod_add_div w1 (2^31)
  have h2' := Nat.mod_add_div w2 (2^31)
  have h3' := Nat.mod_add_div w3 (2^31)
  have h4' := Nat.mod_add_div w4 (2^31)
  rw [show w0 + 2^64 * w1 + 2^128 * w2 + 2^192 * w3 + 2^256 * w4 =
    w0 + 2^64 * (w1 + 2^64 * (w2 + 2^64 * (w3 + 2^64 * w4))) by ring]
  rw [add_mul_pow_div_31]
  clear * - h1' h2' h3' h4'
  omega

private theorem asr63_of_low {w : Nat} (hw : w < 2^63) : asr w 63 = 0 := by
  unfold asr
  rw [word_eq_of_lt (hw.trans (by norm_num))]
  dsimp only
  rw [if_pos hw, Nat.div_eq_of_lt hw]

private theorem asr63_of_high {w : Nat} (hw : w < 2^64) (hhigh : 2^63 ≤ w) :
    asr w 63 = 2^64 - 1 := by
  unfold asr
  rw [word_eq_of_lt hw, if_neg (by omega)]
  have hdiv : w / 2^63 = 1 := by omega
  rw [hdiv]
  norm_num [word, regMod]

/-- Arithmetic shift by 63 exposes the sign mask of a canonical signed word. -/
private theorem asr63_of_wordRep {w : Nat} {z : Int}
    (hw : w < 2^64) (hrep : WordRep w z) (hz : z.natAbs < 2^63) :
    asr w 63 = if z < 0 then 2^64 - 1 else 0 := by
  rcases wordRep_cases hw hrep hz with ⟨hzNonneg, hword⟩ | ⟨hzNeg, hword⟩
  · rw [if_neg (not_lt.mpr hzNonneg), hword]
    apply asr63_of_low
    rw [← Int.natAbs_of_nonneg hzNonneg]
    exact hz
  · rw [if_pos hzNeg, hword]
    apply asr63_of_high
    · have habsPos : 0 < z.natAbs := Int.natAbs_pos.mpr hzNeg.ne
      omega
    · omega

private theorem natXor_allOnes {w : Nat} (hw : w < 2^64) :
    w ^^^ (2^64 - 1) = 2^64 - 1 - w := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one]
  rw [Nat.sub_sub, Nat.add_comm 1 w, Nat.testBit_two_pow_sub_succ hw]
  by_cases hi : i < 64
  · simp [hi]
  · have hpow : 2^64 ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    have hwi : w < 2^i := lt_of_lt_of_le hw hpow
    rw [Nat.testBit_lt_two_pow hwi]
    simp [hi]

private theorem eor_allOnes {w : Nat} (hw : w < 2^64) :
    eor w (2^64 - 1) = 2^64 - 1 - w := by
  unfold eor
  rw [natXor_allOnes hw]
  exact word_eq_of_lt (by norm_num [regMod]; omega)

private theorem eor_zero {w : Nat} (hw : w < 2^64) : eor w 0 = w := by
  unfold eor
  rw [Nat.xor_zero]
  exact word_eq_of_lt hw

/-- The block's final mask-based conditional negation applies the numerator
orientation to a represented coefficient. -/
private theorem wordRep_orient {w mask out : Nat} {x z : Int}
    (hw : w < 2^64) (hx : WordRep w x)
    (hmask : mask = if z < 0 then 2^64 - 1 else 0)
    (hout : out = sub (eor w mask) mask) :
    WordRep out (orient z * x) := by
  unfold orient
  by_cases hz : z < 0
  · rw [if_pos hz] at hmask ⊢
    subst mask
    rw [hout]
    have hmaskBound : 2^64 - 1 < 2^64 := by omega
    have hmaskRep : WordRep (2^64 - 1) (-1) := by
      change ((2^64 - 1 : Nat) : Int) ≡ -1 [ZMOD (2^64 : Nat)]
      norm_num [Int.ModEq]
    have heorBound : eor w (2^64 - 1) < 2^64 := eor_lt _ _
    have heorRep : WordRep (eor w (2^64 - 1)) (-1 - x) := by
      rw [eor_allOnes hw]
      have hvalueRep : WordRep (2^64 - 1 - w) ((2^64 - 1 - w : Nat) : Int) := Int.ModEq.rfl
      have htarget : ((2^64 - 1 - w : Nat) : Int) ≡ -1 - x [ZMOD (2^64 : Nat)] := by
        have hbase : ((2^64 - 1 - w : Nat) : Int) = (2^64 - 1 : Int) - w := by
          rw [Int.natCast_sub (by omega)]
          norm_num
        rw [hbase]
        exact hmaskRep.sub hx
      exact hvalueRep.trans htarget
    have hsub := wordRep_sub heorBound hmaskBound heorRep hmaskRep
    convert hsub using 1
    ring
  · rw [if_neg hz] at hmask ⊢
    subst mask
    rw [hout, eor_zero hw]
    have hzero : WordRep 0 0 := wordRep_zero
    simpa using wordRep_sub hw (by decide : 0 < 2^64) hx hzero

private theorem signedMagnitude_exact {w : Nat} {z : Int}
    (hw : w < 2^64) (hrep : WordRep w z) (hz : z.natAbs < 2^63) :
    sub (eor w (asr w 63)) (asr w 63) = z.natAbs := by
  have hmask := asr63_of_wordRep hw hrep hz
  rcases wordRep_cases hw hrep hz with ⟨hzNonneg, hword⟩ | ⟨hzNeg, hword⟩
  · rw [hmask, if_neg (not_lt.mpr hzNonneg), eor_zero hw, hword]
    have habs : z.natAbs = z.toNat := by
      have h1 : (z.natAbs : Int) = z := Int.natAbs_of_nonneg hzNonneg
      have h2 : (z.toNat : Int) = z := Int.toNat_of_nonneg hzNonneg
      exact_mod_cast h1.trans h2.symm
    rw [habs]
    unfold sub subc
    norm_num only [Nat.reducePow, Nat.reduceSubDiff, Nat.sub_zero, Nat.add_zero]
    have htoLt : z.toNat < 18446744073709551616 := by
      rw [← habs]
      exact hz.trans (by norm_num)
    have hmod : z.toNat % 18446744073709551616 = z.toNat :=
      Nat.mod_eq_of_lt htoLt
    omega
  · rw [hmask, if_pos hzNeg, hword, eor_allOnes (by omega)]
    have habsPos : 0 < z.natAbs := Int.natAbs_pos.mpr hzNeg.ne
    have habsLt : z.natAbs < 2^64 := hz.trans (by norm_num)
    have heor : 2^64 - 1 - (2^64 - z.natAbs) = z.natAbs - 1 := by omega
    rw [heor]
    unfold sub subc
    norm_num only [Nat.reducePow, Nat.reduceSubDiff]
    have harg : z.natAbs - 1 + 18446744073709551616 - 18446744073709551615 - 0 =
        z.natAbs := by omega
    rw [harg]
    exact Nat.mod_eq_of_lt (by simpa only [Nat.reducePow] using habsLt)

private theorem bitAnd_allOnes_left {w : Nat} (hw : w < 2^64) :
    bitAnd (2^64 - 1) w = w := by
  rw [show bitAnd (2^64 - 1) w = bitAnd w (2^64 - 1) by
    simp only [bitAnd, Nat.and_comm]]
  exact and_allOnes w hw

private theorem neg_eq_complement {w : Nat} (hpos : 0 < w) (hw : w < 2^64) :
    neg w = 2^64 - w := by
  unfold neg sub subc
  norm_num only [Nat.reducePow, Nat.reduceSubDiff, Nat.zero_add]
  have harg : 18446744073709551616 - w - 0 = 18446744073709551616 - w := by omega
  rw [harg, Nat.mod_eq_of_lt (by omega)]

private theorem complementFour_eq (q0 q1 q2 q3 : Nat)
    (h0 : q0 < 2^64) (h1 : q1 < 2^64)
    (h2 : q2 < 2^64) (h3 : q3 < 2^64) :
    eor q0 (2^64 - 1) + 2^64 * eor q1 (2^64 - 1) +
        2^128 * eor q2 (2^64 - 1) + 2^192 * eor q3 (2^64 - 1) + 1 +
      (q0 + 2^64 * q1 + 2^128 * q2 + 2^192 * q3) = 2^256 := by
  rw [eor_allOnes h0, eor_allOnes h1, eor_allOnes h2, eor_allOnes h3]
  omega

private theorem fourWordCarryChain_exact
    (i0 i1 i2 i3 o0 o1 o2 o3 c0 c1 c2 k carry target : Nat)
    (h0 : o0 + 2^64 * c0 = i0 + carry)
    (h1 : o1 + 2^64 * c1 = i1 + c0)
    (h2 : o2 + 2^64 * c2 = i2 + c1)
    (h3 : o3 + 2^64 * k = i3 + c2)
    (hinput : i0 + 2^64 * i1 + 2^128 * i2 + 2^192 * i3 + carry = target)
    (htarget : target < 2^256) :
    o0 + 2^64 * o1 + 2^128 * o2 + 2^192 * o3 = target ∧ k = 0 := by
  have hchain :
      o0 + 2^64 * o1 + 2^128 * o2 + 2^192 * o3 + 2^256 * k =
        i0 + 2^64 * i1 + 2^128 * i2 + 2^192 * i3 + carry := by
    clear * - h0 h1 h2 h3
    omega
  clear * - hchain hinput htarget
  omega

private theorem fiveWordShiftAbs
    (w0 w1 w2 w3 w4 : Nat) (z : Int)
    (h0 : w0 < 2^64) (h1 : w1 < 2^64) (h2 : w2 < 2^64)
    (h3 : w3 < 2^64) (h4 : w4 < 2^64)
    (hcases : (0 ≤ z ∧ w0 + 2^64 * w1 + 2^128 * w2 + 2^192 * w3 + 2^256 * w4 = z.toNat) ∨
      (z < 0 ∧ w0 + 2^64 * w1 + 2^128 * w2 + 2^192 * w3 + 2^256 * w4 =
        2^320 - z.natAbs))
    (hz : z.natAbs < 2^287) (hdiv : (2^31 : Int) ∣ z) :
    let shifted := extr w1 w0 31 + 2^64 * extr w2 w1 31 +
      2^128 * extr w3 w2 31 + 2^192 * extr w4 w3 31
    (asr w4 63 = if z < 0 then 2^64 - 1 else 0) ∧
      (if z < 0 then 2^256 - shifted else shifted) = z.natAbs / 2^31 := by
  dsimp only
  have hshift := extrChain31 w0 w1 w2 w3 w4 h0 h1 h2 h3
  rcases hcases with ⟨hnonneg, hvalue⟩ | ⟨hneg, hvalue⟩
  · have htopLow : w4 < 2^31 := by
      have htoLt : z.toNat < 2^287 := by
        rw [← Int.natAbs_of_nonneg hnonneg]
        exact hz
      clear * - hvalue htoLt
      omega
    have hmask : asr w4 63 = 0 := asr63_of_low (htopLow.trans (by norm_num))
    have habsEq : z.natAbs = z.toNat := by
      have h1 : (z.natAbs : Int) = z := Int.natAbs_of_nonneg hnonneg
      have h2 : (z.toNat : Int) = z := Int.toNat_of_nonneg hnonneg
      exact_mod_cast h1.trans h2.symm
    refine ⟨by simpa only [if_neg (not_lt.mpr hnonneg)] using hmask, ?_⟩
    simp only [if_neg (not_lt.mpr hnonneg)]
    have hshift' := hshift
    rw [Nat.div_eq_of_lt htopLow, Nat.mul_zero, add_zero, hvalue] at hshift'
    exact hshift'.trans (congrArg (· / 2^31) habsEq.symm)
  · have hvalueLower : 2^320 - 2^287 ≤
        w0 + 2^64 * w1 + 2^128 * w2 + 2^192 * w3 + 2^256 * w4 := by
      rw [hvalue]
      exact Nat.sub_le_sub_left hz.le _
    have hmask : asr w4 63 = 2^64 - 1 := by
      apply asr63_of_high h4
      clear * - hvalueLower h0 h1 h2 h3
      omega
    obtain ⟨m, habsMul⟩ : ∃ m : Nat, z.natAbs = 2^31 * m := by
      rcases hdiv with ⟨k, hk⟩
      refine ⟨k.natAbs, ?_⟩
      rw [hk, Int.natAbs_mul]
      norm_num
    have hmLt : m < 2^256 := by
      rw [habsMul] at hz
      have hpow : 2^287 = 2^31 * 2^256 := by ring
      rw [hpow] at hz
      exact (Nat.mul_lt_mul_left (by positivity)).mp hz
    have htotalFactor : 2^320 - z.natAbs = 2^31 * (2^289 - m) := by
      rw [habsMul]
      have hp : 2^320 = 2^31 * 2^289 := by ring
      rw [hp, Nat.mul_sub_left_distrib]
    have htotalDiv :
        (w0 + 2^64 * w1 + 2^128 * w2 + 2^192 * w3 + 2^256 * w4) / 2^31 =
          2^289 - m := by
      rw [hvalue, htotalFactor, Nat.mul_comm, Nat.mul_div_left]
      positivity
    have htopDiv : w4 / 2^31 = 2^33 - 1 := by
      have htopLower : 2^64 - 2^31 ≤ w4 := by
        clear * - hvalueLower h0 h1 h2 h3
        omega
      have hlowerDiv := Nat.div_le_div_right (c := 2^31) htopLower
      have hupperDiv : w4 / 2^31 < 2^33 := by
        apply Nat.div_lt_of_lt_mul
        have hp : 2^31 * 2^33 = 2^64 := by ring
        rw [hp]
        exact h4
      norm_num at hlowerDiv ⊢
      omega
    have hlowShift :
        extr w1 w0 31 + 2^64 * extr w2 w1 31 +
          2^128 * extr w3 w2 31 + 2^192 * extr w4 w3 31 = 2^256 - m := by
      rw [htopDiv] at hshift
      clear * - htotalDiv hshift
      omega
    have hquot : z.natAbs / 2^31 = m := by
      rw [habsMul, Nat.mul_comm, Nat.mul_div_left]
      positivity
    refine ⟨by simpa only [if_pos hneg] using hmask, ?_⟩
    simp only [if_pos hneg, hlowShift, hquot]
    omega

-- BEGIN updateAB statement
/-- The AArch64 `updateAB` block returns the unique nonnegative quotient of the
signed row numerator by `2^31`, and applies the same numerator orientation to
both row coefficients.  The two additional hypotheses are exactly the
reachable zero-edge facts required by the block's four-word conditional
negations. -/
theorem updateAB_exact
    (a b : Limbs) (f g : Nat) (x y : Int)
    (ha : a.Bounded) (hb : b.Bounded)
    (hf : f < 2^64) (hg : g < 2^64)
    (hfx : WordRep f x) (hgy : WordRep g y)
    (hx : x.natAbs < 2^63) (hy : y.natAbs < 2^63)
    (hzeroA : a.toNat = 0 → 0 ≤ x) (hbPos : 0 < b.toNat)
    (hnumerator : (x * (a.toNat : Int) + y * (b.toNat : Int)).natAbs < 2^287)
    (hdiv : (2^31 : Int) ∣ x * (a.toNat : Int) + y * (b.toNat : Int)) :
    ∀ r, r = updateAB a b f g →
      r.value.Bounded ∧
        r.value.toNat = (x * (a.toNat : Int) + y * (b.toNat : Int)).natAbs / 2^31 ∧
        WordRep r.f (orient (x * (a.toNat : Int) + y * (b.toNat : Int)) * x) ∧
        WordRep r.g (orient (x * (a.toNat : Int) + y * (b.toNat : Int)) * y) := by
  intro r hr
-- END updateAB statement
  -- generated skeleton for `updateAB`: do not edit between the annotations
  unfold updateAB at hr
  lift_lets -merge at hr
  -- a0: argument
  extract_lets -merge +onlyGivenNames a0 at hr
  have e_a0 : a0 = a.l0 := rfl
  clear_value a0
  have b_a0 : a0 < 2^64 := by rw [e_a0]; exact ha.1
  -- a1: argument
  extract_lets -merge +onlyGivenNames a1 at hr
  have e_a1 : a1 = a.l1 := rfl
  clear_value a1
  have b_a1 : a1 < 2^64 := by rw [e_a1]; exact ha.2.1
  -- a2: argument
  extract_lets -merge +onlyGivenNames a2 at hr
  have e_a2 : a2 = a.l2 := rfl
  clear_value a2
  have b_a2 : a2 < 2^64 := by rw [e_a2]; exact ha.2.2.1
  -- a3: argument
  extract_lets -merge +onlyGivenNames a3 at hr
  have e_a3 : a3 = a.l3 := rfl
  clear_value a3
  have b_a3 : a3 < 2^64 := by rw [e_a3]; exact ha.2.2.2
  -- b0: argument
  extract_lets -merge +onlyGivenNames b0 at hr
  have e_b0 : b0 = b.l0 := rfl
  clear_value b0
  have b_b0 : b0 < 2^64 := by rw [e_b0]; exact hb.1
  -- b1: argument
  extract_lets -merge +onlyGivenNames b1 at hr
  have e_b1 : b1 = b.l1 := rfl
  clear_value b1
  have b_b1 : b1 < 2^64 := by rw [e_b1]; exact hb.2.1
  -- b2: argument
  extract_lets -merge +onlyGivenNames b2 at hr
  have e_b2 : b2 = b.l2 := rfl
  clear_value b2
  have b_b2 : b2 < 2^64 := by rw [e_b2]; exact hb.2.2.1
  -- b3: argument
  extract_lets -merge +onlyGivenNames b3 at hr
  have e_b3 : b3 = b.l3 := rfl
  clear_value b3
  have b_b3 : b3 < 2^64 := by rw [e_b3]; exact hb.2.2.2
  -- f': argument
  extract_lets -merge +onlyGivenNames f' at hr
  have e_f' : f' = f := rfl
  clear_value f'
  have b_f' : f' < 2^64 := by rw [e_f']; exact hf
  -- g': argument
  extract_lets -merge +onlyGivenNames g' at hr
  have e_g' : g' = g := rfl
  clear_value g'
  have b_g' : g' < 2^64 := by rw [e_g']; exact hg
  -- t5: asr t5,f,#63
  extract_lets -merge +onlyGivenNames t5 at hr
  have e_t5 : t5 = asr f' 63 := rfl
  clear_value t5
  have b_t5 : t5 < 2^64 := by rw [e_t5]; exact asr_lt _ _
  -- t6: eor t6,f,t5
  extract_lets -merge +onlyGivenNames t6 at hr
  have e_t6 : t6 = eor f' t5 := rfl
  clear_value t6
  have b_t6 : t6 < 2^64 := by rw [e_t6]; exact eor_lt _ _
  -- a0_1: eor a0,a0,t5
  extract_lets -merge +onlyGivenNames a0_1 at hr
  have e_a0_1 : a0_1 = eor a0 t5 := rfl
  clear_value a0_1
  have b_a0_1 : a0_1 < 2^64 := by rw [e_a0_1]; exact eor_lt _ _
  -- t6_1: sub t6,t6,t5
  extract_lets -merge +onlyGivenNames t6_1 at hr
  have e_t6_1 : t6_1 = sub t6 t5 := rfl
  clear_value t6_1
  have b_t6_1 : t6_1 < 2^64 := by rw [e_t6_1]; exact sub_lt _ _
  -- a1_1: eor a1,a1,t5
  extract_lets -merge +onlyGivenNames a1_1 at hr
  have e_a1_1 : a1_1 = eor a1 t5 := rfl
  clear_value a1_1
  have b_a1_1 : a1_1 < 2^64 := by rw [e_a1_1]; exact eor_lt _ _
  -- a0_2: adds a0,a0,t5,lsr #63
  extract_lets -merge +onlyGivenNames s a0_2 c at hr
  have e_a0_2 : a0_2 = (a0_1 + (lsr t5 63) + 0) % 2^64 := rfl
  have e_c : c = (a0_1 + (lsr t5 63) + 0) / 2^64 := rfl
  clear_value s a0_2 c
  have l_a0_2 : a0_2 + 2^64 * c = a0_1 + (lsr t5 63) + 0 := by
    rw [e_a0_2, e_c]; exact Nat.mod_add_div _ _
  have b_a0_2 : a0_2 < 2^64 := by rw [e_a0_2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c : c ≤ 1 := by
    rw [e_c]; exact addc_carry_le_one a0_1 (lsr t5 63) 0 b_a0_1 (lt_of_le_of_lt (Nat.div_le_self _ _) b_t5) (by decide)
  clear e_a0_2 e_c
  -- a2_1: eor a2,a2,t5
  extract_lets -merge +onlyGivenNames a2_1 at hr
  have e_a2_1 : a2_1 = eor a2 t5 := rfl
  clear_value a2_1
  have b_a2_1 : a2_1 < 2^64 := by rw [e_a2_1]; exact eor_lt _ _
  -- a1_2: adcs a1,a1,xzr
  extract_lets -merge +onlyGivenNames s_1 a1_2 c_1 at hr
  have e_a1_2 : a1_2 = (a1_1 + 0 + c) % 2^64 := rfl
  have e_c_1 : c_1 = (a1_1 + 0 + c) / 2^64 := rfl
  clear_value s_1 a1_2 c_1
  have l_a1_2 : a1_2 + 2^64 * c_1 = a1_1 + 0 + c := by
    rw [e_a1_2, e_c_1]; exact Nat.mod_add_div _ _
  have b_a1_2 : a1_2 < 2^64 := by rw [e_a1_2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_1 : c_1 ≤ 1 := by
    rw [e_c_1]; exact addc_carry_le_one a1_1 0 c b_a1_1 (by decide) b_c
  clear e_a1_2 e_c_1
  -- a3_1: eor a3,a3,t5
  extract_lets -merge +onlyGivenNames a3_1 at hr
  have e_a3_1 : a3_1 = eor a3 t5 := rfl
  clear_value a3_1
  have b_a3_1 : a3_1 < 2^64 := by rw [e_a3_1]; exact eor_lt _ _
  -- t0: umulh t0,a0,t6
  extract_lets -merge +onlyGivenNames t0 at hr
  have e_t0 : t0 = a0_2 * t6_1 / 2^64 := rfl
  clear_value t0
  have p_t0 : a0_2 * t6_1 < 2^64 * 2^64 := Nat.mul_lt_mul'' b_a0_2 b_t6_1
  have b_t0 : t0 < 2^64 := by rw [e_t0]; exact Nat.div_lt_of_lt_mul p_t0
  obtain ⟨lo_t0, b_lo_t0, d_t0⟩ :
      ∃ lo, lo < 2^64 ∧ lo + 2^64 * t0 = a0_2 * t6_1 :=
    ⟨a0_2 * t6_1 % 2^64, Nat.mod_lt _ (Nat.two_pow_pos _),
      by rw [e_t0]; exact Nat.mod_add_div _ _⟩
  clear e_t0
  -- a2_2: adcs a2,a2,xzr
  extract_lets -merge +onlyGivenNames s_2 a2_2 c_2 at hr
  have e_a2_2 : a2_2 = (a2_1 + 0 + c_1) % 2^64 := rfl
  have e_c_2 : c_2 = (a2_1 + 0 + c_1) / 2^64 := rfl
  clear_value s_2 a2_2 c_2
  have l_a2_2 : a2_2 + 2^64 * c_2 = a2_1 + 0 + c_1 := by
    rw [e_a2_2, e_c_2]; exact Nat.mod_add_div _ _
  have b_a2_2 : a2_2 < 2^64 := by rw [e_a2_2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_2 : c_2 ≤ 1 := by
    rw [e_c_2]; exact addc_carry_le_one a2_1 0 c_1 b_a2_1 (by decide) b_c_1
  clear e_a2_2 e_c_2
  -- t1: umulh t1,a1,t6
  extract_lets -merge +onlyGivenNames t1 at hr
  have e_t1 : t1 = a1_2 * t6_1 / 2^64 := rfl
  clear_value t1
  have p_t1 : a1_2 * t6_1 < 2^64 * 2^64 := Nat.mul_lt_mul'' b_a1_2 b_t6_1
  have b_t1 : t1 < 2^64 := by rw [e_t1]; exact Nat.div_lt_of_lt_mul p_t1
  obtain ⟨lo_t1, b_lo_t1, d_t1⟩ :
      ∃ lo, lo < 2^64 ∧ lo + 2^64 * t1 = a1_2 * t6_1 :=
    ⟨a1_2 * t6_1 % 2^64, Nat.mod_lt _ (Nat.two_pow_pos _),
      by rw [e_t1]; exact Nat.mod_add_div _ _⟩
  clear e_t1
  -- a3_2: adc a3,a3,xzr
  extract_lets -merge +onlyGivenNames a3_2 at hr
  have e_a3_2 : a3_2 = (a3_1 + 0 + c_2) % 2^64 := rfl
  clear_value a3_2
  have b_a3_2 : a3_2 < 2^64 := by rw [e_a3_2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨k_a3_2, b_k_a3_2, l_a3_2⟩ :
      ∃ k, k ≤ 1 ∧ a3_2 + 2^64 * k = a3_1 + 0 + c_2 :=
    ⟨(a3_1 + 0 + c_2) / 2^64, addc_carry_le_one a3_1 0 c_2 b_a3_1 (by decide) b_c_2,
      by rw [e_a3_2]; exact Nat.mod_add_div _ _⟩
  clear e_a3_2
  -- t2: umulh t2,a2,t6
  extract_lets -merge +onlyGivenNames t2 at hr
  have e_t2 : t2 = a2_2 * t6_1 / 2^64 := rfl
  clear_value t2
  have p_t2 : a2_2 * t6_1 < 2^64 * 2^64 := Nat.mul_lt_mul'' b_a2_2 b_t6_1
  have b_t2 : t2 < 2^64 := by rw [e_t2]; exact Nat.div_lt_of_lt_mul p_t2
  obtain ⟨lo_t2, b_lo_t2, d_t2⟩ :
      ∃ lo, lo < 2^64 ∧ lo + 2^64 * t2 = a2_2 * t6_1 :=
    ⟨a2_2 * t6_1 % 2^64, Nat.mod_lt _ (Nat.two_pow_pos _),
      by rw [e_t2]; exact Nat.mod_add_div _ _⟩
  clear e_t2
  -- t5_1: and t5,t5,t6
  extract_lets -merge +onlyGivenNames t5_1 at hr
  have e_t5_1 : t5_1 = bitAnd t5 t6_1 := rfl
  clear_value t5_1
  have b_t5_1 : t5_1 < 2^64 := by rw [e_t5_1]; exact bitAnd_lt _ _
  -- t3: umulh t3,a3,t6
  extract_lets -merge +onlyGivenNames t3 at hr
  have e_t3 : t3 = a3_2 * t6_1 / 2^64 := rfl
  clear_value t3
  have p_t3 : a3_2 * t6_1 < 2^64 * 2^64 := Nat.mul_lt_mul'' b_a3_2 b_t6_1
  have b_t3 : t3 < 2^64 := by rw [e_t3]; exact Nat.div_lt_of_lt_mul p_t3
  obtain ⟨lo_t3, b_lo_t3, d_t3⟩ :
      ∃ lo, lo < 2^64 ∧ lo + 2^64 * t3 = a3_2 * t6_1 :=
    ⟨a3_2 * t6_1 % 2^64, Nat.mod_lt _ (Nat.two_pow_pos _),
      by rw [e_t3]; exact Nat.mod_add_div _ _⟩
  clear e_t3
  -- t5_2: neg t5,t5
  extract_lets -merge +onlyGivenNames t5_2 at hr
  have e_t5_2 : t5_2 = neg t5_1 := rfl
  clear_value t5_2
  have b_t5_2 : t5_2 < 2^64 := by rw [e_t5_2]; exact neg_lt _
  -- a0_3: mul a0,a0,t6
  extract_lets -merge +onlyGivenNames a0_3 at hr
  have e_a0_3 : a0_3 = a0_2 * t6_1 % 2^64 := rfl
  clear_value a0_3
  have b_a0_3 : a0_3 < 2^64 := by rw [e_a0_3]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- a1_3: mul a1,a1,t6
  extract_lets -merge +onlyGivenNames a1_3 at hr
  have e_a1_3 : a1_3 = a1_2 * t6_1 % 2^64 := rfl
  clear_value a1_3
  have b_a1_3 : a1_3 < 2^64 := by rw [e_a1_3]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- a2_3: mul a2,a2,t6
  extract_lets -merge +onlyGivenNames a2_3 at hr
  have e_a2_3 : a2_3 = a2_2 * t6_1 % 2^64 := rfl
  clear_value a2_3
  have b_a2_3 : a2_3 < 2^64 := by rw [e_a2_3]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- a1_4: adds a1,a1,t0
  extract_lets -merge +onlyGivenNames s_3 a1_4 c_3 at hr
  have e_a1_4 : a1_4 = (a1_3 + t0 + 0) % 2^64 := rfl
  have e_c_3 : c_3 = (a1_3 + t0 + 0) / 2^64 := rfl
  clear_value s_3 a1_4 c_3
  have l_a1_4 : a1_4 + 2^64 * c_3 = a1_3 + t0 + 0 := by
    rw [e_a1_4, e_c_3]; exact Nat.mod_add_div _ _
  have b_a1_4 : a1_4 < 2^64 := by rw [e_a1_4]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_3 : c_3 ≤ 1 := by
    rw [e_c_3]; exact addc_carry_le_one a1_3 t0 0 b_a1_3 b_t0 (by decide)
  clear e_a1_4 e_c_3
  -- a3_3: mul a3,a3,t6
  extract_lets -merge +onlyGivenNames a3_3 at hr
  have e_a3_3 : a3_3 = a3_2 * t6_1 % 2^64 := rfl
  clear_value a3_3
  have b_a3_3 : a3_3 < 2^64 := by rw [e_a3_3]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- a2_4: adcs a2,a2,t1
  extract_lets -merge +onlyGivenNames s_4 a2_4 c_4 at hr
  have e_a2_4 : a2_4 = (a2_3 + t1 + c_3) % 2^64 := rfl
  have e_c_4 : c_4 = (a2_3 + t1 + c_3) / 2^64 := rfl
  clear_value s_4 a2_4 c_4
  have l_a2_4 : a2_4 + 2^64 * c_4 = a2_3 + t1 + c_3 := by
    rw [e_a2_4, e_c_4]; exact Nat.mod_add_div _ _
  have b_a2_4 : a2_4 < 2^64 := by rw [e_a2_4]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_4 : c_4 ≤ 1 := by
    rw [e_c_4]; exact addc_carry_le_one a2_3 t1 c_3 b_a2_3 b_t1 b_c_3
  clear e_a2_4 e_c_4
  -- a3_4: adcs a3,a3,t2
  extract_lets -merge +onlyGivenNames s_5 a3_4 c_5 at hr
  have e_a3_4 : a3_4 = (a3_3 + t2 + c_4) % 2^64 := rfl
  have e_c_5 : c_5 = (a3_3 + t2 + c_4) / 2^64 := rfl
  clear_value s_5 a3_4 c_5
  have l_a3_4 : a3_4 + 2^64 * c_5 = a3_3 + t2 + c_4 := by
    rw [e_a3_4, e_c_5]; exact Nat.mod_add_div _ _
  have b_a3_4 : a3_4 < 2^64 := by rw [e_a3_4]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_5 : c_5 ≤ 1 := by
    rw [e_c_5]; exact addc_carry_le_one a3_3 t2 c_4 b_a3_3 b_t2 b_c_4
  clear e_a3_4 e_c_5
  -- t3_1: adc t3,t3,t5
  extract_lets -merge +onlyGivenNames t3_1 at hr
  have e_t3_1 : t3_1 = (t3 + t5_2 + c_5) % 2^64 := rfl
  clear_value t3_1
  have b_t3_1 : t3_1 < 2^64 := by rw [e_t3_1]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨k_t3_1, b_k_t3_1, l_t3_1⟩ :
      ∃ k, k ≤ 1 ∧ t3_1 + 2^64 * k = t3 + t5_2 + c_5 :=
    ⟨(t3 + t5_2 + c_5) / 2^64, addc_carry_le_one t3 t5_2 c_5 b_t3 b_t5_2 b_c_5,
      by rw [e_t3_1]; exact Nat.mod_add_div _ _⟩
  clear e_t3_1
  -- BEGIN updateAB product a
  have hANat : a.toNat = a0 + 2^64 * a1 + 2^128 * a2 + 2^192 * a3 := by
    rw [e_a0, e_a1, e_a2, e_a3]
    rfl
  have hmaskF : t5 = if x < 0 then 2^64 - 1 else 0 := by
    rw [e_t5, e_f']
    exact asr63_of_wordRep hf hfx hx
  have hmagF : t6_1 = x.natAbs := by
    rw [e_t6_1, e_t6, e_t5, e_f']
    exact signedMagnitude_exact hf hfx hx
  have hprepChainA :
      a0_2 + 2^64 * a1_2 + 2^128 * a2_2 + 2^192 * a3_2 + 2^256 * k_a3_2 =
        a0_1 + 2^64 * a1_1 + 2^128 * a2_1 + 2^192 * a3_1 + lsr t5 63 := by
    clear * - l_a0_2 l_a1_2 l_a2_2 l_a3_2
    omega
  have hprepLowA : a0_2 + 2^64 * a1_2 + 2^128 * a2_2 + 2^192 * a3_2 < 2^256 := by
    clear * - b_a0_2 b_a1_2 b_a2_2 b_a3_2
    omega
  have hprepA : a0_2 + 2^64 * a1_2 + 2^128 * a2_2 + 2^192 * a3_2 =
      if x < 0 then 2^256 - a.toNat else a.toNat := by
    by_cases hneg : x < 0
    · have haPos : 0 < a.toNat := by
        by_contra hnot
        have haZero : a.toNat = 0 := by omega
        exact (not_le_of_gt hneg) (hzeroA haZero)
      have ht5 : t5 = 2^64 - 1 := by rw [hmaskF, if_pos hneg]
      have hbit : lsr t5 63 = 1 := by rw [ht5]; norm_num [lsr]
      have hcompA :
          a0_1 + 2^64 * a1_1 + 2^128 * a2_1 + 2^192 * a3_1 + 1 +
            (a0 + 2^64 * a1 + 2^128 * a2 + 2^192 * a3) = 2^256 := by
        rw [e_a0_1, e_a1_1, e_a2_1, e_a3_1, ht5]
        exact complementFour_eq a0 a1 a2 a3 b_a0 b_a1 b_a2 b_a3
      rw [if_pos hneg]
      clear * - hANat hprepChainA hprepLowA hbit hcompA haPos
      omega
    · have ht5 : t5 = 0 := by rw [hmaskF, if_neg hneg]
      have hbit : lsr t5 63 = 0 := by rw [ht5]; rfl
      have ha0s : a0_1 = a0 := by rw [e_a0_1, ht5, eor_zero b_a0]
      have ha1s : a1_1 = a1 := by rw [e_a1_1, ht5, eor_zero b_a1]
      have ha2s : a2_1 = a2 := by rw [e_a2_1, ht5, eor_zero b_a2]
      have ha3s : a3_1 = a3 := by rw [e_a3_1, ht5, eor_zero b_a3]
      rw [if_neg hneg]
      have hAlt := Limbs.toNat_lt a ha
      clear * - hANat hprepChainA hbit ha0s ha1s ha2s ha3s hAlt
      omega
  have htopF : t5_2 = if x < 0 then 2^64 - x.natAbs else 0 := by
    by_cases hneg : x < 0
    · have ht5 : t5 = 2^64 - 1 := by rw [hmaskF, if_pos hneg]
      have habsPos : 0 < x.natAbs := Int.natAbs_pos.mpr hneg.ne
      have habsLt : x.natAbs < 2^64 := hx.trans (by norm_num)
      rw [if_pos hneg, e_t5_2, e_t5_1, ht5, hmagF,
        bitAnd_allOnes_left habsLt, neg_eq_complement habsPos habsLt]
    · have ht5 : t5 = 0 := by rw [hmaskF, if_neg hneg]
      rw [if_neg hneg, e_t5_2, e_t5_1, ht5]
      rw [show bitAnd 0 t6_1 = 0 by simp [bitAnd, word]]
      decide
  have ha0lo : a0_3 = lo_t0 := by
    rw [e_a0_3, ← d_t0, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b_lo_t0]
  have ha1lo : a1_3 = lo_t1 := by
    rw [e_a1_3, ← d_t1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b_lo_t1]
  have ha2lo : a2_3 = lo_t2 := by
    rw [e_a2_3, ← d_t2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b_lo_t2]
  have ha3lo : a3_3 = lo_t3 := by
    rw [e_a3_3, ← d_t3, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b_lo_t3]
  have hmulA :
      a0_3 + 2^64 * a1_4 + 2^128 * a2_4 + 2^192 * a3_4 + 2^256 * t3_1 +
          2^320 * k_t3_1 =
        (a0_2 + 2^64 * a1_2 + 2^128 * a2_2 + 2^192 * a3_2) * t6_1 +
          2^256 * t5_2 := by
    rw [show (a0_2 + 2^64 * a1_2 + 2^128 * a2_2 + 2^192 * a3_2) * t6_1 =
      a0_2 * t6_1 + 2^64 * (a1_2 * t6_1) + 2^128 * (a2_2 * t6_1) +
        2^192 * (a3_2 * t6_1) by ring]
    clear * - d_t0 d_t1 d_t2 d_t3 ha0lo ha1lo ha2lo ha3lo
      l_a1_4 l_a2_4 l_a3_4 l_t3_1
    omega
  have hfullA :
      a0_3 + 2^64 * a1_4 + 2^128 * a2_4 + 2^192 * a3_4 + 2^256 * t3_1 +
          2^320 * k_t3_1 = signedProductValue a.toNat x := by
    rw [hmulA, hprepA, hmagF, htopF]
    by_cases hneg : x < 0
    · simp only [signedProductValue, if_pos hneg]
    · have hnonneg : 0 ≤ x := Int.not_lt.mp hneg
      have habs : x.natAbs = x.toNat := by
        have h1 : (x.natAbs : Int) = x := Int.natAbs_of_nonneg hnonneg
        have h2 : (x.toNat : Int) = x := Int.toNat_of_nonneg hnonneg
        exact_mod_cast h1.trans h2.symm
      simp only [signedProductValue, if_neg hneg, habs, Nat.mul_zero, Nat.add_zero]
  have hexactA := signedProductValue_exact a.toNat x (Limbs.toNat_lt a ha) hx hzeroA
  have hboundProdA : signedProductValue a.toNat x < 2^320 := by
    rw [hexactA]
    by_cases hneg : x < 0
    · rw [if_pos hneg]
      have haPos : 0 < a.toNat := by
        by_contra hnot
        exact (not_le_of_gt hneg) (hzeroA (by omega))
      have habsPos : 0 < x.natAbs := Int.natAbs_pos.mpr hneg.ne
      have hprodPos : 0 < a.toNat * x.natAbs := Nat.mul_pos haPos habsPos
      omega
    · rw [if_neg hneg]
      have hnonneg : 0 ≤ x := Int.not_lt.mp hneg
      have habs : x.natAbs = x.toNat := by
        have h1 : (x.natAbs : Int) = x := Int.natAbs_of_nonneg hnonneg
        have h2 : (x.toNat : Int) = x := Int.toNat_of_nonneg hnonneg
        exact_mod_cast h1.trans h2.symm
      have hxTo : x.toNat < 2^63 := by rw [← habs]; exact hx
      have hprod := Nat.mul_lt_mul'' (Limbs.toNat_lt a ha) hxTo
      norm_num at hprod ⊢
      exact hprod.trans (by norm_num)
  have hkProdA : k_t3_1 = 0 := by
    clear * - hfullA hboundProdA
    omega
  have hprodA :
      a0_3 + 2^64 * a1_4 + 2^128 * a2_4 + 2^192 * a3_4 + 2^256 * t3_1 =
        signedProductValue a.toNat x := by
    clear * - hfullA hkProdA
    omega
  -- END updateAB product a
  -- t5_3: asr t5,g,#63
  extract_lets -merge +onlyGivenNames t5_3 at hr
  have e_t5_3 : t5_3 = asr g' 63 := rfl
  clear_value t5_3
  have b_t5_3 : t5_3 < 2^64 := by rw [e_t5_3]; exact asr_lt _ _
  -- t6_2: eor t6,g,t5
  extract_lets -merge +onlyGivenNames t6_2 at hr
  have e_t6_2 : t6_2 = eor g' t5_3 := rfl
  clear_value t6_2
  have b_t6_2 : t6_2 < 2^64 := by rw [e_t6_2]; exact eor_lt _ _
  -- b0_1: eor b0,b0,t5
  extract_lets -merge +onlyGivenNames b0_1 at hr
  have e_b0_1 : b0_1 = eor b0 t5_3 := rfl
  clear_value b0_1
  have b_b0_1 : b0_1 < 2^64 := by rw [e_b0_1]; exact eor_lt _ _
  -- t6_3: sub t6,t6,t5
  extract_lets -merge +onlyGivenNames t6_3 at hr
  have e_t6_3 : t6_3 = sub t6_2 t5_3 := rfl
  clear_value t6_3
  have b_t6_3 : t6_3 < 2^64 := by rw [e_t6_3]; exact sub_lt _ _
  -- b1_1: eor b1,b1,t5
  extract_lets -merge +onlyGivenNames b1_1 at hr
  have e_b1_1 : b1_1 = eor b1 t5_3 := rfl
  clear_value b1_1
  have b_b1_1 : b1_1 < 2^64 := by rw [e_b1_1]; exact eor_lt _ _
  -- b0_2: adds b0,b0,t5,lsr #63
  extract_lets -merge +onlyGivenNames s_6 b0_2 c_6 at hr
  have e_b0_2 : b0_2 = (b0_1 + (lsr t5_3 63) + 0) % 2^64 := rfl
  have e_c_6 : c_6 = (b0_1 + (lsr t5_3 63) + 0) / 2^64 := rfl
  clear_value s_6 b0_2 c_6
  have l_b0_2 : b0_2 + 2^64 * c_6 = b0_1 + (lsr t5_3 63) + 0 := by
    rw [e_b0_2, e_c_6]; exact Nat.mod_add_div _ _
  have b_b0_2 : b0_2 < 2^64 := by rw [e_b0_2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_6 : c_6 ≤ 1 := by
    rw [e_c_6]; exact addc_carry_le_one b0_1 (lsr t5_3 63) 0 b_b0_1 (lt_of_le_of_lt (Nat.div_le_self _ _) b_t5_3) (by decide)
  clear e_b0_2 e_c_6
  -- b2_1: eor b2,b2,t5
  extract_lets -merge +onlyGivenNames b2_1 at hr
  have e_b2_1 : b2_1 = eor b2 t5_3 := rfl
  clear_value b2_1
  have b_b2_1 : b2_1 < 2^64 := by rw [e_b2_1]; exact eor_lt _ _
  -- b1_2: adcs b1,b1,xzr
  extract_lets -merge +onlyGivenNames s_7 b1_2 c_7 at hr
  have e_b1_2 : b1_2 = (b1_1 + 0 + c_6) % 2^64 := rfl
  have e_c_7 : c_7 = (b1_1 + 0 + c_6) / 2^64 := rfl
  clear_value s_7 b1_2 c_7
  have l_b1_2 : b1_2 + 2^64 * c_7 = b1_1 + 0 + c_6 := by
    rw [e_b1_2, e_c_7]; exact Nat.mod_add_div _ _
  have b_b1_2 : b1_2 < 2^64 := by rw [e_b1_2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_7 : c_7 ≤ 1 := by
    rw [e_c_7]; exact addc_carry_le_one b1_1 0 c_6 b_b1_1 (by decide) b_c_6
  clear e_b1_2 e_c_7
  -- b3_1: eor b3,b3,t5
  extract_lets -merge +onlyGivenNames b3_1 at hr
  have e_b3_1 : b3_1 = eor b3 t5_3 := rfl
  clear_value b3_1
  have b_b3_1 : b3_1 < 2^64 := by rw [e_b3_1]; exact eor_lt _ _
  -- t0_1: umulh t0,b0,t6
  extract_lets -merge +onlyGivenNames t0_1 at hr
  have e_t0_1 : t0_1 = b0_2 * t6_3 / 2^64 := rfl
  clear_value t0_1
  have p_t0_1 : b0_2 * t6_3 < 2^64 * 2^64 := Nat.mul_lt_mul'' b_b0_2 b_t6_3
  have b_t0_1 : t0_1 < 2^64 := by rw [e_t0_1]; exact Nat.div_lt_of_lt_mul p_t0_1
  obtain ⟨lo_t0_1, b_lo_t0_1, d_t0_1⟩ :
      ∃ lo, lo < 2^64 ∧ lo + 2^64 * t0_1 = b0_2 * t6_3 :=
    ⟨b0_2 * t6_3 % 2^64, Nat.mod_lt _ (Nat.two_pow_pos _),
      by rw [e_t0_1]; exact Nat.mod_add_div _ _⟩
  clear e_t0_1
  -- b2_2: adcs b2,b2,xzr
  extract_lets -merge +onlyGivenNames s_8 b2_2 c_8 at hr
  have e_b2_2 : b2_2 = (b2_1 + 0 + c_7) % 2^64 := rfl
  have e_c_8 : c_8 = (b2_1 + 0 + c_7) / 2^64 := rfl
  clear_value s_8 b2_2 c_8
  have l_b2_2 : b2_2 + 2^64 * c_8 = b2_1 + 0 + c_7 := by
    rw [e_b2_2, e_c_8]; exact Nat.mod_add_div _ _
  have b_b2_2 : b2_2 < 2^64 := by rw [e_b2_2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_8 : c_8 ≤ 1 := by
    rw [e_c_8]; exact addc_carry_le_one b2_1 0 c_7 b_b2_1 (by decide) b_c_7
  clear e_b2_2 e_c_8
  -- t1_1: umulh t1,b1,t6
  extract_lets -merge +onlyGivenNames t1_1 at hr
  have e_t1_1 : t1_1 = b1_2 * t6_3 / 2^64 := rfl
  clear_value t1_1
  have p_t1_1 : b1_2 * t6_3 < 2^64 * 2^64 := Nat.mul_lt_mul'' b_b1_2 b_t6_3
  have b_t1_1 : t1_1 < 2^64 := by rw [e_t1_1]; exact Nat.div_lt_of_lt_mul p_t1_1
  obtain ⟨lo_t1_1, b_lo_t1_1, d_t1_1⟩ :
      ∃ lo, lo < 2^64 ∧ lo + 2^64 * t1_1 = b1_2 * t6_3 :=
    ⟨b1_2 * t6_3 % 2^64, Nat.mod_lt _ (Nat.two_pow_pos _),
      by rw [e_t1_1]; exact Nat.mod_add_div _ _⟩
  clear e_t1_1
  -- b3_2: adc b3,b3,xzr
  extract_lets -merge +onlyGivenNames b3_2 at hr
  have e_b3_2 : b3_2 = (b3_1 + 0 + c_8) % 2^64 := rfl
  clear_value b3_2
  have b_b3_2 : b3_2 < 2^64 := by rw [e_b3_2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨k_b3_2, b_k_b3_2, l_b3_2⟩ :
      ∃ k, k ≤ 1 ∧ b3_2 + 2^64 * k = b3_1 + 0 + c_8 :=
    ⟨(b3_1 + 0 + c_8) / 2^64, addc_carry_le_one b3_1 0 c_8 b_b3_1 (by decide) b_c_8,
      by rw [e_b3_2]; exact Nat.mod_add_div _ _⟩
  clear e_b3_2
  -- t2_1: umulh t2,b2,t6
  extract_lets -merge +onlyGivenNames t2_1 at hr
  have e_t2_1 : t2_1 = b2_2 * t6_3 / 2^64 := rfl
  clear_value t2_1
  have p_t2_1 : b2_2 * t6_3 < 2^64 * 2^64 := Nat.mul_lt_mul'' b_b2_2 b_t6_3
  have b_t2_1 : t2_1 < 2^64 := by rw [e_t2_1]; exact Nat.div_lt_of_lt_mul p_t2_1
  obtain ⟨lo_t2_1, b_lo_t2_1, d_t2_1⟩ :
      ∃ lo, lo < 2^64 ∧ lo + 2^64 * t2_1 = b2_2 * t6_3 :=
    ⟨b2_2 * t6_3 % 2^64, Nat.mod_lt _ (Nat.two_pow_pos _),
      by rw [e_t2_1]; exact Nat.mod_add_div _ _⟩
  clear e_t2_1
  -- t5_4: and t5,t5,t6
  extract_lets -merge +onlyGivenNames t5_4 at hr
  have e_t5_4 : t5_4 = bitAnd t5_3 t6_3 := rfl
  clear_value t5_4
  have b_t5_4 : t5_4 < 2^64 := by rw [e_t5_4]; exact bitAnd_lt _ _
  -- t4: umulh t4,b3,t6
  extract_lets -merge +onlyGivenNames t4 at hr
  have e_t4 : t4 = b3_2 * t6_3 / 2^64 := rfl
  clear_value t4
  have p_t4 : b3_2 * t6_3 < 2^64 * 2^64 := Nat.mul_lt_mul'' b_b3_2 b_t6_3
  have b_t4 : t4 < 2^64 := by rw [e_t4]; exact Nat.div_lt_of_lt_mul p_t4
  obtain ⟨lo_t4, b_lo_t4, d_t4⟩ :
      ∃ lo, lo < 2^64 ∧ lo + 2^64 * t4 = b3_2 * t6_3 :=
    ⟨b3_2 * t6_3 % 2^64, Nat.mod_lt _ (Nat.two_pow_pos _),
      by rw [e_t4]; exact Nat.mod_add_div _ _⟩
  clear e_t4
  -- t5_5: neg t5,t5
  extract_lets -merge +onlyGivenNames t5_5 at hr
  have e_t5_5 : t5_5 = neg t5_4 := rfl
  clear_value t5_5
  have b_t5_5 : t5_5 < 2^64 := by rw [e_t5_5]; exact neg_lt _
  -- b0_3: mul b0,b0,t6
  extract_lets -merge +onlyGivenNames b0_3 at hr
  have e_b0_3 : b0_3 = b0_2 * t6_3 % 2^64 := rfl
  clear_value b0_3
  have b_b0_3 : b0_3 < 2^64 := by rw [e_b0_3]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- b1_3: mul b1,b1,t6
  extract_lets -merge +onlyGivenNames b1_3 at hr
  have e_b1_3 : b1_3 = b1_2 * t6_3 % 2^64 := rfl
  clear_value b1_3
  have b_b1_3 : b1_3 < 2^64 := by rw [e_b1_3]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- b2_3: mul b2,b2,t6
  extract_lets -merge +onlyGivenNames b2_3 at hr
  have e_b2_3 : b2_3 = b2_2 * t6_3 % 2^64 := rfl
  clear_value b2_3
  have b_b2_3 : b2_3 < 2^64 := by rw [e_b2_3]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- b1_4: adds b1,b1,t0
  extract_lets -merge +onlyGivenNames s_9 b1_4 c_9 at hr
  have e_b1_4 : b1_4 = (b1_3 + t0_1 + 0) % 2^64 := rfl
  have e_c_9 : c_9 = (b1_3 + t0_1 + 0) / 2^64 := rfl
  clear_value s_9 b1_4 c_9
  have l_b1_4 : b1_4 + 2^64 * c_9 = b1_3 + t0_1 + 0 := by
    rw [e_b1_4, e_c_9]; exact Nat.mod_add_div _ _
  have b_b1_4 : b1_4 < 2^64 := by rw [e_b1_4]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_9 : c_9 ≤ 1 := by
    rw [e_c_9]; exact addc_carry_le_one b1_3 t0_1 0 b_b1_3 b_t0_1 (by decide)
  clear e_b1_4 e_c_9
  -- b3_3: mul b3,b3,t6
  extract_lets -merge +onlyGivenNames b3_3 at hr
  have e_b3_3 : b3_3 = b3_2 * t6_3 % 2^64 := rfl
  clear_value b3_3
  have b_b3_3 : b3_3 < 2^64 := by rw [e_b3_3]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- b2_4: adcs b2,b2,t1
  extract_lets -merge +onlyGivenNames s_10 b2_4 c_10 at hr
  have e_b2_4 : b2_4 = (b2_3 + t1_1 + c_9) % 2^64 := rfl
  have e_c_10 : c_10 = (b2_3 + t1_1 + c_9) / 2^64 := rfl
  clear_value s_10 b2_4 c_10
  have l_b2_4 : b2_4 + 2^64 * c_10 = b2_3 + t1_1 + c_9 := by
    rw [e_b2_4, e_c_10]; exact Nat.mod_add_div _ _
  have b_b2_4 : b2_4 < 2^64 := by rw [e_b2_4]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_10 : c_10 ≤ 1 := by
    rw [e_c_10]; exact addc_carry_le_one b2_3 t1_1 c_9 b_b2_3 b_t1_1 b_c_9
  clear e_b2_4 e_c_10
  -- b3_4: adcs b3,b3,t2
  extract_lets -merge +onlyGivenNames s_11 b3_4 c_11 at hr
  have e_b3_4 : b3_4 = (b3_3 + t2_1 + c_10) % 2^64 := rfl
  have e_c_11 : c_11 = (b3_3 + t2_1 + c_10) / 2^64 := rfl
  clear_value s_11 b3_4 c_11
  have l_b3_4 : b3_4 + 2^64 * c_11 = b3_3 + t2_1 + c_10 := by
    rw [e_b3_4, e_c_11]; exact Nat.mod_add_div _ _
  have b_b3_4 : b3_4 < 2^64 := by rw [e_b3_4]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_11 : c_11 ≤ 1 := by
    rw [e_c_11]; exact addc_carry_le_one b3_3 t2_1 c_10 b_b3_3 b_t2_1 b_c_10
  clear e_b3_4 e_c_11
  -- t4_1: adc t4,t4,t5
  extract_lets -merge +onlyGivenNames t4_1 at hr
  have e_t4_1 : t4_1 = (t4 + t5_5 + c_11) % 2^64 := rfl
  clear_value t4_1
  have b_t4_1 : t4_1 < 2^64 := by rw [e_t4_1]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨k_t4_1, b_k_t4_1, l_t4_1⟩ :
      ∃ k, k ≤ 1 ∧ t4_1 + 2^64 * k = t4 + t5_5 + c_11 :=
    ⟨(t4 + t5_5 + c_11) / 2^64, addc_carry_le_one t4 t5_5 c_11 b_t4 b_t5_5 b_c_11,
      by rw [e_t4_1]; exact Nat.mod_add_div _ _⟩
  clear e_t4_1
  -- BEGIN updateAB product b
  have hBNat : b.toNat = b0 + 2^64 * b1 + 2^128 * b2 + 2^192 * b3 := by
    rw [e_b0, e_b1, e_b2, e_b3]
    rfl
  have hzeroB : b.toNat = 0 → 0 ≤ y := by intro h; omega
  have hmaskG : t5_3 = if y < 0 then 2^64 - 1 else 0 := by
    rw [e_t5_3, e_g']
    exact asr63_of_wordRep hg hgy hy
  have hmagG : t6_3 = y.natAbs := by
    rw [e_t6_3, e_t6_2, e_t5_3, e_g']
    exact signedMagnitude_exact hg hgy hy
  have hprepChainB :
      b0_2 + 2^64 * b1_2 + 2^128 * b2_2 + 2^192 * b3_2 + 2^256 * k_b3_2 =
        b0_1 + 2^64 * b1_1 + 2^128 * b2_1 + 2^192 * b3_1 + lsr t5_3 63 := by
    clear * - l_b0_2 l_b1_2 l_b2_2 l_b3_2
    omega
  have hprepLowB : b0_2 + 2^64 * b1_2 + 2^128 * b2_2 + 2^192 * b3_2 < 2^256 := by
    clear * - b_b0_2 b_b1_2 b_b2_2 b_b3_2
    omega
  have hprepB : b0_2 + 2^64 * b1_2 + 2^128 * b2_2 + 2^192 * b3_2 =
      if y < 0 then 2^256 - b.toNat else b.toNat := by
    by_cases hneg : y < 0
    · have ht5 : t5_3 = 2^64 - 1 := by rw [hmaskG, if_pos hneg]
      have hbit : lsr t5_3 63 = 1 := by rw [ht5]; norm_num [lsr]
      have hcompB :
          b0_1 + 2^64 * b1_1 + 2^128 * b2_1 + 2^192 * b3_1 + 1 +
            (b0 + 2^64 * b1 + 2^128 * b2 + 2^192 * b3) = 2^256 := by
        rw [e_b0_1, e_b1_1, e_b2_1, e_b3_1, ht5]
        exact complementFour_eq b0 b1 b2 b3 b_b0 b_b1 b_b2 b_b3
      rw [if_pos hneg]
      clear * - hBNat hprepChainB hprepLowB hbit hcompB hbPos
      omega
    · have ht5 : t5_3 = 0 := by rw [hmaskG, if_neg hneg]
      have hbit : lsr t5_3 63 = 0 := by rw [ht5]; rfl
      have hb0s : b0_1 = b0 := by rw [e_b0_1, ht5, eor_zero b_b0]
      have hb1s : b1_1 = b1 := by rw [e_b1_1, ht5, eor_zero b_b1]
      have hb2s : b2_1 = b2 := by rw [e_b2_1, ht5, eor_zero b_b2]
      have hb3s : b3_1 = b3 := by rw [e_b3_1, ht5, eor_zero b_b3]
      rw [if_neg hneg]
      have hBlt := Limbs.toNat_lt b hb
      clear * - hBNat hprepChainB hbit hb0s hb1s hb2s hb3s hBlt
      omega
  have htopG : t5_5 = if y < 0 then 2^64 - y.natAbs else 0 := by
    by_cases hneg : y < 0
    · have ht5 : t5_3 = 2^64 - 1 := by rw [hmaskG, if_pos hneg]
      have habsPos : 0 < y.natAbs := Int.natAbs_pos.mpr hneg.ne
      have habsLt : y.natAbs < 2^64 := hy.trans (by norm_num)
      rw [if_pos hneg, e_t5_5, e_t5_4, ht5, hmagG,
        bitAnd_allOnes_left habsLt, neg_eq_complement habsPos habsLt]
    · have ht5 : t5_3 = 0 := by rw [hmaskG, if_neg hneg]
      rw [if_neg hneg, e_t5_5, e_t5_4, ht5]
      rw [show bitAnd 0 t6_3 = 0 by simp [bitAnd, word]]
      decide
  have hb0lo : b0_3 = lo_t0_1 := by
    rw [e_b0_3, ← d_t0_1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b_lo_t0_1]
  have hb1lo : b1_3 = lo_t1_1 := by
    rw [e_b1_3, ← d_t1_1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b_lo_t1_1]
  have hb2lo : b2_3 = lo_t2_1 := by
    rw [e_b2_3, ← d_t2_1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b_lo_t2_1]
  have hb3lo : b3_3 = lo_t4 := by
    rw [e_b3_3, ← d_t4, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b_lo_t4]
  have hmulB :
      b0_3 + 2^64 * b1_4 + 2^128 * b2_4 + 2^192 * b3_4 + 2^256 * t4_1 +
          2^320 * k_t4_1 =
        (b0_2 + 2^64 * b1_2 + 2^128 * b2_2 + 2^192 * b3_2) * t6_3 +
          2^256 * t5_5 := by
    rw [show (b0_2 + 2^64 * b1_2 + 2^128 * b2_2 + 2^192 * b3_2) * t6_3 =
      b0_2 * t6_3 + 2^64 * (b1_2 * t6_3) + 2^128 * (b2_2 * t6_3) +
        2^192 * (b3_2 * t6_3) by ring]
    clear * - d_t0_1 d_t1_1 d_t2_1 d_t4 hb0lo hb1lo hb2lo hb3lo
      l_b1_4 l_b2_4 l_b3_4 l_t4_1
    omega
  have hfullB :
      b0_3 + 2^64 * b1_4 + 2^128 * b2_4 + 2^192 * b3_4 + 2^256 * t4_1 +
          2^320 * k_t4_1 = signedProductValue b.toNat y := by
    rw [hmulB, hprepB, hmagG, htopG]
    by_cases hneg : y < 0
    · simp only [signedProductValue, if_pos hneg]
    · have hnonneg : 0 ≤ y := Int.not_lt.mp hneg
      have habs : y.natAbs = y.toNat := by
        have h1 : (y.natAbs : Int) = y := Int.natAbs_of_nonneg hnonneg
        have h2 : (y.toNat : Int) = y := Int.toNat_of_nonneg hnonneg
        exact_mod_cast h1.trans h2.symm
      simp only [signedProductValue, if_neg hneg, habs, Nat.mul_zero, Nat.add_zero]
  have hexactB := signedProductValue_exact b.toNat y (Limbs.toNat_lt b hb) hy hzeroB
  have hboundProdB : signedProductValue b.toNat y < 2^320 := by
    rw [hexactB]
    by_cases hneg : y < 0
    · rw [if_pos hneg]
      have habsPos : 0 < y.natAbs := Int.natAbs_pos.mpr hneg.ne
      have hprodPos : 0 < b.toNat * y.natAbs := Nat.mul_pos hbPos habsPos
      omega
    · rw [if_neg hneg]
      have hnonneg : 0 ≤ y := Int.not_lt.mp hneg
      have habs : y.natAbs = y.toNat := by
        have h1 : (y.natAbs : Int) = y := Int.natAbs_of_nonneg hnonneg
        have h2 : (y.toNat : Int) = y := Int.toNat_of_nonneg hnonneg
        exact_mod_cast h1.trans h2.symm
      have hyTo : y.toNat < 2^63 := by rw [← habs]; exact hy
      have hprod := Nat.mul_lt_mul'' (Limbs.toNat_lt b hb) hyTo
      norm_num at hprod ⊢
      exact hprod.trans (by norm_num)
  have hkProdB : k_t4_1 = 0 := by
    clear * - hfullB hboundProdB
    omega
  have hprodB :
      b0_3 + 2^64 * b1_4 + 2^128 * b2_4 + 2^192 * b3_4 + 2^256 * t4_1 =
        signedProductValue b.toNat y := by
    clear * - hfullB hkProdB
    omega
  -- END updateAB product b
  -- a0_4: adds a0,a0,b0
  extract_lets -merge +onlyGivenNames s_12 a0_4 c_12 at hr
  have e_a0_4 : a0_4 = (a0_3 + b0_3 + 0) % 2^64 := rfl
  have e_c_12 : c_12 = (a0_3 + b0_3 + 0) / 2^64 := rfl
  clear_value s_12 a0_4 c_12
  have l_a0_4 : a0_4 + 2^64 * c_12 = a0_3 + b0_3 + 0 := by
    rw [e_a0_4, e_c_12]; exact Nat.mod_add_div _ _
  have b_a0_4 : a0_4 < 2^64 := by rw [e_a0_4]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_12 : c_12 ≤ 1 := by
    rw [e_c_12]; exact addc_carry_le_one a0_3 b0_3 0 b_a0_3 b_b0_3 (by decide)
  clear e_a0_4 e_c_12
  -- a1_5: adcs a1,a1,b1
  extract_lets -merge +onlyGivenNames s_13 a1_5 c_13 at hr
  have e_a1_5 : a1_5 = (a1_4 + b1_4 + c_12) % 2^64 := rfl
  have e_c_13 : c_13 = (a1_4 + b1_4 + c_12) / 2^64 := rfl
  clear_value s_13 a1_5 c_13
  have l_a1_5 : a1_5 + 2^64 * c_13 = a1_4 + b1_4 + c_12 := by
    rw [e_a1_5, e_c_13]; exact Nat.mod_add_div _ _
  have b_a1_5 : a1_5 < 2^64 := by rw [e_a1_5]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_13 : c_13 ≤ 1 := by
    rw [e_c_13]; exact addc_carry_le_one a1_4 b1_4 c_12 b_a1_4 b_b1_4 b_c_12
  clear e_a1_5 e_c_13
  -- a2_5: adcs a2,a2,b2
  extract_lets -merge +onlyGivenNames s_14 a2_5 c_14 at hr
  have e_a2_5 : a2_5 = (a2_4 + b2_4 + c_13) % 2^64 := rfl
  have e_c_14 : c_14 = (a2_4 + b2_4 + c_13) / 2^64 := rfl
  clear_value s_14 a2_5 c_14
  have l_a2_5 : a2_5 + 2^64 * c_14 = a2_4 + b2_4 + c_13 := by
    rw [e_a2_5, e_c_14]; exact Nat.mod_add_div _ _
  have b_a2_5 : a2_5 < 2^64 := by rw [e_a2_5]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_14 : c_14 ≤ 1 := by
    rw [e_c_14]; exact addc_carry_le_one a2_4 b2_4 c_13 b_a2_4 b_b2_4 b_c_13
  clear e_a2_5 e_c_14
  -- a3_5: adcs a3,a3,b3
  extract_lets -merge +onlyGivenNames s_15 a3_5 c_15 at hr
  have e_a3_5 : a3_5 = (a3_4 + b3_4 + c_14) % 2^64 := rfl
  have e_c_15 : c_15 = (a3_4 + b3_4 + c_14) / 2^64 := rfl
  clear_value s_15 a3_5 c_15
  have l_a3_5 : a3_5 + 2^64 * c_15 = a3_4 + b3_4 + c_14 := by
    rw [e_a3_5, e_c_15]; exact Nat.mod_add_div _ _
  have b_a3_5 : a3_5 < 2^64 := by rw [e_a3_5]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_15 : c_15 ≤ 1 := by
    rw [e_c_15]; exact addc_carry_le_one a3_4 b3_4 c_14 b_a3_4 b_b3_4 b_c_14
  clear e_a3_5 e_c_15
  -- b0_4: adc b0,t3,t4
  extract_lets -merge +onlyGivenNames b0_4 at hr
  have e_b0_4 : b0_4 = (t3_1 + t4_1 + c_15) % 2^64 := rfl
  clear_value b0_4
  have b_b0_4 : b0_4 < 2^64 := by rw [e_b0_4]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨k_b0_4, b_k_b0_4, l_b0_4⟩ :
      ∃ k, k ≤ 1 ∧ b0_4 + 2^64 * k = t3_1 + t4_1 + c_15 :=
    ⟨(t3_1 + t4_1 + c_15) / 2^64, addc_carry_le_one t3_1 t4_1 c_15 b_t3_1 b_t4_1 b_c_15,
      by rw [e_b0_4]; exact Nat.mod_add_div _ _⟩
  clear e_b0_4
  -- BEGIN updateAB five-word sum
  let sumValue := a0_4 + 2^64 * a1_5 + 2^128 * a2_5 + 2^192 * a3_5 + 2^256 * b0_4
  let numerator : Int := x * (a.toNat : Int) + y * (b.toNat : Int)
  have hsumFull : sumValue + 2^320 * k_b0_4 =
      signedProductValue a.toNat x + signedProductValue b.toNat y := by
    dsimp only [sumValue]
    rw [← hprodA, ← hprodB]
    clear * - l_a0_4 l_a1_5 l_a2_5 l_a3_5 l_b0_4
    omega
  have hsumBound : sumValue < 2^320 := by
    dsimp only [sumValue]
    clear * - b_a0_4 b_a1_5 b_a2_5 b_a3_5 b_b0_4
    omega
  have hsumNatMod : sumValue ≡
      signedProductValue a.toNat x + signedProductValue b.toNat y [MOD 2^320] :=
    modEq_of_add_mul _ _ k_b0_4 0 _ (by simpa [Nat.mul_comm] using hsumFull)
  have hprodAMod := signedProductValue_modEq a.toNat x (Limbs.toNat_lt a ha) hx hzeroA
  have hprodBMod := signedProductValue_modEq b.toNat y (Limbs.toNat_lt b hb) hy hzeroB
  have hsumMod : (sumValue : Int) ≡ numerator [ZMOD (2^320 : Nat)] := by
    have hcast := Int.natCast_modEq_iff.mpr hsumNatMod
    apply hcast.trans
    dsimp only [numerator]
    have hadd := hprodAMod.add hprodBMod
    simpa only [Int.natCast_add, mul_comm] using hadd
  have hsumCases := fiveWord_cases hsumBound hsumMod hnumerator
  -- END updateAB five-word sum
  -- a0_5: extr a0,a1,a0,#31
  extract_lets -merge +onlyGivenNames a0_5 at hr
  have e_a0_5 : a0_5 = extr a1_5 a0_4 31 := rfl
  clear_value a0_5
  have b_a0_5 : a0_5 < 2^64 := by rw [e_a0_5]; exact extr_lt _ _ _
  -- a1_6: extr a1,a2,a1,#31
  extract_lets -merge +onlyGivenNames a1_6 at hr
  have e_a1_6 : a1_6 = extr a2_5 a1_5 31 := rfl
  clear_value a1_6
  have b_a1_6 : a1_6 < 2^64 := by rw [e_a1_6]; exact extr_lt _ _ _
  -- a2_6: extr a2,a3,a2,#31
  extract_lets -merge +onlyGivenNames a2_6 at hr
  have e_a2_6 : a2_6 = extr a3_5 a2_5 31 := rfl
  clear_value a2_6
  have b_a2_6 : a2_6 < 2^64 := by rw [e_a2_6]; exact extr_lt _ _ _
  -- t4_2: asr t4,b0,#63
  extract_lets -merge +onlyGivenNames t4_2 at hr
  have e_t4_2 : t4_2 = asr b0_4 63 := rfl
  clear_value t4_2
  have b_t4_2 : t4_2 < 2^64 := by rw [e_t4_2]; exact asr_lt _ _
  -- a3_6: extr a3,b0,a3,#31
  extract_lets -merge +onlyGivenNames a3_6 at hr
  have e_a3_6 : a3_6 = extr b0_4 a3_5 31 := rfl
  clear_value a3_6
  have b_a3_6 : a3_6 < 2^64 := by rw [e_a3_6]; exact extr_lt _ _ _
  -- a0_6: eor a0,a0,t4
  extract_lets -merge +onlyGivenNames a0_6 at hr
  have e_a0_6 : a0_6 = eor a0_5 t4_2 := rfl
  clear_value a0_6
  have b_a0_6 : a0_6 < 2^64 := by rw [e_a0_6]; exact eor_lt _ _
  -- a1_7: eor a1,a1,t4
  extract_lets -merge +onlyGivenNames a1_7 at hr
  have e_a1_7 : a1_7 = eor a1_6 t4_2 := rfl
  clear_value a1_7
  have b_a1_7 : a1_7 < 2^64 := by rw [e_a1_7]; exact eor_lt _ _
  -- a0_7: adds a0,a0,t4,lsr #63
  extract_lets -merge +onlyGivenNames s_16 a0_7 c_16 at hr
  have e_a0_7 : a0_7 = (a0_6 + (lsr t4_2 63) + 0) % 2^64 := rfl
  have e_c_16 : c_16 = (a0_6 + (lsr t4_2 63) + 0) / 2^64 := rfl
  clear_value s_16 a0_7 c_16
  have l_a0_7 : a0_7 + 2^64 * c_16 = a0_6 + (lsr t4_2 63) + 0 := by
    rw [e_a0_7, e_c_16]; exact Nat.mod_add_div _ _
  have b_a0_7 : a0_7 < 2^64 := by rw [e_a0_7]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_16 : c_16 ≤ 1 := by
    rw [e_c_16]; exact addc_carry_le_one a0_6 (lsr t4_2 63) 0 b_a0_6 (lt_of_le_of_lt (Nat.div_le_self _ _) b_t4_2) (by decide)
  clear e_a0_7 e_c_16
  -- a2_7: eor a2,a2,t4
  extract_lets -merge +onlyGivenNames a2_7 at hr
  have e_a2_7 : a2_7 = eor a2_6 t4_2 := rfl
  clear_value a2_7
  have b_a2_7 : a2_7 < 2^64 := by rw [e_a2_7]; exact eor_lt _ _
  -- a1_8: adcs a1,a1,xzr
  extract_lets -merge +onlyGivenNames s_17 a1_8 c_17 at hr
  have e_a1_8 : a1_8 = (a1_7 + 0 + c_16) % 2^64 := rfl
  have e_c_17 : c_17 = (a1_7 + 0 + c_16) / 2^64 := rfl
  clear_value s_17 a1_8 c_17
  have l_a1_8 : a1_8 + 2^64 * c_17 = a1_7 + 0 + c_16 := by
    rw [e_a1_8, e_c_17]; exact Nat.mod_add_div _ _
  have b_a1_8 : a1_8 < 2^64 := by rw [e_a1_8]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_17 : c_17 ≤ 1 := by
    rw [e_c_17]; exact addc_carry_le_one a1_7 0 c_16 b_a1_7 (by decide) b_c_16
  clear e_a1_8 e_c_17
  -- a3_7: eor a3,a3,t4
  extract_lets -merge +onlyGivenNames a3_7 at hr
  have e_a3_7 : a3_7 = eor a3_6 t4_2 := rfl
  clear_value a3_7
  have b_a3_7 : a3_7 < 2^64 := by rw [e_a3_7]; exact eor_lt _ _
  -- a2_8: adcs a2,a2,xzr
  extract_lets -merge +onlyGivenNames s_18 a2_8 c_18 at hr
  have e_a2_8 : a2_8 = (a2_7 + 0 + c_17) % 2^64 := rfl
  have e_c_18 : c_18 = (a2_7 + 0 + c_17) / 2^64 := rfl
  clear_value s_18 a2_8 c_18
  have l_a2_8 : a2_8 + 2^64 * c_18 = a2_7 + 0 + c_17 := by
    rw [e_a2_8, e_c_18]; exact Nat.mod_add_div _ _
  have b_a2_8 : a2_8 < 2^64 := by rw [e_a2_8]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_18 : c_18 ≤ 1 := by
    rw [e_c_18]; exact addc_carry_le_one a2_7 0 c_17 b_a2_7 (by decide) b_c_17
  clear e_a2_8 e_c_18
  -- a3_8: adc a3,a3,xzr
  extract_lets -merge +onlyGivenNames a3_8 at hr
  have e_a3_8 : a3_8 = (a3_7 + 0 + c_18) % 2^64 := rfl
  clear_value a3_8
  have b_a3_8 : a3_8 < 2^64 := by rw [e_a3_8]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨k_a3_8, b_k_a3_8, l_a3_8⟩ :
      ∃ k, k ≤ 1 ∧ a3_8 + 2^64 * k = a3_7 + 0 + c_18 :=
    ⟨(a3_7 + 0 + c_18) / 2^64, addc_carry_le_one a3_7 0 c_18 b_a3_7 (by decide) b_c_18,
      by rw [e_a3_8]; exact Nat.mod_add_div _ _⟩
  clear e_a3_8
  -- f_1: eor f,f,t4
  extract_lets -merge +onlyGivenNames f_1 at hr
  have e_f_1 : f_1 = eor f' t4_2 := rfl
  clear_value f_1
  have b_f_1 : f_1 < 2^64 := by rw [e_f_1]; exact eor_lt _ _
  -- g_1: eor g,g,t4
  extract_lets -merge +onlyGivenNames g_1 at hr
  have e_g_1 : g_1 = eor g' t4_2 := rfl
  clear_value g_1
  have b_g_1 : g_1 < 2^64 := by rw [e_g_1]; exact eor_lt _ _
  -- f_2: sub f,f,t4
  extract_lets -merge +onlyGivenNames f_2 at hr
  have e_f_2 : f_2 = sub f_1 t4_2 := rfl
  clear_value f_2
  have b_f_2 : f_2 < 2^64 := by rw [e_f_2]; exact sub_lt _ _
  -- g_2: sub g,g,t4
  extract_lets -merge +onlyGivenNames g_2 at hr
  have e_g_2 : g_2 = sub g_1 t4_2 := rfl
  clear_value g_2
  have b_g_2 : g_2 < 2^64 := by rw [e_g_2]; exact sub_lt _ _
  subst hr
  -- BEGIN updateAB conclusion
  have houtBound : (⟨a0_7, a1_8, a2_8, a3_8⟩ : Limbs).Bounded :=
    ⟨b_a0_7, b_a1_8, b_a2_8, b_a3_8⟩
  have hdivNum : (2^31 : Int) ∣ numerator := by simpa [numerator] using hdiv
  have hshiftAbs := fiveWordShiftAbs a0_4 a1_5 a2_5 a3_5 b0_4 numerator
    b_a0_4 b_a1_5 b_a2_5 b_a3_5 b_b0_4 hsumCases hnumerator hdivNum
  rcases hshiftAbs with ⟨hmaskBase, hshiftAbs⟩
  rw [← e_a0_5, ← e_a1_6, ← e_a2_6, ← e_a3_6] at hshiftAbs
  have hmaskOut : t4_2 = if numerator < 0 then 2^64 - 1 else 0 :=
    e_t4_2.trans hmaskBase
  have horientF : WordRep f_2 (orient numerator * x) :=
    wordRep_orient hf hfx hmaskOut (by rw [e_f_2, e_f_1, e_f'])
  have horientG : WordRep g_2 (orient numerator * y) :=
    wordRep_orient hg hgy hmaskOut (by rw [e_g_2, e_g_1, e_g'])
  have hquotLt : numerator.natAbs / 2^31 < 2^256 := by
    apply Nat.div_lt_of_lt_mul
    have hp : 2^31 * 2^256 = 2^287 := by ring
    rw [hp]
    exact hnumerator
  refine ⟨houtBound, ?_, ?_, ?_⟩
  · change a0_7 + 2^64 * a1_8 + 2^128 * a2_8 + 2^192 * a3_8 =
      numerator.natAbs / 2^31
    by_cases hneg : numerator < 0
    · have hmaskOnes : t4_2 = 2^64 - 1 := by rw [hmaskOut, if_pos hneg]
      have hbitOne : lsr t4_2 63 = 1 := by rw [hmaskOnes]; norm_num [lsr]
      have hcompShift := complementFour_eq a0_5 a1_6 a2_6 a3_6
        b_a0_5 b_a1_6 b_a2_6 b_a3_6
      rw [if_pos hneg] at hshiftAbs
      have hinputTotal :
          a0_6 + 2^64 * a1_7 + 2^128 * a2_7 + 2^192 * a3_7 + 1 +
            (a0_5 + 2^64 * a1_6 + 2^128 * a2_6 + 2^192 * a3_6) = 2^256 := by
        rw [e_a0_6, e_a1_7, e_a2_7, e_a3_7, hmaskOnes]
        exact hcompShift
      have hinputTarget :
          a0_6 + 2^64 * a1_7 + 2^128 * a2_7 + 2^192 * a3_7 + 1 =
            numerator.natAbs / 2^31 := by
        clear * - hinputTotal hshiftAbs
        omega
      exact (fourWordCarryChain_exact
        a0_6 a1_7 a2_7 a3_7 a0_7 a1_8 a2_8 a3_8 c_16 c_17 c_18 k_a3_8 1
        (numerator.natAbs / 2^31)
        (by simpa [hbitOne] using l_a0_7) (by simpa using l_a1_8)
        (by simpa using l_a2_8) (by simpa using l_a3_8) hinputTarget hquotLt).1
    · have hmaskZero : t4_2 = 0 := by rw [hmaskOut, if_neg hneg]
      have hbitZero : lsr t4_2 63 = 0 := by rw [hmaskZero]; rfl
      have ha0same : a0_6 = a0_5 := by rw [e_a0_6, hmaskZero, eor_zero b_a0_5]
      have ha1same : a1_7 = a1_6 := by rw [e_a1_7, hmaskZero, eor_zero b_a1_6]
      have ha2same : a2_7 = a2_6 := by rw [e_a2_7, hmaskZero, eor_zero b_a2_6]
      have ha3same : a3_7 = a3_6 := by rw [e_a3_7, hmaskZero, eor_zero b_a3_6]
      rw [if_neg hneg] at hshiftAbs
      have hinputTarget :
          a0_6 + 2^64 * a1_7 + 2^128 * a2_7 + 2^192 * a3_7 + 0 =
            numerator.natAbs / 2^31 := by
        rw [ha0same, ha1same, ha2same, ha3same, add_zero]
        exact hshiftAbs
      exact (fourWordCarryChain_exact
        a0_6 a1_7 a2_7 a3_7 a0_7 a1_8 a2_8 a3_8 c_16 c_17 c_18 k_a3_8 0
        (numerator.natAbs / 2^31)
        (by simpa [hbitZero] using l_a0_7) (by simpa using l_a1_8)
        (by simpa using l_a2_8) (by simpa using l_a3_8) hinputTarget hquotLt).1
  · simpa only [numerator] using horientF
  · simpa only [numerator] using horientG
  -- END updateAB conclusion

end PastaAsm.AArch64
