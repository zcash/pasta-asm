/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.X86_64.Spec.Invert.Adjustment
import PastaAsm.X86_64.Spec.Invert.Compositions
import PastaAsm.X86_64.Spec.Invert.Divsteps.Lemmas
import Mathlib.Tactic.NormNum

/-!
# Correctness of the x86-64 full-width GCD-state update

This file connects Rust's five-word signed linear combination and the generated
shift/absolute-value helper to the shared signed transition rows.
-/

set_option exponentiation.threshold 400

namespace PastaAsm.X86_64

open InversionSpec InversionConvergence

private theorem signedWordRep_cases {w : Nat} {z : Int}
    (hrep : SignedWordRep w z) (hz : z.natAbs < 2^63) :
    (0 ≤ z ∧ w = z.toNat) ∨ (z < 0 ∧ w = 2^64 - z.natAbs) := by
  rcases hrep with ⟨hw, k, hk⟩
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

private theorem mulSigned5_signed_modEq
    (value : PastaAsm.WideLimbs) (scalar : Nat) (z : Int)
    (hv : value.Bounded) (hrep : SignedWordRep scalar z)
    (hz : z.natAbs < 2^63) :
    (mulSigned5 value scalar).Bounded ∧
      (mulSigned5 value scalar).toNat5 ≡ (value.toNat5 : Int) * z
        [ZMOD updateModulus] := by
  rcases signedWordRep_cases hrep hz with ⟨hznonneg, hscalar⟩ | ⟨hzneg, hscalar⟩
  · have hscalarBound : scalar < 2^64 := hrep.1
    have htoLt : z.toNat < 2^63 := by
      rw [Int.toNat_lt_of_ne_zero (by norm_num)]
      have hcast : (z.natAbs : Int) < 2^63 := by exact_mod_cast hz
      simpa only [Int.natAbs_of_nonneg hznonneg] using hcast
    have hscalarLow : scalar < 2^63 := by simpa [hscalar] using htoLt
    obtain ⟨hb, hcases⟩ := mulSigned5_spec value scalar hv hscalarBound
    rcases hcases with ⟨_, hmod⟩ | ⟨hcontra, _⟩
    · refine ⟨hb, ?_⟩
      rw [hscalar]
      have hcast := Int.natCast_modEq_iff.mpr hmod
      rw [hscalar, Int.natCast_mul, Int.toNat_of_nonneg hznonneg] at hcast
      exact hcast
    · omega
  · have hscalarBound : scalar < 2^64 := hrep.1
    have hscalarHigh : 2^63 ≤ scalar := by
      rw [hscalar]
      have hzabsPos : 0 < z.natAbs := Int.natAbs_pos.mpr hzneg.ne
      omega
    obtain ⟨hb, hcases⟩ := mulSigned5_spec value scalar hv hscalarBound
    rcases hcases with ⟨hcontra, _⟩ | ⟨_, hmod⟩
    · omega
    · refine ⟨hb, ?_⟩
      have hcast := Int.natCast_modEq_iff.mpr hmod
      have hmag : 2^64 - scalar = z.natAbs := by rw [hscalar]; omega
      rw [hmag, Int.natCast_add, Int.natCast_mul] at hcast
      have hzEq : z = -(z.natAbs : Int) := by
        have habs := Int.ofNat_natAbs_of_nonpos (Int.le_of_lt hzneg)
        omega
      rw [hzEq]
      rw [Int.modEq_iff_dvd] at hcast ⊢
      convert hcast using 1
      ring

/-- Rust's actual five-word `lincomb` represents the signed integer linear
combination modulo `2^320`, provided the two scalar words represent coefficients
inside the signed 64-bit range. -/
theorem invertLincomb5_signed_spec
    (a b : Limbs) (f g : Nat) (x y : Int)
    (ha : a.Bounded) (hb : b.Bounded)
    (hf : SignedWordRep f x) (hg : SignedWordRep g y)
    (hx : x.natAbs < 2^63) (hy : y.natAbs < 2^63) :
    let out := invertLincomb5 (extendForUpdate a) (extendForUpdate b) f g
    out.Bounded ∧
      out.toNat5 ≡ x * (a.toNat : Int) + y * (b.toNat : Int)
        [ZMOD updateModulus] := by
  dsimp only
  have hea : (extendForUpdate a).Bounded := by
    simp only [extendForUpdate, PastaAsm.WideLimbs.Bounded]
    exact ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2,
      by norm_num [regMod], by norm_num [regMod], by norm_num [regMod],
      by norm_num [regMod], by norm_num [regMod]⟩
  have heb : (extendForUpdate b).Bounded := by
    simp only [extendForUpdate, PastaAsm.WideLimbs.Bounded]
    exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2,
      by norm_num [regMod], by norm_num [regMod], by norm_num [regMod],
      by norm_num [regMod], by norm_num [regMod]⟩
  obtain ⟨hfa, hmoda⟩ := mulSigned5_signed_modEq (extendForUpdate a) f x hea hf hx
  obtain ⟨hgb, hmodb⟩ := mulSigned5_signed_modEq (extendForUpdate b) g y heb hg hy
  obtain ⟨hout, _⟩ := addWords5_spec
    (mulSigned5 (extendForUpdate a) f) (mulSigned5 (extendForUpdate b) g) hfa hgb
  refine ⟨hout, ?_⟩
  have haddNat := addWords5_modEq
    (mulSigned5 (extendForUpdate a) f) (mulSigned5 (extendForUpdate b) g) hfa hgb
  have hadd := Int.natCast_modEq_iff.mpr haddNat
  have hsum := hmoda.add hmodb
  apply hadd.trans
  simpa [PastaAsm.WideLimbs.toNat5, Limbs.toNat, extendForUpdate,
    Int.natCast_add, Int.natCast_mul, mul_comm] using hsum

private theorem toNat5_lt (value : PastaAsm.WideLimbs) (hv : value.Bounded) :
    value.toNat5 < 2^320 := by
  simp only [PastaAsm.WideLimbs.toNat5]
  obtain ⟨h0, h1, h2, h3, h4, _⟩ := hv
  simp only [regMod] at h0 h1 h2 h3 h4
  omega

private theorem add_mul_pow_div_31 (lo hi : Nat) :
    (lo + 2^64 * hi) / 2^31 = lo / 2^31 + 2^33 * hi := by
  have hfactor : 2^64 * hi = 2^31 * (2^33 * hi) := by ring
  rw [hfactor, Nat.add_mul_div_left _ _ (by positivity)]

private theorem shrd31_eq {lo hi : Nat} (hlo : lo < 2^64) (hhi : hi < 2^64) :
    shrd lo hi 31 = lo / 2^31 + 2^33 * (hi % 2^31) := by
  unfold shrd lsr lsl
  norm_num only [Nat.reducePow, Nat.reduceMod, Nat.reduceLeDiff]
  rw [word_eq_of_lt hlo, word_eq_of_lt hhi]
  have hmul : hi * 8589934592 % 18446744073709551616 =
      8589934592 * (hi % 2147483648) := by
    have hsplit := Nat.mod_add_div hi 2147483648
    rw [show hi = hi % 2147483648 + 2147483648 * (hi / 2147483648) by omega]
    rw [show (hi % 2147483648 + 2147483648 * (hi / 2147483648)) * 8589934592 =
      8589934592 * (hi % 2147483648) +
        18446744073709551616 * (hi / 2147483648) by ring]
    rw [hsplit, Nat.mul_comm 18446744073709551616,
      Nat.add_mul_mod_self_right]
    apply Nat.mod_eq_of_lt
    have hr := Nat.mod_lt hi (by norm_num : 0 < 2147483648)
    omega
  rw [hmul]
  apply word_eq_of_lt
  simp only [regMod]
  have hr := Nat.mod_lt hi (by norm_num : 0 < 2147483648)
  omega

private theorem shrdChain31 (value : PastaAsm.WideLimbs) (hv : value.Bounded) :
    shrd value.l0 value.l1 31 +
        2^64 * shrd value.l1 value.l2 31 +
        2^128 * shrd value.l2 value.l3 31 +
        2^192 * shrd value.l3 value.l4 31 +
        2^256 * (value.l4 / 2^31) =
      value.toNat5 / 2^31 := by
  rw [shrd31_eq hv.1 hv.2.1, shrd31_eq hv.2.1 hv.2.2.1,
    shrd31_eq hv.2.2.1 hv.2.2.2.1, shrd31_eq hv.2.2.2.1 hv.2.2.2.2.1]
  simp only [PastaAsm.WideLimbs.toNat5]
  have h1 := Nat.mod_add_div value.l1 (2^31)
  have h2 := Nat.mod_add_div value.l2 (2^31)
  have h3 := Nat.mod_add_div value.l3 (2^31)
  have h4 := Nat.mod_add_div value.l4 (2^31)
  rw [show value.l0 + 2^64 * value.l1 + 2^128 * value.l2 +
      2^192 * value.l3 + 2^256 * value.l4 =
    value.l0 + 2^64 * (value.l1 + 2^64 * (value.l2 +
      2^64 * (value.l3 + 2^64 * value.l4))) by ring]
  rw [add_mul_pow_div_31]
  clear * - h1 h2 h3 h4
  omega

private theorem toNat5_div_top (value : PastaAsm.WideLimbs) (hv : value.Bounded) :
    value.toNat5 / 2^256 = value.l4 := by
  simp only [PastaAsm.WideLimbs.toNat5]
  have hlow : value.l0 + 2^64 * value.l1 + 2^128 * value.l2 +
      2^192 * value.l3 < 2^256 := by
    obtain ⟨h0, h1, h2, h3, _, _⟩ := hv
    simp only [regMod] at h0 h1 h2 h3
    omega
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlow, zero_add]

private theorem signedFiveWord_cases {value : PastaAsm.WideLimbs} {z : Int}
    (hv : value.Bounded)
    (hrep : (value.toNat5 : Int) ≡ z [ZMOD updateModulus])
    (hz : z.natAbs < 2^287) :
    (0 ≤ z ∧ value.toNat5 = z.toNat) ∨
      (z < 0 ∧ value.toNat5 = 2^320 - z.natAbs) := by
  have hvalue := toNat5_lt value hv
  rw [Int.modEq_iff_dvd] at hrep
  rcases hrep with ⟨k, hk⟩
  by_cases hneg : z < 0
  · right
    refine ⟨hneg, ?_⟩
    have habs : (z.natAbs : Int) = -z :=
      Int.ofNat_natAbs_of_nonpos (Int.le_of_lt hneg)
    have habsLt : z.natAbs < 2^320 := hz.trans (by norm_num)
    have habsPos : 0 < z.natAbs := Int.natAbs_pos.mpr hneg.ne
    simp only [updateModulus] at hk
    norm_num at hk
    have hkNeg : k < 0 := by
      have hleftNeg : z - (value.toNat5 : Int) < 0 := by
        have hvalueNonneg : (0 : Int) ≤ value.toNat5 := by positivity
        omega
      rw [hk] at hleftNeg
      by_contra hnot
      have hkNonneg : 0 ≤ k := le_of_not_gt hnot
      have hmulNonneg : 0 ≤ (2^320 : Int) * k :=
        mul_nonneg (by positivity) hkNonneg
      exact (not_lt_of_ge hmulNonneg hleftNeg).elim
    have hkGtNegTwo : (-2 : Int) < k := by
      by_contra hnot
      have hkle : k ≤ -2 := le_of_not_gt hnot
      have hmulLe : (2^320 : Int) * k ≤ 2^320 * (-2) :=
        mul_le_mul_of_nonneg_left hkle (by positivity)
      have hvalueInt : (value.toNat5 : Int) < 2^320 := by exact_mod_cast hvalue
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
    simp only [updateModulus] at hk
    norm_num at hk
    have hkZero : k = 0 := by omega
    omega

private theorem natXor_allOnes_local {x : Nat} (hx : x < 2^64) :
    x ^^^ (2^64 - 1) = 2^64 - 1 - x := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one]
  rw [Nat.sub_sub, Nat.add_comm 1 x, Nat.testBit_two_pow_sub_succ hx]
  by_cases hi : i < 64
  · simp [hi]
  · have hpow : 2^64 ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    have hxi : x < 2^i := lt_of_lt_of_le hx hpow
    rw [Nat.testBit_lt_two_pow hxi]
    simp [hi]

private theorem bitXor_zero_local {x : Nat} (hx : x < 2^64) : bitXor x 0 = x := by
  unfold bitXor
  rw [word_eq_of_lt hx, word_zero, Nat.xor_zero, word_eq_of_lt hx]

private theorem bitXor_allOnes_local {x : Nat} (hx : x < 2^64) :
    bitXor x (2^64 - 1) = 2^64 - 1 - x := by
  unfold bitXor
  rw [word_eq_of_lt hx]
  have hall : 2^64 - 1 < regMod := by simp only [regMod]; omega
  rw [word_eq_of_lt hall, natXor_allOnes_local hx]
  exact word_eq_of_lt (by simp only [regMod]; omega)

private theorem complementFour_eq (q0 q1 q2 q3 : Nat)
    (h0 : q0 < 2^64) (h1 : q1 < 2^64)
    (h2 : q2 < 2^64) (h3 : q3 < 2^64) :
    bitXor q0 (2^64 - 1) + 2^64 * bitXor q1 (2^64 - 1) +
        2^128 * bitXor q2 (2^64 - 1) +
        2^192 * bitXor q3 (2^64 - 1) + 1 +
      (q0 + 2^64 * q1 + 2^128 * q2 + 2^192 * q3) = 2^256 := by
  rw [bitXor_allOnes_local h0, bitXor_allOnes_local h1,
    bitXor_allOnes_local h2, bitXor_allOnes_local h3]
  omega

private theorem updateAbShift_exact
    (value : PastaAsm.WideLimbs) (f g : Nat) (z : Int)
    (hv : value.Bounded)
    (hrep : (value.toNat5 : Int) ≡ z [ZMOD updateModulus])
    (hz : z.natAbs < 2^287) (hdiv : (2^31 : Int) ∣ z) :
    let out := updateAbShift value f g
    out.value.toNat = z.natAbs / 2^31 ∧
      out.f = word ((word f ^^^ (if z < 0 then 2^64 - 1 else 0)) +
        (if z < 0 then 1 else 0)) ∧
      out.g = word ((word g ^^^ (if z < 0 then 2^64 - 1 else 0)) +
        (if z < 0 then 1 else 0)) := by
  dsimp only
  obtain ⟨houtBound, q0, q1, q2, q3, mask, signBit, carry,
    hq0, hq1, hq2, hq3, hmaskDef, hbitDef, hcarry, hout, hf, hg⟩ :=
    updateAbShift_spec value f g hv (updateAbShift value f g) rfl
  have houtLt := Limbs.toNat_lt (updateAbShift value f g).value houtBound
  have hq0b : q0 < 2^64 := by rw [hq0]; exact shrd_lt _ _ _
  have hq1b : q1 < 2^64 := by rw [hq1]; exact shrd_lt _ _ _
  have hq2b : q2 < 2^64 := by rw [hq2]; exact shrd_lt _ _ _
  have hq3b : q3 < 2^64 := by rw [hq3]; exact shrd_lt _ _ _
  obtain hpos | hneg := signedFiveWord_cases hv hrep hz
  · obtain ⟨hzNonneg, hvalue⟩ := hpos
    have htopLow : value.l4 < 2^31 := by
      have htoLt : z.toNat < 2^287 := by
        rw [← Int.natAbs_of_nonneg hzNonneg]
        exact hz
      simp only [PastaAsm.WideLimbs.toNat5] at hvalue
      omega
    have hmask : mask = 0 := by
      rw [hmaskDef, sar63_eq_signMask hv.2.2.2.2.1, if_pos (by omega)]
    have hbit : signBit = 0 := by rw [hbitDef, hmask]; rfl
    have hshift := shrdChain31 value hv
    rw [← hq0, ← hq1, ← hq2, ← hq3, hvalue] at hshift
    have htopZero : value.l4 / 2^31 = 0 := Nat.div_eq_of_lt htopLow
    rw [htopZero, Nat.mul_zero, add_zero] at hshift
    rw [hmask, hbit, bitXor_zero_local hq0b, bitXor_zero_local hq1b,
      bitXor_zero_local hq2b, bitXor_zero_local hq3b, add_zero] at hout
    have hcarry0 : carry = 0 := by omega
    rw [hcarry0, Nat.mul_zero, add_zero] at hout
    rw [if_neg (not_lt.mpr hzNonneg)]
    have habsEq : z.natAbs = z.toNat := by
      have habsCast : (z.natAbs : Int) = z := Int.natAbs_of_nonneg hzNonneg
      have htoCast : (z.toNat : Int) = z := Int.toNat_of_nonneg hzNonneg
      exact_mod_cast habsCast.trans htoCast.symm
    exact ⟨by rw [habsEq]; exact hout.trans hshift,
      hf.trans (by simp only [hmask, hbit, if_neg (not_lt.mpr hzNonneg)]),
      hg.trans (by simp only [hmask, hbit, if_neg (not_lt.mpr hzNonneg)])⟩
  · obtain ⟨hzNeg, hvalue⟩ := hneg
    have habsLt287 : z.natAbs < 2^287 := hz
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
    have htopHigh : 2^63 ≤ value.l4 := by
      have hvalueLower : 2^320 - 2^287 ≤ value.toNat5 := by
        rw [hvalue]
        exact Nat.sub_le_sub_left (Nat.le_of_lt habsLt287) _
      have hdivLower := Nat.div_le_div_right (c := 2^256) hvalueLower
      rw [toNat5_div_top value hv] at hdivLower
      norm_num at hdivLower ⊢
      omega
    have hmask : mask = 2^64 - 1 := by
      rw [hmaskDef, sar63_eq_signMask hv.2.2.2.2.1, if_neg (by omega)]
    have hbit : signBit = 1 := by
      rw [hbitDef, hmask]
      norm_num [bitAnd, word, regMod]
    have hshift := shrdChain31 value hv
    rw [← hq0, ← hq1, ← hq2, ← hq3, hvalue] at hshift
    have hcomp := complementFour_eq q0 q1 q2 q3 hq0b hq1b hq2b hq3b
    rw [hmask, hbit] at hout
    have htotalFactor : 2^320 - z.natAbs = 2^31 * (2^289 - m) := by
      rw [habsMul]
      have hmLe : m ≤ 2^289 := hmLt.le.trans (by norm_num)
      have hp320 : 2^320 = 2^31 * 2^289 := by ring
      rw [hp320, Nat.mul_sub_left_distrib]
    have htotalDiv : (2^320 - z.natAbs) / 2^31 = 2^289 - m := by
      rw [htotalFactor, Nat.mul_comm, Nat.mul_div_left]
      positivity
    have htopDiv : value.l4 / 2^31 = 2^33 - 1 := by
      have htopUpper : value.l4 < 2^64 := hv.2.2.2.2.1
      have htopLower : 2^64 - 2^31 ≤ value.l4 := by
        have htop := toNat5_div_top value hv
        have hvalueLower : 2^320 - 2^287 ≤ value.toNat5 := by
          rw [hvalue]
          exact Nat.sub_le_sub_left (Nat.le_of_lt habsLt287) _
        have hdivLower := Nat.div_le_div_right (c := 2^256) hvalueLower
        rw [htop] at hdivLower
        norm_num at hdivLower ⊢
        exact hdivLower
      have hbase : (2^64 - 2^31) / 2^31 = 2^33 - 1 := by norm_num
      have hlowerDiv := Nat.div_le_div_right (c := 2^31) htopLower
      have hupperDiv : value.l4 / 2^31 < 2^33 := by
        exact Nat.div_lt_of_lt_mul (by
          have hp : 2^31 * 2^33 = 2^64 := by ring
          rw [hp]
          exact htopUpper)
      rw [hbase] at hlowerDiv
      omega
    have hlowShift : q0 + 2^64 * q1 + 2^128 * q2 + 2^192 * q3 =
        2^256 - m := by
      rw [htotalDiv, htopDiv] at hshift
      omega
    have hcarry0 : carry = 0 := by
      rw [hlowShift] at hcomp
      omega
    rw [hcarry0, Nat.mul_zero, add_zero] at hout
    simp only [if_pos hzNeg]
    refine ⟨?_, hf.trans (by rw [hmask, hbit]), hg.trans (by rw [hmask, hbit])⟩
    have hquot : z.natAbs / 2^31 = m := by
      rw [habsMul, Nat.mul_comm, Nat.mul_div_left]
      positivity
    rw [hquot]
    rw [hout]
    rw [hlowShift] at hcomp
    omega

private theorem signedWordRep_orient_word {w : Nat} {x z : Int}
    (hw : SignedWordRep w x) :
    SignedWordRep
      (word ((word w ^^^ (if z < 0 then 2^64 - 1 else 0)) +
        (if z < 0 then 1 else 0))) (orient z * x) := by
  rcases hw with ⟨hwBound, k, hk⟩
  constructor
  · exact word_lt _
  · unfold orient
    by_cases hz : z < 0
    · simp only [if_pos hz, neg_one_mul]
      by_cases hzero : w = 0
      · subst w
        refine ⟨-k, ?_⟩
        norm_num [word, regMod] at hk ⊢
        omega
      · have hwPos : 0 < w := Nat.pos_of_ne_zero hzero
        have hinner : word w ^^^ (2^64 - 1) = 2^64 - 1 - w := by
          rw [word_eq_of_lt hwBound, natXor_allOnes_local hwBound]
        have houter : word ((word w ^^^ (2^64 - 1)) + 1) = 2^64 - w := by
          rw [hinner]
          have heq : 2^64 - 1 - w + 1 = 2^64 - w := by omega
          rw [heq, word_eq_of_lt (by simp only [regMod]; omega)]
        rw [houter]
        refine ⟨1 - k, ?_⟩
        have hsubCast : ((2^64 - w : Nat) : Int) = (2^64 : Int) - w := by
          rw [Nat.cast_sub (Nat.le_of_lt hwBound)]
          norm_num
        rw [hsubCast]
        calc
          (2^64 : Int) - w - -x = 2^64 - (w - x) := by ring
          _ = 2^64 - 2^64 * k := by rw [hk]
          _ = 2^64 * (1 - k) := by ring
    · simp only [if_neg hz, one_mul, Nat.xor_zero, add_zero]
      rw [word_eq_of_lt hwBound, word_eq_of_lt hwBound]
      exact ⟨k, hk⟩

/-- Exact bridge for the actual `updateAb` routine order: Rust first forms the
five-word signed linear combination and then invokes the generated shift and
sign-correction helper.  This theorem retains the signed integer congruence of
the temporary while exposing every word and coefficient produced by the helper. -/
theorem updateAb_bridge
    (a b : Limbs) (f g : Nat) (x y : Int)
    (ha : a.Bounded) (hb : b.Bounded)
    (hf : SignedWordRep f x) (hg : SignedWordRep g y)
    (hx : x.natAbs < 2^63) (hy : y.natAbs < 2^63) :
    let temporary := invertLincomb5 (extendForUpdate a) (extendForUpdate b) f g
    let out := updateAb a b f g
    temporary.Bounded ∧
      temporary.toNat5 ≡ x * (a.toNat : Int) + y * (b.toNat : Int)
        [ZMOD updateModulus] ∧
      out.value.Bounded ∧
        ∃ q0 q1 q2 q3 mask signBit carry,
          q0 = shrd temporary.l0 temporary.l1 31 ∧
          q1 = shrd temporary.l1 temporary.l2 31 ∧
          q2 = shrd temporary.l2 temporary.l3 31 ∧
          q3 = shrd temporary.l3 temporary.l4 31 ∧
          mask = sar temporary.l4 63 ∧ signBit = bitAnd mask 1 ∧ carry ≤ 1 ∧
          out.value.toNat + 2^256 * carry =
            bitXor q0 mask + 2^64 * bitXor q1 mask +
              2^128 * bitXor q2 mask + 2^192 * bitXor q3 mask + signBit ∧
          out.f = word ((word f ^^^ mask) + signBit) ∧
          out.g = word ((word g ^^^ mask) + signBit) := by
  dsimp only
  let temporary := invertLincomb5 (extendForUpdate a) (extendForUpdate b) f g
  obtain ⟨htemp, hcong⟩ := invertLincomb5_signed_spec a b f g x y ha hb hf hg hx hy
  have hout : updateAb a b f g = updateAbShift temporary f g := by rfl
  obtain ⟨hvalue, hexact⟩ := updateAbShift_spec temporary f g htemp
    (updateAb a b f g) hout
  exact ⟨htemp, hcong, hvalue, hexact⟩

/-- The actual x86-64 `updateAb` composition returns the unique nonnegative
quotient of the signed row numerator by `2^31`, and applies the same numerator
orientation to both row coefficients. -/
theorem updateAb_exact
    (a b : Limbs) (f g : Nat) (x y : Int)
    (ha : a.Bounded) (hb : b.Bounded)
    (hf : SignedWordRep f x) (hg : SignedWordRep g y)
    (hx : x.natAbs < 2^63) (hy : y.natAbs < 2^63)
    (hnumerator : (x * (a.toNat : Int) + y * (b.toNat : Int)).natAbs < 2^287)
    (hdiv : (2^31 : Int) ∣ x * (a.toNat : Int) + y * (b.toNat : Int)) :
    let numerator := x * (a.toNat : Int) + y * (b.toNat : Int)
    let out := updateAb a b f g
    out.value.Bounded ∧
      out.value.toNat = numerator.natAbs / 2^31 ∧
      SignedWordRep out.f (orient numerator * x) ∧
      SignedWordRep out.g (orient numerator * y) := by
  dsimp only
  let temporary := invertLincomb5 (extendForUpdate a) (extendForUpdate b) f g
  obtain ⟨htemp, hcong⟩ := invertLincomb5_signed_spec a b f g x y ha hb hf hg hx hy
  have houtEq : updateAb a b f g = updateAbShift temporary f g := by rfl
  have hvalueBound := (updateAbShift_spec temporary f g htemp
    (updateAb a b f g) houtEq).1
  obtain ⟨hvalue, houtF, houtG⟩ := updateAbShift_exact temporary f g
    (x * (a.toNat : Int) + y * (b.toNat : Int)) htemp hcong hnumerator hdiv
  have horientF := signedWordRep_orient_word (z :=
    x * (a.toNat : Int) + y * (b.toNat : Int)) hf
  have horientG := signedWordRep_orient_word (z :=
    x * (a.toNat : Int) + y * (b.toNat : Int)) hg
  rw [← houtEq] at hvalue houtF houtG
  rw [← houtF] at horientF
  rw [← houtG] at horientG
  exact ⟨hvalueBound, hvalue, horientF, horientG⟩

end PastaAsm.X86_64
