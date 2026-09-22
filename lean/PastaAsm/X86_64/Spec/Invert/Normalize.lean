/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.Spec.Invert.Normalize
import PastaAsm.X86_64.Spec.Invert.Adjustment
import PastaAsm.X86_64.Compositions
import Mathlib.Tactic.NormNum

/-!
# Correctness of the x86-64 inversion coefficient normalization

This file connects the two generated normalization helpers and Rust's computation of `modx`
to the shared integer normalization model.
-/

set_option exponentiation.threshold 600

namespace PastaAsm.X86_64

open PastaAsm.Spec.Invert.Normalize

/-- Rust's limbwise computation of `modx` is bounded and exactly represents `2 * p` when
`p < 2^255`, so the top doubling carry is zero. -/
theorem doubledModulus_spec (modulus : Limbs) (hm : modulus.Bounded)
    (hp : modulus.toNat < 2^255) :
    (doubledModulus modulus).Bounded ∧
      (doubledModulus modulus).toNat = 2 * modulus.toNat := by
  obtain ⟨h0, h1, h2, h3⟩ := hm
  let d0 := word (2 * modulus.l0)
  let d1 := word (2 * modulus.l1 + modulus.l0 / 2^63)
  let d2 := word (2 * modulus.l2 + modulus.l1 / 2^63)
  let d3 := word (2 * modulus.l3 + modulus.l2 / 2^63)
  have b0 : d0 < 2^64 := word_lt _
  have b1 : d1 < 2^64 := word_lt _
  have b2 : d2 < 2^64 := word_lt _
  have b3 : d3 < 2^64 := word_lt _
  have q0 : (2 * modulus.l0) / 2^64 = modulus.l0 / 2^63 := by omega
  have q1 : (2 * modulus.l1 + modulus.l0 / 2^63) / 2^64 = modulus.l1 / 2^63 := by
    have hc : modulus.l0 / 2^63 ≤ 1 := by omega
    omega
  have q2 : (2 * modulus.l2 + modulus.l1 / 2^63) / 2^64 = modulus.l2 / 2^63 := by
    have hc : modulus.l1 / 2^63 ≤ 1 := by omega
    omega
  have q3 : (2 * modulus.l3 + modulus.l2 / 2^63) / 2^64 = 0 := by
    have hc : modulus.l2 / 2^63 ≤ 1 := by omega
    simp only [Limbs.toNat] at hp
    omega
  have e0 : d0 + 2^64 * (modulus.l0 / 2^63) = 2 * modulus.l0 := by
    dsimp only [d0, word, regMod]
    rw [← q0]
    exact Nat.mod_add_div _ _
  have e1 : d1 + 2^64 * (modulus.l1 / 2^63) =
      2 * modulus.l1 + modulus.l0 / 2^63 := by
    dsimp only [d1, word, regMod]
    rw [← q1]
    exact Nat.mod_add_div _ _
  have e2 : d2 + 2^64 * (modulus.l2 / 2^63) =
      2 * modulus.l2 + modulus.l1 / 2^63 := by
    dsimp only [d2, word, regMod]
    rw [← q2]
    exact Nat.mod_add_div _ _
  have e3 : d3 = 2 * modulus.l3 + modulus.l2 / 2^63 := by
    have h := Nat.mod_add_div (2 * modulus.l3 + modulus.l2 / 2^63) (2^64)
    dsimp only [d3, word, regMod]
    rw [q3, mul_zero, add_zero] at h
    exact h
  have hout : doubledModulus modulus = (⟨d0, d1, d2, d3⟩ : Limbs) := by rfl
  rw [hout]
  refine ⟨⟨b0, b1, b2, b3⟩, ?_⟩
  simp only [Limbs.toNat]
  clear * - e0 e1 e2 e3
  omega

private def highExcessValue (value : PastaAsm.WideLimbs) : Int :=
  (value.l4 : Int) + 2^64 * value.l5 + 2^128 * value.l6 + 2^192 * value.l7 +
    2^256 * (if value.l8 < 2^63 then (value.l8 : Int) else (value.l8 : Int) - 2^64)

private theorem toInt_split (value : PastaAsm.WideLimbs) :
    value.toInt = (value.low.toNat : Int) + (splitRadix : Int) * highExcessValue value := by
  unfold PastaAsm.WideLimbs.toInt PastaAsm.WideLimbs.toNat PastaAsm.WideLimbs.low
    Limbs.toNat highExcessValue splitRadix
  by_cases hsign : value.l8 < 2^63
  · rw [if_pos hsign, if_pos hsign]
    push_cast
    ring
  · rw [if_neg hsign, if_neg hsign]
    push_cast
    ring

private theorem low_lt_splitRadix (value : PastaAsm.WideLimbs) (hv : value.Bounded) :
    value.low.toNat < splitRadix := by
  exact Limbs.toNat_lt value.low ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1⟩

private theorem wideToNat_lt (value : PastaAsm.WideLimbs) (hv : value.Bounded) :
    value.toNat < 2^576 := by
  unfold PastaAsm.WideLimbs.toNat
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hv
  simp only [regMod] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  omega

private theorem bitXor_zero {x : Nat} (hx : x < 2^64) : bitXor x 0 = x := by
  unfold bitXor
  rw [word_eq_of_lt hx, word_zero, Nat.xor_zero, word_eq_of_lt hx]

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

private theorem bitXor_allOnes_local {x : Nat} (hx : x < 2^64) :
    bitXor x (2^64 - 1) = 2^64 - 1 - x := by
  unfold bitXor
  rw [word_eq_of_lt hx]
  have hall : 2^64 - 1 < regMod := by simp only [regMod]; omega
  rw [word_eq_of_lt hall, natXor_allOnes_local hx]
  exact word_eq_of_lt (by simp only [regMod]; omega)

private theorem addc_zero_zero {x : Nat} (hx : x < 2^64) : addc x 0 0 = (x, 0) := by
  have hx' : x < regMod := by simpa [regMod] using hx
  simp [addc, Nat.mod_eq_of_lt hx', Nat.div_eq_of_lt hx']

private theorem addcChain4 (lhs rhs : Limbs) :
    let s0 := addc lhs.l0 rhs.l0 0
    let s1 := addc lhs.l1 rhs.l1 s0.2
    let s2 := addc lhs.l2 rhs.l2 s1.2
    let s3 := addc lhs.l3 rhs.l3 s2.2
    (⟨s0.1, s1.1, s2.1, s3.1⟩ : Limbs).toNat + 2^256 * s3.2 =
      lhs.toNat + rhs.toNat := by
  dsimp only
  have h0 := addc_lin lhs.l0 rhs.l0 0
  have h1 := addc_lin lhs.l1 rhs.l1 (addc lhs.l0 rhs.l0 0).2
  have h2 := addc_lin lhs.l2 rhs.l2 (addc lhs.l1 rhs.l1 (addc lhs.l0 rhs.l0 0).2).2
  have h3 := addc_lin lhs.l3 rhs.l3
    (addc lhs.l2 rhs.l2 (addc lhs.l1 rhs.l1 (addc lhs.l0 rhs.l0 0).2).2).2
  simp only [Limbs.toNat]
  omega

private theorem negAdjustmentChain4 (modulus2 : Limbs) (hm : modulus2.Bounded)
    (hpos : 0 < modulus2.toNat) :
    let d0 := addc (bitXor modulus2.l0 (2^64 - 1)) 1 0
    let d1 := addc (bitXor modulus2.l1 (2^64 - 1)) 0 d0.2
    let d2 := addc (bitXor modulus2.l2 (2^64 - 1)) 0 d1.2
    let d3 := addc (bitXor modulus2.l3 (2^64 - 1)) 0 d2.2
    (⟨d0.1, d1.1, d2.1, d3.1⟩ : Limbs).toNat = 2^256 - modulus2.toNat := by
  let complement : Limbs :=
    ⟨bitXor modulus2.l0 (2^64 - 1), bitXor modulus2.l1 (2^64 - 1),
      bitXor modulus2.l2 (2^64 - 1), bitXor modulus2.l3 (2^64 - 1)⟩
  let one : Limbs := ⟨1, 0, 0, 0⟩
  have hsum := addcChain4 complement one
  have hcomplement : complement.toNat + modulus2.toNat + 1 = 2^256 := by
    simp only [complement, Limbs.toNat]
    rw [bitXor_allOnes_local hm.1, bitXor_allOnes_local hm.2.1,
      bitXor_allOnes_local hm.2.2.1, bitXor_allOnes_local hm.2.2.2]
    obtain ⟨hm0, hm1, hm2, hm3⟩ := hm
    omega
  have hsum' :
      let d0 := addc (bitXor modulus2.l0 (2^64 - 1)) 1 0
      let d1 := addc (bitXor modulus2.l1 (2^64 - 1)) 0 d0.2
      let d2 := addc (bitXor modulus2.l2 (2^64 - 1)) 0 d1.2
      let d3 := addc (bitXor modulus2.l3 (2^64 - 1)) 0 d2.2
      (⟨d0.1, d1.1, d2.1, d3.1⟩ : Limbs).toNat + 2^256 * d3.2 =
        complement.toNat + 1 := by
    simpa only [complement, one, Limbs.toNat, mul_zero, add_zero] using hsum
  dsimp only at hsum' ⊢
  have houtLt :
      (⟨(addc (bitXor modulus2.l0 (2^64 - 1)) 1 0).1,
          (addc (bitXor modulus2.l1 (2^64 - 1)) 0
            (addc (bitXor modulus2.l0 (2^64 - 1)) 1 0).2).1,
          (addc (bitXor modulus2.l2 (2^64 - 1)) 0
            (addc (bitXor modulus2.l1 (2^64 - 1)) 0
              (addc (bitXor modulus2.l0 (2^64 - 1)) 1 0).2).2).1,
          (addc (bitXor modulus2.l3 (2^64 - 1)) 0
            (addc (bitXor modulus2.l2 (2^64 - 1)) 0
              (addc (bitXor modulus2.l1 (2^64 - 1)) 0
                (addc (bitXor modulus2.l0 (2^64 - 1)) 1 0).2).2).2).1⟩ : Limbs).toNat < 2^256 := by
    apply Limbs.toNat_lt
    exact ⟨addc_value_lt _ _ _, addc_value_lt _ _ _, addc_value_lt _ _ _,
      addc_value_lt _ _ _⟩
  omega

/-- The helper interprets the all-ones excess word as signed `-1` and therefore
adds `modulus2`. -/
private theorem normalizeExcess_negOne_eq (high modulus2 : Limbs)
    (hm : modulus2.Bounded) :
    normalizeExcess high modulus2 (2^64 - 1) =
      let s0 := addc high.l0 modulus2.l0 0
      let s1 := addc high.l1 modulus2.l1 s0.2
      let s2 := addc high.l2 modulus2.l2 s1.2
      let s3 := addc high.l3 modulus2.l3 s2.2
      ⟨s0.1, s1.1, s2.1, s3.1⟩ := by
  have hneg : neg (2^64 - 1) = (1, 1) := by
    norm_num [neg, sbb, regMod]
  have hor : bitOr (2^64 - 1) 1 = 2^64 - 1 := by decide
  have hsar : sar 1 63 = 0 := by decide
  simp only [normalizeExcess, hneg, hor, hsar,
    bitAnd_allOnes hm.1, bitAnd_allOnes hm.2.1,
    bitAnd_allOnes hm.2.2.1, bitAnd_allOnes hm.2.2.2,
    bitXor_zero hm.1, bitXor_zero hm.2.1,
    bitXor_zero hm.2.2.1, bitXor_zero hm.2.2.2]
  norm_num [bitXor32, sbb, word32, regMod]
  simp only [addc_zero_zero hm.1, addc_zero_zero hm.2.1,
    addc_zero_zero hm.2.2.1, addc_zero_zero hm.2.2.2]
  simp

/-- The helper interprets excess word one as signed `+1` and therefore adds the
four-word XOR-plus-one encoding of `-modulus2`. -/
private theorem normalizeExcess_one_eq (high modulus2 : Limbs)
    (hm : modulus2.Bounded) :
    normalizeExcess high modulus2 1 =
      let d0 := addc (bitXor modulus2.l0 (2^64 - 1)) 1 0
      let d1 := addc (bitXor modulus2.l1 (2^64 - 1)) 0 d0.2
      let d2 := addc (bitXor modulus2.l2 (2^64 - 1)) 0 d1.2
      let d3 := addc (bitXor modulus2.l3 (2^64 - 1)) 0 d2.2
      let s0 := addc high.l0 d0.1 0
      let s1 := addc high.l1 d1.1 s0.2
      let s2 := addc high.l2 d2.1 s1.2
      let s3 := addc high.l3 d3.1 s2.2
      ⟨s0.1, s1.1, s2.1, s3.1⟩ := by
  have hneg : neg 1 = (2^64 - 1, 1) := by
    norm_num [neg, sbb, regMod]
  have hor : bitOr 1 (2^64 - 1) = 2^64 - 1 := by decide
  have hsar : sar (2^64 - 1) 63 = 2^64 - 1 := by decide
  simp only [normalizeExcess, hneg, hor, hsar,
    bitAnd_allOnes hm.1, bitAnd_allOnes hm.2.1,
    bitAnd_allOnes hm.2.2.1, bitAnd_allOnes hm.2.2.2]
  rfl

private theorem normalizeExcess_negOne_numeric (high modulus2 : Limbs)
    (hhigh : high.Bounded) (hm : modulus2.Bounded) :
    let out := normalizeExcess high modulus2 (2^64 - 1)
    out.Bounded ∧ ∃ carry, carry ≤ 1 ∧
      out.toNat + 2^256 * carry = high.toNat + modulus2.toNat := by
  dsimp only
  let s0 := addc high.l0 modulus2.l0 0
  let s1 := addc high.l1 modulus2.l1 s0.2
  let s2 := addc high.l2 modulus2.l2 s1.2
  let s3 := addc high.l3 modulus2.l3 s2.2
  have heq := normalizeExcess_negOne_eq high modulus2 hm
  have hsum := addcChain4 high modulus2
  obtain ⟨hout, _, _, _, _, _, _⟩ :=
    normalizeExcess_spec high modulus2 (2^64 - 1) hhigh hm (by omega) _ rfl
  refine ⟨hout, s3.2, addc_carry_le_one high.l3 modulus2.l3 s2.2
    hhigh.2.2.2 hm.2.2.2 ?_, ?_⟩
  · exact addc_carry_le_one high.l2 modulus2.l2 s1.2
      hhigh.2.2.1 hm.2.2.1
      (addc_carry_le_one high.l1 modulus2.l1 s0.2 hhigh.2.1 hm.2.1
        (addc_carry_le_one high.l0 modulus2.l0 0 hhigh.1 hm.1 (by decide)))
  · rw [heq]
    simpa only [s0, s1, s2, s3] using hsum

private theorem normalizeExcess_one_numeric (high modulus2 : Limbs)
    (hhigh : high.Bounded) (hm : modulus2.Bounded) (hpos : 0 < modulus2.toNat) :
    let out := normalizeExcess high modulus2 1
    out.Bounded ∧ ∃ carry, carry ≤ 1 ∧
      out.toNat + modulus2.toNat + 2^256 * carry = high.toNat + 2^256 := by
  dsimp only
  let d0 := addc (bitXor modulus2.l0 (2^64 - 1)) 1 0
  let d1 := addc (bitXor modulus2.l1 (2^64 - 1)) 0 d0.2
  let d2 := addc (bitXor modulus2.l2 (2^64 - 1)) 0 d1.2
  let d3 := addc (bitXor modulus2.l3 (2^64 - 1)) 0 d2.2
  let adjustment : Limbs := ⟨d0.1, d1.1, d2.1, d3.1⟩
  let s0 := addc high.l0 adjustment.l0 0
  let s1 := addc high.l1 adjustment.l1 s0.2
  let s2 := addc high.l2 adjustment.l2 s1.2
  let s3 := addc high.l3 adjustment.l3 s2.2
  have heq := normalizeExcess_one_eq high modulus2 hm
  have hadj : adjustment.toNat = 2^256 - modulus2.toNat := by
    simpa only [adjustment, d0, d1, d2, d3] using negAdjustmentChain4 modulus2 hm hpos
  have hadjBound : adjustment.Bounded :=
    ⟨addc_value_lt _ _ _, addc_value_lt _ _ _, addc_value_lt _ _ _, addc_value_lt _ _ _⟩
  have hsum := addcChain4 high adjustment
  obtain ⟨hout, _, _, _, _, _, _⟩ :=
    normalizeExcess_spec high modulus2 1 hhigh hm (by decide) _ rfl
  refine ⟨hout, s3.2, addc_carry_le_one high.l3 adjustment.l3 s2.2
    hhigh.2.2.2 hadjBound.2.2.2 ?_, ?_⟩
  · exact addc_carry_le_one high.l2 adjustment.l2 s1.2
      hhigh.2.2.1 hadjBound.2.2.1
      (addc_carry_le_one high.l1 adjustment.l1 s0.2 hhigh.2.1 hadjBound.2.1
        (addc_carry_le_one high.l0 adjustment.l0 0 hhigh.1 hadjBound.1 (by decide)))
  · have hsum' :
        (normalizeExcess high modulus2 1).toNat + 2^256 * s3.2 =
          high.toNat + adjustment.toNat := by
      rw [heq]
      simpa only [adjustment, s0, s1, s2, s3, d0, d1, d2, d3] using hsum
    rw [hadj] at hsum'
    have hmLt := Limbs.toNat_lt modulus2 hm
    omega

private theorem normalizeNegative_firstAdjustment
    (value : PastaAsm.WideLimbs) (modulus2 : Limbs) (p : Nat)
    (hv : value.Bounded) (hm : modulus2.Bounded)
    (hmodulus2 : modulus2.toNat = 2 * p)
    (hp : PastaSizedOdd p)
    (hlower : -(coefficientRadix : Int) ≤ value.toInt)
    (hupper : value.toInt < alignedModulus p) :
    let first := normalizeNegative value modulus2
    let high : Limbs := ⟨first.h0, first.h1, first.h2, first.h3⟩
    high.Bounded ∧
      first.excess = (if signedExcess (firstAdjustment p value.toInt) = -1
        then 2^64 - 1 else 0) ∧
      firstAdjustment p value.toInt =
        (value.low.toNat : Int) + (splitRadix : Int) *
          ((high.toNat : Int) + (splitRadix : Int) *
            signedExcess (firstAdjustment p value.toInt)) := by
  dsimp only
  let first := normalizeNegative value modulus2
  let high : Limbs := ⟨first.h0, first.h1, first.h2, first.h3⟩
  obtain ⟨bh0, bh1, bh2, bh3, be, carry, hcarry, heq⟩ :=
    normalizeNegative_spec value modulus2 hv hm first rfl
  have hhigh : high.Bounded := ⟨bh0, bh1, bh2, bh3⟩
  have heLt : first.excess < 2^64 := be
  have hlow := low_lt_splitRadix value hv
  have hsplit := toInt_split value
  have hMltNat := alignedModulus_lt_coefficientRadix hp
  have hMleNat := half_coefficientRadix_le_alignedModulus hp
  have hMlt : (alignedModulus p : Int) < coefficientRadix := by exact_mod_cast hMltNat
  have hMhalf : (2^511 : Int) ≤ alignedModulus p := by exact_mod_cast hMleNat
  have hmodAlign : (alignedModulus p : Int) = (splitRadix : Int) * modulus2.toNat := by
    rw [hmodulus2]
    unfold alignedModulus splitRadix
    push_cast
    ring
  have hhighNatLt := Limbs.toNat_lt high hhigh
  have htop : value.l8 < 2^64 := hv.2.2.2.2.2.2.2.2
  have hrest : value.l4 + 2^64 * value.l5 + 2^128 * value.l6 +
      2^192 * value.l7 < 2^256 := by
    obtain ⟨_, _, _, _, h4, h5, h6, h7, _⟩ := hv
    simp only [regMod] at h4 h5 h6 h7
    omega
  have hfirstRange :
      -(splitRadix : Int) <
          ((firstAdjustment p value.toInt - value.low.toNat) / splitRadix) ∧
        ((firstAdjustment p value.toInt - value.low.toNat) / splitRadix) < splitRadix := by
    have hlowInt : (0 : Int) ≤ value.low.toNat := by positivity
    have hlowLtInt : (value.low.toNat : Int) < splitRadix := by exact_mod_cast hlow
    have hMpos : (0 : Int) < alignedModulus p := by
      exact_mod_cast alignedModulus_pos hp
    unfold firstAdjustment
    split_ifs with hc
    · have hcUpper : value.toInt + alignedModulus p < alignedModulus p := by omega
      have hcLower : -(coefficientRadix : Int) + alignedModulus p ≤
          value.toInt + alignedModulus p := by omega
      have hcover : (coefficientRadix : Int) ≤ 2 * alignedModulus p := by
        exact_mod_cast coefficientRadix_le_two_alignedModulus hp
      unfold coefficientRadix splitRadix at *
      norm_num at *
      constructor <;> omega
    · have hc0 : 0 ≤ value.toInt := by omega
      unfold coefficientRadix splitRadix at *
      norm_num at *
      constructor <;> omega
  have heqInt :
      (high.toNat : Int) + (splitRadix : Int) * first.excess +
          (2^320 : Int) * carry =
        (value.l4 : Int) + 2^64 * value.l5 + 2^128 * value.l6 +
          2^192 * value.l7 + 2^256 * value.l8 +
          (if value.l8 < 2^63 then 0 else modulus2.toNat) := by
    dsimp only [high] at heq ⊢
    exact_mod_cast heq
  by_cases hsign : value.l8 < 2^63
  · have hcNonneg : 0 ≤ value.toInt := by
      unfold PastaAsm.WideLimbs.toInt
      rw [if_pos hsign]
      positivity
    have hfirst : firstAdjustment p value.toInt = value.toInt := by
      unfold firstAdjustment
      rw [if_neg (not_lt.mpr hcNonneg)]
    have hexcess : signedExcess (firstAdjustment p value.toInt) = 0 := by
      unfold signedExcess
      rw [if_neg (by omega), if_pos]
      rw [hfirst]
      exact hupper.trans hMlt
    have hquot : (firstAdjustment p value.toInt - value.low.toNat) / splitRadix =
        highExcessValue value := by
      rw [hfirst, hsplit]
      have hRpos : (0 : Int) < splitRadix := by positivity
      rw [add_sub_cancel_left, Int.mul_ediv_cancel_left _ (by omega)]
    rw [if_pos hsign] at heqInt
    have hquotNonneg : 0 ≤ highExcessValue value := by
      unfold highExcessValue
      rw [if_pos hsign]
      positivity
    have hquotLt : highExcessValue value < splitRadix := by
      rw [← hquot]
      exact hfirstRange.2
    have hcarry0 : carry = 0 := by
      dsimp only [high, splitRadix] at hhighNatLt heqInt hquotLt
      unfold highExcessValue at hquotLt
      rw [if_pos hsign] at hquotLt
      omega
    have he0 : first.excess = 0 := by
      dsimp only [high, splitRadix] at hhighNatLt heqInt hquotLt
      unfold highExcessValue at hquotLt
      rw [if_pos hsign] at hquotLt
      omega
    have hhighEq : (high.toNat : Int) = highExcessValue value := by
      dsimp only [high, splitRadix] at heqInt ⊢
      unfold highExcessValue
      rw [if_pos hsign]
      omega
    refine ⟨hhigh, ?_, ?_⟩
    · rw [hexcess, if_neg (by decide)]
      exact he0
    · rw [hexcess, hfirst, hsplit, hhighEq]
      simp
  · have hsignGe : 2^63 ≤ value.l8 := by omega
    have hcNeg : value.toInt < 0 := by
      unfold PastaAsm.WideLimbs.toInt
      rw [if_neg hsign]
      have hnat := wideToNat_lt value hv
      have hnatInt : (value.toNat : Int) < 2^576 := by exact_mod_cast hnat
      omega
    have hfirst : firstAdjustment p value.toInt = value.toInt + alignedModulus p := by
      unfold firstAdjustment
      rw [if_pos hcNeg]
    have hfirstDecomp : firstAdjustment p value.toInt =
        (value.low.toNat : Int) + (splitRadix : Int) *
          (highExcessValue value + modulus2.toNat) := by
      rw [hfirst, hsplit, hmodAlign]
      ring
    have hquot : (firstAdjustment p value.toInt - value.low.toNat) / splitRadix =
        highExcessValue value + modulus2.toNat := by
      rw [hfirstDecomp, add_sub_cancel_left]
      exact Int.mul_ediv_cancel_left _ (by positivity)
    rw [if_neg hsign] at heqInt
    by_cases hfirstNeg : firstAdjustment p value.toInt < 0
    · have hexcess : signedExcess (firstAdjustment p value.toInt) = -1 := by
        unfold signedExcess
        rw [if_pos hfirstNeg]
      have hquotNeg : highExcessValue value + modulus2.toNat < 0 := by
        by_contra hnot
        have hq0 : 0 ≤ highExcessValue value + modulus2.toNat := by omega
        have hlow0 : (0 : Int) ≤ value.low.toNat := by positivity
        rw [hfirstDecomp] at hfirstNeg
        dsimp only [splitRadix] at hfirstNeg
        omega
      have hquotLower : -(splitRadix : Int) < highExcessValue value + modulus2.toNat := by
        rw [← hquot]
        exact hfirstRange.1
      have hcarry0 : carry = 0 := by
        dsimp only [high, splitRadix] at hhighNatLt heqInt hquotNeg hquotLower
        unfold highExcessValue at hquotNeg hquotLower
        rw [if_neg hsign] at hquotNeg hquotLower
        omega
      have heNegOne : first.excess = 2^64 - 1 := by
        dsimp only [high, splitRadix] at hhighNatLt heqInt hquotNeg hquotLower
        unfold highExcessValue at hquotNeg hquotLower
        rw [if_neg hsign] at hquotNeg hquotLower
        omega
      have hhighEq : (high.toNat : Int) =
          highExcessValue value + modulus2.toNat + splitRadix := by
        dsimp only [high, splitRadix] at heqInt ⊢
        unfold highExcessValue
        rw [if_neg hsign]
        omega
      refine ⟨hhigh, ?_, ?_⟩
      · rw [hexcess, if_pos rfl]
        exact heNegOne
      · rw [hexcess, hfirstDecomp, hhighEq]
        ring
    · have hfirstNonneg : 0 ≤ firstAdjustment p value.toInt := by omega
      have hfirstLt : firstAdjustment p value.toInt < coefficientRadix := by
        rw [hfirst]
        omega
      have hexcess : signedExcess (firstAdjustment p value.toInt) = 0 := by
        unfold signedExcess
        rw [if_neg hfirstNeg, if_pos hfirstLt]
      have hfirstDecomp : firstAdjustment p value.toInt =
          (value.low.toNat : Int) + (splitRadix : Int) *
            (highExcessValue value + modulus2.toNat) := by
        rw [hfirst, hsplit, hmodAlign]
        ring
      have hquotNonneg : 0 ≤ highExcessValue value + modulus2.toNat := by
        by_contra hnot
        have hqNeg : highExcessValue value + modulus2.toNat ≤ -1 := by omega
        have hlowLtInt : (value.low.toNat : Int) < splitRadix := by exact_mod_cast hlow
        rw [hfirstDecomp] at hfirstNonneg
        dsimp only [splitRadix] at hfirstNonneg hlowLtInt
        omega
      have hquotLt : highExcessValue value + modulus2.toNat < splitRadix := by
        rw [← hquot]
        exact hfirstRange.2
      have hcarry1 : carry = 1 := by
        dsimp only [high, splitRadix] at hhighNatLt heqInt hquotNonneg hquotLt
        unfold highExcessValue at hquotNonneg hquotLt
        rw [if_neg hsign] at hquotNonneg hquotLt
        omega
      have he0 : first.excess = 0 := by
        dsimp only [high, splitRadix] at hhighNatLt heqInt hquotNonneg hquotLt
        unfold highExcessValue at hquotNonneg hquotLt
        rw [if_neg hsign] at hquotNonneg hquotLt
        omega
      have hhighEq : (high.toNat : Int) = highExcessValue value + modulus2.toNat := by
        dsimp only [high, splitRadix] at heqInt ⊢
        unfold highExcessValue
        rw [if_neg hsign]
        omega
      refine ⟨hhigh, ?_, ?_⟩
      · rw [hexcess, if_neg (by decide)]
        exact he0
      · rw [hexcess, hfirstDecomp, hhighEq]
        simp

/-- The actual x86-64 normalization composition exactly implements the shared
integer model. The low half is preserved and the returned high half is below
`2 * modulus`, as required by the following single reduction. -/
theorem normalizeCoefficient_spec
    (value : PastaAsm.WideLimbs) (modulus : Limbs)
    (hv : value.Bounded) (hm : modulus.Bounded)
    (hp : PastaSizedOdd modulus.toNat)
    (hlower : -(coefficientRadix : Int) ≤ value.toInt)
    (hupper : value.toInt < alignedModulus modulus.toNat) :
    let out := normalizeCoefficient value modulus
    out.1 = value.low ∧ out.2.Bounded ∧
      out.1.toNat + splitRadix * out.2.toNat =
        (normalize modulus.toNat value.toInt).toNat ∧
      out.2.toNat < 2 * modulus.toNat := by
  dsimp only
  let modulus2 := doubledModulus modulus
  let first := normalizeNegative value modulus2
  let high : Limbs := ⟨first.h0, first.h1, first.h2, first.h3⟩
  let outHigh := normalizeExcess high modulus2 first.excess
  have hpUpper : modulus.toNat < 2^255 := hp.2.2
  obtain ⟨hm2, hm2eq⟩ := doubledModulus_spec modulus hm hpUpper
  obtain ⟨hhigh, hexcessWord, hfirstRep⟩ := normalizeNegative_firstAdjustment
    value modulus2 modulus.toNat hv hm2 hm2eq hp hlower hupper
  obtain ⟨hnormNonneg, hnormUpper, _⟩ := normalize_spec hp hlower hupper
  have hfirstExcess := signedExcess_eq_neg_one_or_zero_or_one
    (firstAdjustment modulus.toNat value.toInt)
  have halignedLt : alignedModulus modulus.toNat < coefficientRadix := by
    unfold alignedModulus splitRadix coefficientRadix
    omega
  have hfirstLt : firstAdjustment modulus.toNat value.toInt < coefficientRadix := by
    have halignedLt' : (alignedModulus modulus.toNat : Int) < coefficientRadix := by
      exact_mod_cast halignedLt
    unfold firstAdjustment
    split_ifs <;> omega
  have hnotOne : signedExcess (firstAdjustment modulus.toNat value.toInt) ≠ 1 := by
    unfold signedExcess
    split_ifs <;> omega
  have hmod2pos : 0 < modulus2.toNat := by
    have hm2eq' : modulus2.toNat = 2 * modulus.toNat := hm2eq
    rw [hm2eq']
    have hpLower := hp.2.1
    omega
  have houtBounded : outHigh.Bounded := by
    rcases hfirstExcess with hneg | hzero | hone
    · have hexcessWord' := hexcessWord
      rw [hneg] at hexcessWord'
      dsimp only [outHigh]
      rw [hexcessWord']
      exact (normalizeExcess_negOne_numeric high modulus2 hhigh hm2).1
    · have hexcessWord' := hexcessWord
      rw [hzero] at hexcessWord'
      norm_num at hexcessWord'
      dsimp only [outHigh]
      rw [hexcessWord']
      exact (normalizeExcess_spec high modulus2 0 hhigh hm2 (by decide) _ rfl).1
    · exact (hnotOne hone).elim
  have hnormEq : normalize modulus.toNat value.toInt =
      (value.low.toNat : Int) + (splitRadix : Int) * (outHigh.toNat : Int) := by
    unfold normalize
    dsimp only
    unfold secondAdjustment
    rcases hfirstExcess with hneg | hzero | hone
    · rw [hneg]
      have hexcessWord' := hexcessWord
      rw [hneg] at hexcessWord'
      obtain ⟨_, carry, hcarry, houtConcrete⟩ :=
        normalizeExcess_negOne_numeric high modulus2 hhigh hm2
      have hout : outHigh.toNat + 2^256 * carry =
          high.toNat + modulus2.toNat := by
        dsimp only [outHigh]
        rw [hexcessWord']
        exact houtConcrete
      have houtLt := Limbs.toNat_lt outHigh houtBounded
      have hfirstRep' := hfirstRep
      rw [hneg] at hfirstRep'
      have hm2eq' : modulus2.toNat = 2 * modulus.toNat := by
        exact hm2eq
      rw [hm2eq'] at hout
      have hnormNonneg' : 0 ≤ firstAdjustment modulus.toNat value.toInt -
          (-1) * alignedModulus modulus.toNat := by
        simpa only [normalize, secondAdjustment, hneg] using hnormNonneg
      have hlowLt := low_lt_splitRadix value hv
      have hhighLt := Limbs.toNat_lt high hhigh
      have hfirstExpanded : firstAdjustment modulus.toNat value.toInt =
          (value.low.toNat : Int) + (splitRadix : Int) * high.toNat -
            (splitRadix : Int) * splitRadix := by
        calc
          firstAdjustment modulus.toNat value.toInt =
              (value.low.toNat : Int) + (splitRadix : Int) *
                ((high.toNat : Int) + (splitRadix : Int) * -1) := hfirstRep'
          _ = (value.low.toNat : Int) + (splitRadix : Int) * high.toNat -
                (splitRadix : Int) * splitRadix := by ring
      have hlargeInt : (2^256 : Int) * 2^256 ≤
          (value.low.toNat : Int) + 2^256 *
            ((high.toNat : Int) + 2 * modulus.toNat) := by
        rw [hfirstExpanded] at hnormNonneg'
        unfold alignedModulus splitRadix at hnormNonneg'
        push_cast at hnormNonneg'
        omega
      have hlargeNat : 2^256 * 2^256 ≤
          value.low.toNat + 2^256 * (high.toNat + 2 * modulus.toNat) := by
        exact_mod_cast hlargeInt
      have hsumGe : 2^256 ≤ high.toNat + 2 * modulus.toNat := by
        by_contra hnot
        have hsumLt : high.toNat + 2 * modulus.toNat < 2^256 :=
          Nat.lt_of_not_ge hnot
        have hstep : value.low.toNat + 2^256 * (high.toNat + 2 * modulus.toNat) <
            2^256 + 2^256 * (high.toNat + 2 * modulus.toNat) :=
          Nat.add_lt_add_right hlowLt _
        have hsucc : high.toNat + 2 * modulus.toNat + 1 ≤ 2^256 := by omega
        have hmul : 2^256 * (high.toNat + 2 * modulus.toNat + 1) ≤
            2^256 * 2^256 := Nat.mul_le_mul_left _ hsucc
        have hfactor : 2^256 + 2^256 * (high.toNat + 2 * modulus.toNat) =
            2^256 * (high.toNat + 2 * modulus.toNat + 1) := by ring
        rw [hfactor] at hstep
        exact (Nat.not_lt_of_ge hlargeNat) (hstep.trans_le hmul)
      have hcarry1 : carry = 1 := by omega
      rw [hcarry1] at hout
      norm_num only [Nat.mul_one] at hout
      have hout' : (outHigh.toNat : Int) + 2^256 =
          (high.toNat : Int) + 2 * modulus.toNat := by
        exact_mod_cast hout
      rw [hfirstRep']
      unfold alignedModulus splitRadix
      push_cast
      calc
        (value.low.toNat : Int) + 2 ^ 256 *
              ((high.toNat : Int) + 2 ^ 256 * -1) -
            -1 * (2 * (modulus.toNat : Int) * 2 ^ 256) =
            (value.low.toNat : Int) + 2^256 *
              (((high.toNat : Int) + 2 * modulus.toNat) - 2^256) := by ring
        _ = (value.low.toNat : Int) + 2^256 *
              (((outHigh.toNat : Int) + 2^256) - 2^256) := by rw [hout']
        _ = (value.low.toNat : Int) + 2^256 * outHigh.toNat := by ring
    · rw [hzero]
      simp only [zero_mul, sub_zero]
      have hexcessWord' := hexcessWord
      rw [hzero] at hexcessWord'
      norm_num at hexcessWord'
      obtain ⟨_, _, _, _, _, _, hzeroSpec⟩ :=
        normalizeExcess_spec high modulus2 0 hhigh hm2 (by decide) outHigh (by
          dsimp only [outHigh]
          rw [hexcessWord'])
      obtain ⟨_, houtEq⟩ := hzeroSpec rfl
      have hfirstRep' := hfirstRep
      rw [hzero] at hfirstRep'
      rw [houtEq]
      simpa using hfirstRep'
    · exact (hnotOne hone).elim
  have hdecomp : (normalize modulus.toNat value.toInt).toNat =
      value.low.toNat + splitRadix * outHigh.toNat := by
    have hnormCast : ((normalize modulus.toNat value.toInt).toNat : Int) =
        normalize modulus.toNat value.toInt := Int.toNat_of_nonneg hnormNonneg
    have hcast : ((normalize modulus.toNat value.toInt).toNat : Int) =
        (value.low.toNat + splitRadix * outHigh.toNat : Nat) := by
      rw [hnormCast, hnormEq]
      push_cast
      rfl
    exact_mod_cast hcast
  have hnormNatLt : (normalize modulus.toNat value.toInt).toNat <
      alignedModulus modulus.toNat := by
    rw [Int.toNat_lt hnormNonneg]
    exact_mod_cast hnormUpper
  have hhighDiv := split_high_lt_two_mul_modulus hnormNatLt
  have hdivEq : (normalize modulus.toNat value.toInt).toNat / splitRadix =
      outHigh.toNat := by
    rw [hdecomp, Nat.add_mul_div_left _ _ (by positivity),
      Nat.div_eq_of_lt (low_lt_splitRadix value hv), zero_add]
  refine ⟨rfl, houtBounded, ?_, ?_⟩
  · change value.low.toNat + splitRadix * outHigh.toNat =
      (normalize modulus.toNat value.toInt).toNat
    exact hdecomp.symm
  · change outHigh.toNat < 2 * modulus.toNat
    rw [hdivEq] at hhighDiv
    exact hhighDiv

end PastaAsm.X86_64
