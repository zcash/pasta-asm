/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.Spec.Invert.Normalize
import PastaAsm.AArch64.Spec.Invert.Divsteps.Core
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic

/-!
# Correctness of AArch64 inversion coefficient normalization

The generated instruction trace is connected here to the shared full-range integer normalizer.
-/

set_option exponentiation.threshold 600

namespace PastaAsm.AArch64

open Spec.Invert.Normalize

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

private theorem addChain5Value
    (a0 a1 a2 a3 a4 b0 b1 b2 b3 o0 o1 o2 o3 o4
      c0 c1 c2 c3 top : Nat)
    (h0 : o0 + 2^64 * c0 = a0 + b0)
    (h1 : o1 + 2^64 * c1 = a1 + b1 + c0)
    (h2 : o2 + 2^64 * c2 = a2 + b2 + c1)
    (h3 : o3 + 2^64 * c3 = a3 + b3 + c2)
    (h4 : o4 + 2^64 * top = a4 + c3) :
    o0 + 2^64 * o1 + 2^128 * o2 + 2^192 * o3 + 2^256 * o4 + 2^320 * top =
      a0 + 2^64 * a1 + 2^128 * a2 + 2^192 * a3 + 2^256 * a4 +
        (b0 + 2^64 * b1 + 2^128 * b2 + 2^192 * b3) := by
  omega

private theorem firstStageNegativeIdentity
    (low high firstHigh w8 w8out carry modulus2 : Nat)
    (hchain : firstHigh + 2^256 * w8out + 2^320 * carry =
      high + 2^256 * w8 + modulus2) :
    (low : Int) + 2^256 * ((high : Int) + 2^256 * ((w8 : Int) - 2^64)) +
        2^256 * modulus2 =
      (low : Int) + 2^256 * firstHigh +
        2^512 * ((w8out : Int) + 2^64 * carry - 2^64) := by
  have hchainInt :
      (firstHigh : Int) + 2^256 * w8out + 2^320 * carry =
        high + 2^256 * w8 + modulus2 := by
    have h := congrArg (fun n : Nat => (n : Int)) hchain
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h
  calc
    _ = (low : Int) + 2^256 *
        ((high : Int) + 2^256 * w8 + modulus2) - 2^576 := by ring
    _ = (low : Int) + 2^256 *
        ((firstHigh : Int) + 2^256 * w8out + 2^320 * carry) - 2^576 := by
      rw [hchainInt]
    _ = _ := by ring

private theorem firstStageNonnegativeIdentity
    (low high firstHigh w8 w8out carry : Nat)
    (hchain : firstHigh + 2^256 * w8out + 2^320 * carry = high + 2^256 * w8) :
    (low : Int) + 2^256 * ((high : Int) + 2^256 * (w8 : Int)) =
      (low : Int) + 2^256 * firstHigh +
        2^512 * ((w8out : Int) + 2^64 * carry) := by
  have hchainInt :
      (firstHigh : Int) + 2^256 * w8out + 2^320 * carry = high + 2^256 * w8 := by
    have h := congrArg (fun n : Nat => (n : Int)) hchain
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h
  calc
    _ = (low : Int) + 2^256 * ((high : Int) + 2^256 * w8) := by ring
    _ = (low : Int) + 2^256 *
        ((firstHigh : Int) + 2^256 * w8out + 2^320 * carry) := by
      rw [hchainInt]
    _ = _ := by ring

private theorem wrappedCarryIsOne
    (low first out correction carry : Nat)
    (hlow : low < 2^256) (hfirst : first < 2^256) (hout : out < 2^256)
    (hcorr : correction < 2^256)
    (hchain : out + 2^256 * carry = first + correction)
    (hnonneg : 0 ≤ (low : Int) + (2^256 : Int) *
      ((first : Int) + correction - 2^256)) : carry = 1 := by
  omega

private theorem zeroCarryOfBoundedSum
    (first out correction carry : Nat)
    (hfirst : first < 2^256) (hout : out < 2^256) (hcorr : correction < 2^256)
    (hchain : out + 2^256 * carry = first + correction)
    (hsum : first + correction < 2^256) : carry = 0 := by
  omega

private theorem complementedAddOneValue
    (a0 a1 a2 a3 o0 o1 o2 o3 c0 c1 c2 top : Nat)
    (ha0 : a0 < 2^64) (ha1 : a1 < 2^64) (ha2 : a2 < 2^64) (ha3 : a3 < 2^64)
    (hpos : 0 < a0 + 2^64 * a1 + 2^128 * a2 + 2^192 * a3)
    (hlt : a0 + 2^64 * a1 + 2^128 * a2 + 2^192 * a3 < 2^256)
    (h0 : o0 + 2^64 * c0 = (2^64 - 1 - a0) + 1)
    (h1 : o1 + 2^64 * c1 = (2^64 - 1 - a1) + c0)
    (h2 : o2 + 2^64 * c2 = (2^64 - 1 - a2) + c1)
    (h3 : o3 + 2^64 * top = (2^64 - 1 - a3) + c2) :
    o0 + 2^64 * o1 + 2^128 * o2 + 2^192 * o3 +
      (a0 + 2^64 * a1 + 2^128 * a2 + 2^192 * a3) = 2^256 := by
  omega

private theorem doubledModulusValue
    (p0 p1 m4 m5 m6 m7 : Nat)
    (em4 : m4 = p0 * 2^1 % 2^64)
    (em5 : m5 = 2 * p1 % 2^64 + p0 / 2^63)
    (em6 : m6 = p1 / 2^63) (em7 : m7 = 2^63) :
    m4 + 2^64 * m5 + 2^128 * m6 + 2^192 * m7 =
      2 * (p0 + 2^64 * p1 + 2^192 * 2^62) := by
  have h0 := Nat.mod_add_div (2 * p0) (2^64)
  have h1 := Nat.mod_add_div (2 * p1) (2^64)
  have q0 : (2 * p0) / 2^64 = p0 / 2^63 := by omega
  have q1 : (2 * p1) / 2^64 = p1 / 2^63 := by omega
  rw [q0] at h0
  rw [q1] at h1
  rw [em4, em5, em6, em7]
  omega

private theorem asr63_eq_signMask {a : Nat} (ha : a < 2^64) :
    asr a 63 = if a < 2^63 then 0 else 2^64 - 1 := by
  unfold asr PastaAsm.word PastaAsm.regMod
  rw [Nat.mod_eq_of_lt ha]
  by_cases h : a < 2^63
  · rw [if_pos h, if_pos h]
    exact Nat.div_eq_of_lt h
  · have hge : 2^63 ≤ a := by omega
    rw [if_neg h, if_neg h]
    have hq : a / 2^63 = 1 := by omega
    rw [hq]
    norm_num

private theorem eor_zero {a : Nat} (ha : a < 2^64) : eor a 0 = a := by
  unfold eor PastaAsm.word PastaAsm.regMod
  rw [Nat.xor_zero, Nat.mod_eq_of_lt ha]

private theorem natXor_allOnes {x : Nat} (hx : x < 2^64) :
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

private theorem eor_allOnes {a : Nat} (ha : a < 2^64) :
    eor a (2^64 - 1) = 2^64 - 1 - a := by
  unfold eor PastaAsm.word PastaAsm.regMod
  rw [natXor_allOnes ha]
  exact Nat.mod_eq_of_lt (by omega)

private theorem one_lor_of_even {n : Nat} (h : Even n) : 1 ||| n = n + 1 := by
  obtain ⟨k, rfl⟩ := h
  rw [show 1 = Nat.bit true 0 by rfl]
  rw [show k + k = Nat.bit false k by simp [Nat.bit, Nat.two_mul]]
  rw [Nat.lor_bit]
  simp [Nat.bit, Nat.two_mul]

private theorem orr_allOnes_one : orr (2^64 - 1) 1 = 2^64 - 1 := by
  norm_num [orr, PastaAsm.word, PastaAsm.regMod]
  decide

private theorem orr_one_allOnes : orr 1 (2^64 - 1) = 2^64 - 1 := by
  unfold orr
  rw [Nat.or_comm]
  exact orr_allOnes_one

private theorem limbsValue_lt (a0 a1 a2 a3 : Nat)
    (h0 : a0 < 2^64) (h1 : a1 < 2^64) (h2 : a2 < 2^64) (h3 : a3 < 2^64) :
    a0 + 2^64 * a1 + 2^128 * a2 + 2^192 * a3 < 2^256 := by
  omega

private theorem wideValue_lt
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Nat)
    (h0 : a0 < 2^64) (h1 : a1 < 2^64) (h2 : a2 < 2^64) (h3 : a3 < 2^64)
    (h4 : a4 < 2^64) (h5 : a5 < 2^64) (h6 : a6 < 2^64) (h7 : a7 < 2^64)
    (h8 : a8 < 2^64) :
    a0 + 2^64 * a1 + 2^128 * a2 + 2^192 * a3 + 2^256 * a4 +
        2^320 * a5 + 2^384 * a6 + 2^448 * a7 + 2^512 * a8 < 2^576 := by
  omega

private theorem orr_carry_shift (p0 p1 : Nat) (h0 : p0 < 2^64) :
    orr (lsr p0 63) (lsl p1 1) = 2 * p1 % 2^64 + p0 / 2^63 := by
  have hc : p0 / 2^63 = 0 ∨ p0 / 2^63 = 1 := by omega
  have heven : Even (2 * p1 % 2^64) := by
    have heq : 2 * p1 % 2^64 = 2 * (p1 % 2^63) := by
      rw [show 2^64 = 2 * 2^63 by norm_num, Nat.mul_mod_mul_left]
    rw [heq]
    exact even_two_mul _
  rcases hc with hc | hc
  · simp only [lsr, hc, orr, PastaAsm.word, Nat.zero_or, lsl]
    rw [Nat.mod_mod]
    congr 1
    omega
  · simp only [lsr, hc, orr, PastaAsm.word, lsl]
    have hshift : p1 * 2^1 % regMod = 2 * p1 % 2^64 := by
      simp only [PastaAsm.regMod]
      congr 1
      ring
    rw [hshift, one_lor_of_even heven]
    have hlt : 2 * p1 % 2^64 + 1 < 2^64 := by
      have heq : 2 * p1 % 2^64 = 2 * (p1 % 2^63) := by
        rw [show 2^64 = 2 * 2^63 by norm_num, Nat.mul_mod_mul_left]
      rw [heq]
      have := Nat.mod_lt p1 (by positivity : 0 < 2^63)
      omega
    rw [Nat.mod_eq_of_lt hlt]

-- BEGIN normalizeCoefficient_spec statement
/-- The actual AArch64 normalization block implements the shared normalizer on the complete
signed schedule range.  Its low half is unchanged; its high half is an arbitrary bounded
four-limb value (not generally below `2 * modulus`). -/
theorem normalizeCoefficient_spec
    (value : PastaAsm.WideLimbs) (modulus : Limbs)
    (hv : value.Bounded) (hm : modulus.Bounded)
    (hshape : modulus.l2 = 0 ∧ modulus.l3 = 2^62)
    (hp : PastaSizedOdd modulus.toNat)
    (hlower : -(coefficientRadix : Int) ≤ value.toInt)
    (hupper : value.toInt ≤ coefficientRadix) :
    ∀ r, r = normalizeCoefficient value modulus →
      r.low = value.low ∧ r.high.Bounded ∧
        r.low.toNat + splitRadix * r.high.toNat =
          (normalize modulus.toNat value.toInt).toNat ∧
        r.high.toNat < splitRadix := by
  intro r hr
-- END normalizeCoefficient_spec statement
  -- generated skeleton for `normalizeCoefficient`: do not edit between the annotations
  unfold normalizeCoefficient at hr
  lift_lets -merge at hr
  -- p0: argument
  extract_lets -merge +onlyGivenNames p0 at hr
  have e_p0 : p0 = modulus.l0 := rfl
  clear_value p0
  have b_p0 : p0 < 2^64 := by rw [e_p0]; exact hm.1
  -- p1: argument
  extract_lets -merge +onlyGivenNames p1 at hr
  have e_p1 : p1 = modulus.l1 := rfl
  clear_value p1
  have b_p1 : p1 < 2^64 := by rw [e_p1]; exact hm.2.1
  -- w4: argument
  extract_lets -merge +onlyGivenNames w4 at hr
  have e_w4 : w4 = value.l4 := rfl
  clear_value w4
  have b_w4 : w4 < 2^64 := by rw [e_w4]; exact hv.2.2.2.2.1
  -- w5: argument
  extract_lets -merge +onlyGivenNames w5 at hr
  have e_w5 : w5 = value.l5 := rfl
  clear_value w5
  have b_w5 : w5 < 2^64 := by rw [e_w5]; exact hv.2.2.2.2.2.1
  -- w6: argument
  extract_lets -merge +onlyGivenNames w6 at hr
  have e_w6 : w6 = value.l6 := rfl
  clear_value w6
  have b_w6 : w6 < 2^64 := by rw [e_w6]; exact hv.2.2.2.2.2.2.1
  -- w7: argument
  extract_lets -merge +onlyGivenNames w7 at hr
  have e_w7 : w7 = value.l7 := rfl
  clear_value w7
  have b_w7 : w7 < 2^64 := by rw [e_w7]; exact hv.2.2.2.2.2.2.2.1
  -- w8: argument
  extract_lets -merge +onlyGivenNames w8 at hr
  have e_w8 : w8 = value.l8 := rfl
  clear_value w8
  have b_w8 : w8 < 2^64 := by rw [e_w8]; exact hv.2.2.2.2.2.2.2.2
  -- sign: asr sign,w8,#63
  extract_lets -merge +onlyGivenNames sign at hr
  have e_sign : sign = asr w8 63 := rfl
  clear_value sign
  have b_sign : sign < 2^64 := by rw [e_sign]; exact asr_lt _ _
  -- m4: lsl m4,p0,#1
  extract_lets -merge +onlyGivenNames m4 at hr
  have e_m4 : m4 = p0 * 2^1 % 2^64 := rfl
  clear_value m4
  have b_m4 : m4 < 2^64 := by rw [e_m4]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- tmp: lsr tmp,p0,#63
  extract_lets -merge +onlyGivenNames tmp at hr
  have e_tmp : tmp = lsr p0 63 := rfl
  clear_value tmp
  have b_tmp : tmp < 2^64 := by rw [e_tmp]; exact lt_of_le_of_lt (Nat.div_le_self _ _) b_p0
  -- m5: orr m5,tmp,p1,lsl #1
  extract_lets -merge +onlyGivenNames m5 at hr
  have e_m5 : m5 = orr tmp (lsl p1 1) := rfl
  clear_value m5
  have b_m5 : m5 < 2^64 := by rw [e_m5]; exact orr_lt _ _
  -- m6: lsr m6,p1,#63
  extract_lets -merge +onlyGivenNames m6 at hr
  have e_m6 : m6 = lsr p1 63 := rfl
  clear_value m6
  have b_m6 : m6 < 2^64 := by rw [e_m6]; exact lt_of_le_of_lt (Nat.div_le_self _ _) b_p1
  -- m7: mov m7,#0x8000000000000000
  extract_lets -merge +onlyGivenNames m7 at hr
  have e_m7 : m7 = 9223372036854775808 := rfl
  clear_value m7
  have b_m7 : m7 < 2^64 := by rw [e_m7]; decide
  -- tmp_1: and tmp,m4,sign
  extract_lets -merge +onlyGivenNames tmp_1 at hr
  have e_tmp_1 : tmp_1 = bitAnd m4 sign := rfl
  clear_value tmp_1
  have b_tmp_1 : tmp_1 < 2^64 := by rw [e_tmp_1]; exact bitAnd_lt _ _
  -- w4_1: adds w4,w4,tmp
  extract_lets -merge +onlyGivenNames s w4_1 c at hr
  have e_w4_1 : w4_1 = (w4 + tmp_1 + 0) % 2^64 := rfl
  have e_c : c = (w4 + tmp_1 + 0) / 2^64 := rfl
  clear_value s w4_1 c
  have l_w4_1 : w4_1 + 2^64 * c = w4 + tmp_1 + 0 := by
    rw [e_w4_1, e_c]; exact Nat.mod_add_div _ _
  have b_w4_1 : w4_1 < 2^64 := by rw [e_w4_1]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c : c ≤ 1 := by
    rw [e_c]; exact addc_carry_le_one w4 tmp_1 0 b_w4 b_tmp_1 (by decide)
  clear e_w4_1 e_c
  -- tmp_2: and tmp,m5,sign
  extract_lets -merge +onlyGivenNames tmp_2 at hr
  have e_tmp_2 : tmp_2 = bitAnd m5 sign := rfl
  clear_value tmp_2
  have b_tmp_2 : tmp_2 < 2^64 := by rw [e_tmp_2]; exact bitAnd_lt _ _
  -- w5_1: adcs w5,w5,tmp
  extract_lets -merge +onlyGivenNames s_1 w5_1 c_1 at hr
  have e_w5_1 : w5_1 = (w5 + tmp_2 + c) % 2^64 := rfl
  have e_c_1 : c_1 = (w5 + tmp_2 + c) / 2^64 := rfl
  clear_value s_1 w5_1 c_1
  have l_w5_1 : w5_1 + 2^64 * c_1 = w5 + tmp_2 + c := by
    rw [e_w5_1, e_c_1]; exact Nat.mod_add_div _ _
  have b_w5_1 : w5_1 < 2^64 := by rw [e_w5_1]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_1 : c_1 ≤ 1 := by
    rw [e_c_1]; exact addc_carry_le_one w5 tmp_2 c b_w5 b_tmp_2 b_c
  clear e_w5_1 e_c_1
  -- tmp_3: and tmp,m6,sign
  extract_lets -merge +onlyGivenNames tmp_3 at hr
  have e_tmp_3 : tmp_3 = bitAnd m6 sign := rfl
  clear_value tmp_3
  have b_tmp_3 : tmp_3 < 2^64 := by rw [e_tmp_3]; exact bitAnd_lt _ _
  -- w6_1: adcs w6,w6,tmp
  extract_lets -merge +onlyGivenNames s_2 w6_1 c_2 at hr
  have e_w6_1 : w6_1 = (w6 + tmp_3 + c_1) % 2^64 := rfl
  have e_c_2 : c_2 = (w6 + tmp_3 + c_1) / 2^64 := rfl
  clear_value s_2 w6_1 c_2
  have l_w6_1 : w6_1 + 2^64 * c_2 = w6 + tmp_3 + c_1 := by
    rw [e_w6_1, e_c_2]; exact Nat.mod_add_div _ _
  have b_w6_1 : w6_1 < 2^64 := by rw [e_w6_1]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_2 : c_2 ≤ 1 := by
    rw [e_c_2]; exact addc_carry_le_one w6 tmp_3 c_1 b_w6 b_tmp_3 b_c_1
  clear e_w6_1 e_c_2
  -- tmp_4: and tmp,m7,sign
  extract_lets -merge +onlyGivenNames tmp_4 at hr
  have e_tmp_4 : tmp_4 = bitAnd m7 sign := rfl
  clear_value tmp_4
  have b_tmp_4 : tmp_4 < 2^64 := by rw [e_tmp_4]; exact bitAnd_lt _ _
  -- w7_1: adcs w7,w7,tmp
  extract_lets -merge +onlyGivenNames s_3 w7_1 c_3 at hr
  have e_w7_1 : w7_1 = (w7 + tmp_4 + c_2) % 2^64 := rfl
  have e_c_3 : c_3 = (w7 + tmp_4 + c_2) / 2^64 := rfl
  clear_value s_3 w7_1 c_3
  have l_w7_1 : w7_1 + 2^64 * c_3 = w7 + tmp_4 + c_2 := by
    rw [e_w7_1, e_c_3]; exact Nat.mod_add_div _ _
  have b_w7_1 : w7_1 < 2^64 := by rw [e_w7_1]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_3 : c_3 ≤ 1 := by
    rw [e_c_3]; exact addc_carry_le_one w7 tmp_4 c_2 b_w7 b_tmp_4 b_c_2
  clear e_w7_1 e_c_3
  -- w8_1: adc w8,w8,xzr
  extract_lets -merge +onlyGivenNames w8_1 at hr
  have e_w8_1 : w8_1 = (w8 + 0 + c_3) % 2^64 := rfl
  clear_value w8_1
  have b_w8_1 : w8_1 < 2^64 := by rw [e_w8_1]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨k_w8_1, b_k_w8_1, l_w8_1⟩ :
      ∃ k, k ≤ 1 ∧ w8_1 + 2^64 * k = w8 + 0 + c_3 :=
    ⟨(w8 + 0 + c_3) / 2^64, addc_carry_le_one w8 0 c_3 b_w8 (by decide) b_c_3,
      by rw [e_w8_1]; exact Nat.mod_add_div _ _⟩
  clear e_w8_1
  -- sign_1: neg sign,w8
  extract_lets -merge +onlyGivenNames sign_1 at hr
  have e_sign_1 : sign_1 = neg w8_1 := rfl
  clear_value sign_1
  have b_sign_1 : sign_1 < 2^64 := by rw [e_sign_1]; exact neg_lt _
  -- excess: orr excess,w8,sign
  extract_lets -merge +onlyGivenNames excess at hr
  have e_excess : excess = orr w8_1 sign_1 := rfl
  clear_value excess
  have b_excess : excess < 2^64 := by rw [e_excess]; exact orr_lt _ _
  -- sign_2: asr sign,sign,#63
  extract_lets -merge +onlyGivenNames sign_2 at hr
  have e_sign_2 : sign_2 = asr sign_1 63 := rfl
  clear_value sign_2
  have b_sign_2 : sign_2 < 2^64 := by rw [e_sign_2]; exact asr_lt _ _
  -- m4_1: and m4,m4,excess
  extract_lets -merge +onlyGivenNames m4_1 at hr
  have e_m4_1 : m4_1 = bitAnd m4 excess := rfl
  clear_value m4_1
  have b_m4_1 : m4_1 < 2^64 := by rw [e_m4_1]; exact bitAnd_lt _ _
  -- m5_1: and m5,m5,excess
  extract_lets -merge +onlyGivenNames m5_1 at hr
  have e_m5_1 : m5_1 = bitAnd m5 excess := rfl
  clear_value m5_1
  have b_m5_1 : m5_1 < 2^64 := by rw [e_m5_1]; exact bitAnd_lt _ _
  -- m6_1: and m6,m6,excess
  extract_lets -merge +onlyGivenNames m6_1 at hr
  have e_m6_1 : m6_1 = bitAnd m6 excess := rfl
  clear_value m6_1
  have b_m6_1 : m6_1 < 2^64 := by rw [e_m6_1]; exact bitAnd_lt _ _
  -- m7_1: and m7,m7,excess
  extract_lets -merge +onlyGivenNames m7_1 at hr
  have e_m7_1 : m7_1 = bitAnd m7 excess := rfl
  clear_value m7_1
  have b_m7_1 : m7_1 < 2^64 := by rw [e_m7_1]; exact bitAnd_lt _ _
  -- m4_2: eor m4,m4,sign
  extract_lets -merge +onlyGivenNames m4_2 at hr
  have e_m4_2 : m4_2 = eor m4_1 sign_2 := rfl
  clear_value m4_2
  have b_m4_2 : m4_2 < 2^64 := by rw [e_m4_2]; exact eor_lt _ _
  -- m5_2: eor m5,m5,sign
  extract_lets -merge +onlyGivenNames m5_2 at hr
  have e_m5_2 : m5_2 = eor m5_1 sign_2 := rfl
  clear_value m5_2
  have b_m5_2 : m5_2 < 2^64 := by rw [e_m5_2]; exact eor_lt _ _
  -- m4_3: adds m4,m4,sign,lsr #63
  extract_lets -merge +onlyGivenNames s_4 m4_3 c_4 at hr
  have e_m4_3 : m4_3 = (m4_2 + (lsr sign_2 63) + 0) % 2^64 := rfl
  have e_c_4 : c_4 = (m4_2 + (lsr sign_2 63) + 0) / 2^64 := rfl
  clear_value s_4 m4_3 c_4
  have l_m4_3 : m4_3 + 2^64 * c_4 = m4_2 + (lsr sign_2 63) + 0 := by
    rw [e_m4_3, e_c_4]; exact Nat.mod_add_div _ _
  have b_m4_3 : m4_3 < 2^64 := by rw [e_m4_3]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_4 : c_4 ≤ 1 := by
    rw [e_c_4]; exact addc_carry_le_one m4_2 (lsr sign_2 63) 0 b_m4_2 (lt_of_le_of_lt (Nat.div_le_self _ _) b_sign_2) (by decide)
  clear e_m4_3 e_c_4
  -- m6_2: eor m6,m6,sign
  extract_lets -merge +onlyGivenNames m6_2 at hr
  have e_m6_2 : m6_2 = eor m6_1 sign_2 := rfl
  clear_value m6_2
  have b_m6_2 : m6_2 < 2^64 := by rw [e_m6_2]; exact eor_lt _ _
  -- m5_3: adcs m5,m5,xzr
  extract_lets -merge +onlyGivenNames s_5 m5_3 c_5 at hr
  have e_m5_3 : m5_3 = (m5_2 + 0 + c_4) % 2^64 := rfl
  have e_c_5 : c_5 = (m5_2 + 0 + c_4) / 2^64 := rfl
  clear_value s_5 m5_3 c_5
  have l_m5_3 : m5_3 + 2^64 * c_5 = m5_2 + 0 + c_4 := by
    rw [e_m5_3, e_c_5]; exact Nat.mod_add_div _ _
  have b_m5_3 : m5_3 < 2^64 := by rw [e_m5_3]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_5 : c_5 ≤ 1 := by
    rw [e_c_5]; exact addc_carry_le_one m5_2 0 c_4 b_m5_2 (by decide) b_c_4
  clear e_m5_3 e_c_5
  -- m7_2: eor m7,m7,sign
  extract_lets -merge +onlyGivenNames m7_2 at hr
  have e_m7_2 : m7_2 = eor m7_1 sign_2 := rfl
  clear_value m7_2
  have b_m7_2 : m7_2 < 2^64 := by rw [e_m7_2]; exact eor_lt _ _
  -- m6_3: adcs m6,m6,xzr
  extract_lets -merge +onlyGivenNames s_6 m6_3 c_6 at hr
  have e_m6_3 : m6_3 = (m6_2 + 0 + c_5) % 2^64 := rfl
  have e_c_6 : c_6 = (m6_2 + 0 + c_5) / 2^64 := rfl
  clear_value s_6 m6_3 c_6
  have l_m6_3 : m6_3 + 2^64 * c_6 = m6_2 + 0 + c_5 := by
    rw [e_m6_3, e_c_6]; exact Nat.mod_add_div _ _
  have b_m6_3 : m6_3 < 2^64 := by rw [e_m6_3]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_6 : c_6 ≤ 1 := by
    rw [e_c_6]; exact addc_carry_le_one m6_2 0 c_5 b_m6_2 (by decide) b_c_5
  clear e_m6_3 e_c_6
  -- m7_3: adc m7,m7,xzr
  extract_lets -merge +onlyGivenNames m7_3 at hr
  have e_m7_3 : m7_3 = (m7_2 + 0 + c_6) % 2^64 := rfl
  clear_value m7_3
  have b_m7_3 : m7_3 < 2^64 := by rw [e_m7_3]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨k_m7_3, b_k_m7_3, l_m7_3⟩ :
      ∃ k, k ≤ 1 ∧ m7_3 + 2^64 * k = m7_2 + 0 + c_6 :=
    ⟨(m7_2 + 0 + c_6) / 2^64, addc_carry_le_one m7_2 0 c_6 b_m7_2 (by decide) b_c_6,
      by rw [e_m7_3]; exact Nat.mod_add_div _ _⟩
  clear e_m7_3
  -- w4_2: adds w4,w4,m4
  extract_lets -merge +onlyGivenNames s_7 w4_2 c_7 at hr
  have e_w4_2 : w4_2 = (w4_1 + m4_3 + 0) % 2^64 := rfl
  have e_c_7 : c_7 = (w4_1 + m4_3 + 0) / 2^64 := rfl
  clear_value s_7 w4_2 c_7
  have l_w4_2 : w4_2 + 2^64 * c_7 = w4_1 + m4_3 + 0 := by
    rw [e_w4_2, e_c_7]; exact Nat.mod_add_div _ _
  have b_w4_2 : w4_2 < 2^64 := by rw [e_w4_2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_7 : c_7 ≤ 1 := by
    rw [e_c_7]; exact addc_carry_le_one w4_1 m4_3 0 b_w4_1 b_m4_3 (by decide)
  clear e_w4_2 e_c_7
  -- w5_2: adcs w5,w5,m5
  extract_lets -merge +onlyGivenNames s_8 w5_2 c_8 at hr
  have e_w5_2 : w5_2 = (w5_1 + m5_3 + c_7) % 2^64 := rfl
  have e_c_8 : c_8 = (w5_1 + m5_3 + c_7) / 2^64 := rfl
  clear_value s_8 w5_2 c_8
  have l_w5_2 : w5_2 + 2^64 * c_8 = w5_1 + m5_3 + c_7 := by
    rw [e_w5_2, e_c_8]; exact Nat.mod_add_div _ _
  have b_w5_2 : w5_2 < 2^64 := by rw [e_w5_2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_8 : c_8 ≤ 1 := by
    rw [e_c_8]; exact addc_carry_le_one w5_1 m5_3 c_7 b_w5_1 b_m5_3 b_c_7
  clear e_w5_2 e_c_8
  -- w6_2: adcs w6,w6,m6
  extract_lets -merge +onlyGivenNames s_9 w6_2 c_9 at hr
  have e_w6_2 : w6_2 = (w6_1 + m6_3 + c_8) % 2^64 := rfl
  have e_c_9 : c_9 = (w6_1 + m6_3 + c_8) / 2^64 := rfl
  clear_value s_9 w6_2 c_9
  have l_w6_2 : w6_2 + 2^64 * c_9 = w6_1 + m6_3 + c_8 := by
    rw [e_w6_2, e_c_9]; exact Nat.mod_add_div _ _
  have b_w6_2 : w6_2 < 2^64 := by rw [e_w6_2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_9 : c_9 ≤ 1 := by
    rw [e_c_9]; exact addc_carry_le_one w6_1 m6_3 c_8 b_w6_1 b_m6_3 b_c_8
  clear e_w6_2 e_c_9
  -- w7_2: adc w7,w7,m7
  extract_lets -merge +onlyGivenNames w7_2 at hr
  have e_w7_2 : w7_2 = (w7_1 + m7_3 + c_9) % 2^64 := rfl
  clear_value w7_2
  have b_w7_2 : w7_2 < 2^64 := by rw [e_w7_2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨k_w7_2, b_k_w7_2, l_w7_2⟩ :
      ∃ k, k ≤ 1 ∧ w7_2 + 2^64 * k = w7_1 + m7_3 + c_9 :=
    ⟨(w7_1 + m7_3 + c_9) / 2^64, addc_carry_le_one w7_1 m7_3 c_9 b_w7_1 b_m7_3 b_c_9,
      by rw [e_w7_2]; exact Nat.mod_add_div _ _⟩
  clear e_w7_2
  subst hr
  -- BEGIN normalizeCoefficient conclusion
  have hlowBound : value.low.toNat < splitRadix := by
    exact Limbs.toNat_lt value.low ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1⟩
  have hwideNat : value.toNat < 2^576 := by
    exact wideValue_lt value.l0 value.l1 value.l2 value.l3 value.l4 value.l5 value.l6
      value.l7 value.l8 hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2.1
      hv.2.2.2.2.2.1 hv.2.2.2.2.2.2.1 hv.2.2.2.2.2.2.2.1 hv.2.2.2.2.2.2.2.2
  have hhighBound :
      w4 + 2^64 * w5 + 2^128 * w6 + 2^192 * w7 < splitRadix := by
    exact limbsValue_lt w4 w5 w6 w7 b_w4 b_w5 b_w6 b_w7
  have hfirstHighBound :
      w4_1 + 2^64 * w5_1 + 2^128 * w6_1 + 2^192 * w7_1 < splitRadix := by
    exact limbsValue_lt w4_1 w5_1 w6_1 w7_1 b_w4_1 b_w5_1 b_w6_1 b_w7_1
  have houtBound :
      w4_2 + 2^64 * w5_2 + 2^128 * w6_2 + 2^192 * w7_2 < splitRadix := by
    exact limbsValue_lt w4_2 w5_2 w6_2 w7_2 b_w4_2 b_w5_2 b_w6_2 b_w7_2
  have hm5 : m5 = 2 * p1 % 2^64 + p0 / 2^63 := by
    rw [e_m5, e_tmp]
    exact orr_carry_shift p0 p1 b_p0
  have hdouble :
      m4 + 2^64 * m5 + 2^128 * m6 + 2^192 * m7 = 2 * modulus.toNat := by
    have hpacked := doubledModulusValue p0 p1 m4 m5 m6 m7 e_m4 hm5
      (by simp only [e_m6, lsr]) (by rw [e_m7]; norm_num)
    simpa only [Limbs.toNat, hshape.1, hshape.2, e_p0, e_p1, mul_zero, add_zero]
      using hpacked
  have hdoubleInt :
      (m4 : Int) + 2^64 * m5 + 2^128 * m6 + 2^192 * m7 =
        2 * modulus.toNat := by
    have h := congrArg (fun n : Nat => (n : Int)) hdouble
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h
  have hdoublePos : 0 < m4 + 2^64 * m5 + 2^128 * m6 + 2^192 * m7 := by
    rw [hdouble]
    unfold PastaSizedOdd at hp
    omega
  have hdoubleLt :
      m4 + 2^64 * m5 + 2^128 * m6 + 2^192 * m7 < splitRadix := by
    rw [hdouble]
    unfold PastaSizedOdd at hp
    dsimp only [splitRadix]
    omega
  have hsignInitial : sign = if w8 < 2^63 then 0 else 2^64 - 1 := by
    rw [e_sign]
    exact asr63_eq_signMask b_w8
  have htmp1 : tmp_1 = if w8 < 2^63 then 0 else m4 := by
    by_cases h : w8 < 2^63
    · rw [if_pos h, e_tmp_1, hsignInitial, if_pos h, and_zero]
    · rw [if_neg h, e_tmp_1, hsignInitial, if_neg h, and_allOnes m4 b_m4]
  have htmp2 : tmp_2 = if w8 < 2^63 then 0 else m5 := by
    by_cases h : w8 < 2^63
    · rw [if_pos h, e_tmp_2, hsignInitial, if_pos h, and_zero]
    · rw [if_neg h, e_tmp_2, hsignInitial, if_neg h, and_allOnes m5 b_m5]
  have htmp3 : tmp_3 = if w8 < 2^63 then 0 else m6 := by
    by_cases h : w8 < 2^63
    · rw [if_pos h, e_tmp_3, hsignInitial, if_pos h, and_zero]
    · rw [if_neg h, e_tmp_3, hsignInitial, if_neg h, and_allOnes m6 b_m6]
  have htmp4 : tmp_4 = if w8 < 2^63 then 0 else m7 := by
    by_cases h : w8 < 2^63
    · rw [if_pos h, e_tmp_4, hsignInitial, if_pos h, and_zero]
    · rw [if_neg h, e_tmp_4, hsignInitial, if_neg h, and_allOnes m7 b_m7]
  let firstHigh := w4_1 + 2^64 * w5_1 + 2^128 * w6_1 + 2^192 * w7_1
  let outHigh := w4_2 + 2^64 * w5_2 + 2^128 * w6_2 + 2^192 * w7_2
  have hfirstHighLt : firstHigh < splitRadix := hfirstHighBound
  have houtHighLt : outHigh < splitRadix := houtBound
  obtain ⟨hnormNonneg, hnormLt, _⟩ := normalize_schedule_spec hp hlower hupper
  obtain ⟨sharedLow, hsharedLowLt, hshared⟩ :=
    firstAdjustment_represents_signedExcess hp hlower hupper
  have hmachineLowLt : value.low.toNat + splitRadix * firstHigh < coefficientRadix := by
    clear * - hlowBound hfirstHighLt
    dsimp only [splitRadix, coefficientRadix] at hlowBound hfirstHighLt ⊢
    omega
  have hfirstChain :
      firstHigh + splitRadix * w8_1 + 2^320 * k_w8_1 =
        w4 + 2^64 * w5 + 2^128 * w6 + 2^192 * w7 + splitRadix * w8 +
          (tmp_1 + 2^64 * tmp_2 + 2^128 * tmp_3 + 2^192 * tmp_4) := by
    simpa only [firstHigh, splitRadix, add_zero] using
      addChain5Value w4 w5 w6 w7 w8 tmp_1 tmp_2 tmp_3 tmp_4
        w4_1 w5_1 w6_1 w7_1 w8_1 c c_1 c_2 c_3 k_w8_1
        (by simpa only [add_zero] using l_w4_1) l_w5_1 l_w6_1 l_w7_1
        (by simpa only [zero_add] using l_w8_1)
  let machineExcess : Int :=
    if value.toInt < 0 then
      (w8_1 : Int) + (2^64 : Int) * k_w8_1 - 2^64
    else
      (w8_1 : Int) + (2^64 : Int) * k_w8_1
  have hmachine :
      firstAdjustment modulus.toNat value.toInt =
        (value.low.toNat : Int) + (splitRadix : Int) * firstHigh +
          (coefficientRadix : Int) * machineExcess := by
    by_cases hneg : value.toInt < 0
    · have htop : ¬ w8 < 2^63 := by
        intro h
        have h' : value.l8 < 2^63 := by simpa [e_w8] using h
        unfold PastaAsm.WideLimbs.toInt at hneg
        rw [if_pos h'] at hneg
        clear * - hneg
        omega
      have hchain := hfirstChain
      rw [show tmp_1 = m4 by rw [htmp1, if_neg htop],
        show tmp_2 = m5 by rw [htmp2, if_neg htop],
        show tmp_3 = m6 by rw [htmp3, if_neg htop],
        show tmp_4 = m7 by rw [htmp4, if_neg htop]] at hchain
      rw [firstAdjustment, if_pos hneg, toInt_split]
      unfold highExcessValue alignedModulus
      rw [← e_w4, ← e_w5, ← e_w6, ← e_w7, ← e_w8, if_neg htop]
      simp only [machineExcess, if_pos hneg]
      rw [hdouble] at hchain
      have h := firstStageNegativeIdentity value.low.toNat
        (w4 + 2^64 * w5 + 2^128 * w6 + 2^192 * w7) firstHigh w8 w8_1
        k_w8_1 (2 * modulus.toNat) hchain
      dsimp only [splitRadix, coefficientRadix]
      push_cast at h ⊢
      simpa only [mul_assoc, mul_comm] using h
    · have hnonneg : 0 ≤ value.toInt := by omega
      have htop : w8 < 2^63 := by
        by_contra h
        have h' : ¬ value.l8 < 2^63 := by simpa [e_w8] using h
        have hwideNat' : (value.toNat : Int) < 2^576 := by
          simpa only [Nat.cast_pow, Nat.cast_ofNat] using (Int.ofNat_lt.mpr hwideNat)
        unfold PastaAsm.WideLimbs.toInt at hnonneg
        rw [if_neg h'] at hnonneg
        clear * - hwideNat' hnonneg
        omega
      have hchain := hfirstChain
      rw [show tmp_1 = 0 by rw [htmp1, if_pos htop],
        show tmp_2 = 0 by rw [htmp2, if_pos htop],
        show tmp_3 = 0 by rw [htmp3, if_pos htop],
        show tmp_4 = 0 by rw [htmp4, if_pos htop]] at hchain
      simp only [mul_zero, add_zero] at hchain
      rw [firstAdjustment, if_neg hneg, toInt_split]
      unfold highExcessValue
      rw [← e_w4, ← e_w5, ← e_w6, ← e_w7, ← e_w8, if_pos htop]
      simp only [machineExcess, if_neg hneg]
      have h := firstStageNonnegativeIdentity value.low.toNat
        (w4 + 2^64 * w5 + 2^128 * w6 + 2^192 * w7) firstHigh w8 w8_1
        k_w8_1 hchain
      dsimp only [splitRadix, coefficientRadix]
      exact h
  have hexcess : machineExcess =
      signedExcess (firstAdjustment modulus.toNat value.toInt) := by
    have hdecomp := hmachine.symm.trans hshared
    have hmachineLowNonneg : (0 : Int) ≤ value.low.toNat + splitRadix * firstHigh := by
      positivity
    have hsharedLowNonneg : (0 : Int) ≤ sharedLow := by positivity
    have hmachineLowLt' :
        (value.low.toNat + splitRadix * firstHigh : Int) < coefficientRadix := by
      simpa only [Nat.cast_add, Nat.cast_mul] using (Int.ofNat_lt.mpr hmachineLowLt)
    have hsharedLowLt' : (sharedLow : Int) < coefficientRadix := by
      exact Int.ofNat_lt.mpr hsharedLowLt
    have hradixPos : (0 : Int) < coefficientRadix := by positivity
    clear * - hdecomp hmachineLowNonneg hsharedLowNonneg hmachineLowLt' hsharedLowLt'
      hradixPos
    dsimp only [coefficientRadix, splitRadix] at hdecomp hmachineLowNonneg hmachineLowLt' hsharedLowLt' hradixPos ⊢
    omega
  have hfirstMachine :
      firstAdjustment modulus.toNat value.toInt =
        (value.low.toNat : Int) + (splitRadix : Int) * firstHigh +
          (coefficientRadix : Int) * signedExcess
            (firstAdjustment modulus.toNat value.toInt) := by
    calc
      _ = (value.low.toNat : Int) + (splitRadix : Int) * firstHigh +
          (coefficientRadix : Int) * machineExcess := hmachine
      _ = _ := congrArg
        (fun e : Int => (value.low.toNat : Int) + (splitRadix : Int) * firstHigh +
          (coefficientRadix : Int) * e) hexcess
  have hw8Excess :
      (signedExcess (firstAdjustment modulus.toNat value.toInt) = -1 ∧ w8_1 = 2^64 - 1) ∨
      (signedExcess (firstAdjustment modulus.toNat value.toInt) = 0 ∧ w8_1 = 0) ∨
      (signedExcess (firstAdjustment modulus.toNat value.toInt) = 1 ∧ w8_1 = 1) := by
    have hcases := signedExcess_eq_neg_one_or_zero_or_one
      (firstAdjustment modulus.toNat value.toInt)
    rcases hcases with he | he | he
    · left
      refine ⟨he, ?_⟩
      rw [he] at hexcess
      unfold machineExcess at hexcess
      split_ifs at hexcess <;> clear * - hexcess b_w8_1 b_k_w8_1 <;> omega
    · right; left
      refine ⟨he, ?_⟩
      rw [he] at hexcess
      unfold machineExcess at hexcess
      split_ifs at hexcess <;> clear * - hexcess b_w8_1 b_k_w8_1 <;> omega
    · right; right
      refine ⟨he, ?_⟩
      rw [he] at hexcess
      unfold machineExcess at hexcess
      split_ifs at hexcess <;> clear * - hexcess b_w8_1 b_k_w8_1 <;> omega
  have hnormEq : normalize modulus.toNat value.toInt =
      (value.low.toNat : Int) + (splitRadix : Int) * outHigh := by
    rcases hw8Excess with ⟨he, hw8⟩ | ⟨he, hw8⟩ | ⟨he, hw8⟩
    · have hnegWord : sign_1 = 1 := by
        rw [e_sign_1, hw8]
        norm_num [neg, sub, subc, PastaAsm.regMod]
      have hexcess : excess = 2^64 - 1 := by
        rw [e_excess, hw8, hnegWord, orr_allOnes_one]
      have hsign2 : sign_2 = 0 := by
        rw [e_sign_2, hnegWord]
        norm_num [asr, PastaAsm.word, PastaAsm.regMod]
      have hm4a : m4_2 = m4 := by
        rw [e_m4_2, e_m4_1, hexcess, and_allOnes m4 b_m4, hsign2, eor_zero b_m4]
      have hm5a : m5_2 = m5 := by
        rw [e_m5_2, e_m5_1, hexcess, and_allOnes m5 b_m5, hsign2, eor_zero b_m5]
      have hm6a : m6_2 = m6 := by
        rw [e_m6_2, e_m6_1, hexcess, and_allOnes m6 b_m6, hsign2, eor_zero b_m6]
      have hm7a : m7_2 = m7 := by
        rw [e_m7_2, e_m7_1, hexcess, and_allOnes m7 b_m7, hsign2, eor_zero b_m7]
      have hcorrChain :
          m4_3 + 2^64 * m5_3 + 2^128 * m6_3 + 2^192 * m7_3 +
              splitRadix * k_m7_3 =
            m4 + 2^64 * m5 + 2^128 * m6 + 2^192 * m7 := by
        dsimp only [splitRadix]
        simpa only [hm4a, hm5a, hm6a, hm7a, hsign2, lsr, add_zero, mul_zero] using
          addChain5Value m4_2 m5_2 m6_2 m7_2 0 (lsr sign_2 63) 0 0 0
            m4_3 m5_3 m6_3 m7_3 k_m7_3 c_4 c_5 c_6 k_m7_3 0
            (by simpa only [add_zero] using l_m4_3) l_m5_3 l_m6_3 l_m7_3 (by simp)
      have hcorrCarry : k_m7_3 = 0 := by
        dsimp only [splitRadix] at hcorrChain hdoubleLt
        clear * - hcorrChain hdoubleLt
        omega
      have hcorr :
          m4_3 + 2^64 * m5_3 + 2^128 * m6_3 + 2^192 * m7_3 =
            m4 + 2^64 * m5 + 2^128 * m6 + 2^192 * m7 := by
        rw [hcorrCarry, mul_zero, add_zero] at hcorrChain
        exact hcorrChain
      have houtChain : outHigh + splitRadix * k_w7_2 = firstHigh +
          (m4 + 2^64 * m5 + 2^128 * m6 + 2^192 * m7) := by
        dsimp only [outHigh, firstHigh, splitRadix]
        have h := addChain5Value w4_1 w5_1 w6_1 w7_1 0 m4_3 m5_3 m6_3 m7_3
          w4_2 w5_2 w6_2 w7_2 k_w7_2 c_7 c_8 c_9 k_w7_2 0
          (by simpa only [add_zero] using l_w4_2) l_w5_2 l_w6_2 l_w7_2 (by simp)
        simpa only [hcorr, add_zero] using h
      have hnormalized : normalize modulus.toNat value.toInt =
          (value.low.toNat : Int) + (splitRadix : Int) *
            (firstHigh + (m4 + 2^64 * m5 + 2^128 * m6 + 2^192 * m7) - splitRadix) := by
        unfold Spec.Invert.Normalize.normalize secondAdjustment
        dsimp only
        rw [he, hfirstMachine, he]
        unfold alignedModulus
        push_cast
        rw [← hdoubleInt]
        ring
      have hk : k_w7_2 = 1 := by
        have hnormalized' := hnormNonneg
        rw [hnormalized] at hnormalized'
        dsimp only [splitRadix] at hnormalized' houtChain hlowBound houtHighLt hfirstHighLt hdoubleLt
        exact wrappedCarryIsOne value.low.toNat firstHigh outHigh
          (m4 + 2^64 * m5 + 2^128 * m6 + 2^192 * m7) k_w7_2
          hlowBound hfirstHighLt houtHighLt hdoubleLt houtChain hnormalized'
      rw [hnormalized]
      have houtChain' := congrArg (fun n : Nat => (n : Int)) houtChain
      rw [hk] at houtChain'
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at houtChain'
      dsimp only [splitRadix]
      clear * - houtChain'
      omega
    · have hnegWord : sign_1 = 0 := by
        rw [e_sign_1, hw8]
        norm_num [neg, sub, subc, PastaAsm.regMod]
      have hexcess : excess = 0 := by
        rw [e_excess, hw8, hnegWord]
        norm_num [orr, PastaAsm.word, PastaAsm.regMod]
      have hsign2 : sign_2 = 0 := by
        rw [e_sign_2, hnegWord]
        norm_num [asr, PastaAsm.word, PastaAsm.regMod]
      have hm4a : m4_2 = 0 := by
        rw [e_m4_2, e_m4_1, hexcess, and_zero, hsign2, eor_zero (by decide)]
      have hm5a : m5_2 = 0 := by
        rw [e_m5_2, e_m5_1, hexcess, and_zero, hsign2, eor_zero (by decide)]
      have hm6a : m6_2 = 0 := by
        rw [e_m6_2, e_m6_1, hexcess, and_zero, hsign2, eor_zero (by decide)]
      have hm7a : m7_2 = 0 := by
        rw [e_m7_2, e_m7_1, hexcess, and_zero, hsign2, eor_zero (by decide)]
      have hcorrChain :
          m4_3 + 2^64 * m5_3 + 2^128 * m6_3 + 2^192 * m7_3 +
              splitRadix * k_m7_3 = 0 := by
        dsimp only [splitRadix]
        simpa only [hm4a, hm5a, hm6a, hm7a, hsign2, lsr, add_zero, mul_zero] using
          addChain5Value m4_2 m5_2 m6_2 m7_2 0 (lsr sign_2 63) 0 0 0
            m4_3 m5_3 m6_3 m7_3 k_m7_3 c_4 c_5 c_6 k_m7_3 0
            (by simpa only [add_zero] using l_m4_3) l_m5_3 l_m6_3 l_m7_3 (by simp)
      have hcorr : m4_3 + 2^64 * m5_3 + 2^128 * m6_3 + 2^192 * m7_3 = 0 := by
        dsimp only [splitRadix] at hcorrChain
        omega
      have houtChain : outHigh + splitRadix * k_w7_2 = firstHigh := by
        dsimp only [outHigh, firstHigh, splitRadix]
        have h := addChain5Value w4_1 w5_1 w6_1 w7_1 0 m4_3 m5_3 m6_3 m7_3
          w4_2 w5_2 w6_2 w7_2 k_w7_2 c_7 c_8 c_9 k_w7_2 0
          (by simpa only [add_zero] using l_w4_2) l_w5_2 l_w6_2 l_w7_2 (by simp)
        simpa only [hcorr, add_zero] using h
      have hk : k_w7_2 = 0 := by
        dsimp only [splitRadix] at houtChain hfirstHighLt
        omega
      unfold Spec.Invert.Normalize.normalize secondAdjustment
      dsimp only
      rw [he, hfirstMachine, he]
      rw [hk, mul_zero, add_zero] at houtChain
      push_cast
      omega
    · have hnegWord : sign_1 = 2^64 - 1 := by
        rw [e_sign_1, hw8]
        norm_num [neg, sub, subc, PastaAsm.regMod]
      have hexcess : excess = 2^64 - 1 := by
        rw [e_excess, hw8, hnegWord, orr_one_allOnes]
      have hsign2 : sign_2 = 2^64 - 1 := by
        rw [e_sign_2, hnegWord]
        exact asr63_eq_signMask (by omega)
      have hm4x : m4_2 = 2^64 - 1 - m4 := by
        rw [e_m4_2, e_m4_1, hexcess, and_allOnes m4 b_m4, hsign2,
          eor_allOnes b_m4]
      have hm5x : m5_2 = 2^64 - 1 - m5 := by
        rw [e_m5_2, e_m5_1, hexcess, and_allOnes m5 b_m5, hsign2,
          eor_allOnes b_m5]
      have hm6x : m6_2 = 2^64 - 1 - m6 := by
        rw [e_m6_2, e_m6_1, hexcess, and_allOnes m6 b_m6, hsign2,
          eor_allOnes b_m6]
      have hm7x : m7_2 = 2^64 - 1 - m7 := by
        rw [e_m7_2, e_m7_1, hexcess, and_allOnes m7 b_m7, hsign2,
          eor_allOnes b_m7]
      have hshift : lsr sign_2 63 = 1 := by rw [hsign2]; norm_num [lsr]
      have hadjust :
          m4_3 + 2^64 * m5_3 + 2^128 * m6_3 + 2^192 * m7_3 +
            (m4 + 2^64 * m5 + 2^128 * m6 + 2^192 * m7) = splitRadix := by
        rw [hshift, hm4x] at l_m4_3
        rw [hm5x] at l_m5_3
        rw [hm6x] at l_m6_3
        rw [hm7x] at l_m7_3
        exact complementedAddOneValue m4 m5 m6 m7 m4_3 m5_3 m6_3 m7_3
          c_4 c_5 c_6 k_m7_3 b_m4 b_m5 b_m6 b_m7 hdoublePos hdoubleLt
          (by simpa only [add_zero] using l_m4_3) l_m5_3 l_m6_3 l_m7_3
      have houtChain : outHigh + splitRadix * k_w7_2 = firstHigh +
          (m4_3 + 2^64 * m5_3 + 2^128 * m6_3 + 2^192 * m7_3) := by
        dsimp only [outHigh, firstHigh, splitRadix]
        simpa only [add_zero] using
          addChain5Value w4_1 w5_1 w6_1 w7_1 0 m4_3 m5_3 m6_3 m7_3
            w4_2 w5_2 w6_2 w7_2 k_w7_2 c_7 c_8 c_9 k_w7_2 0
            (by simpa only [add_zero] using l_w4_2) l_w5_2 l_w6_2 l_w7_2
            (by simp)
      have hnormalized : normalize modulus.toNat value.toInt =
          (value.low.toNat : Int) + (splitRadix : Int) *
            (firstHigh + splitRadix -
              (m4 + 2^64 * m5 + 2^128 * m6 + 2^192 * m7)) := by
        unfold Spec.Invert.Normalize.normalize secondAdjustment
        dsimp only
        rw [he, hfirstMachine, he]
        unfold alignedModulus
        push_cast
        rw [← hdoubleInt]
        ring
      have hk : k_w7_2 = 0 := by
        let correction := m4_3 + 2^64 * m5_3 + 2^128 * m6_3 + 2^192 * m7_3
        have hcorrectionLt : correction < 2^256 := by
          dsimp only [correction, splitRadix] at hadjust hdoublePos ⊢
          omega
        have hsumLt : firstHigh + correction < 2^256 := by
          have hnormalized' := hnormLt
          rw [hnormalized] at hnormalized'
          dsimp only [correction, splitRadix, coefficientRadix] at hnormalized' hadjust hlowBound hfirstHighLt ⊢
          omega
        dsimp only [correction, splitRadix] at houtChain
        exact zeroCarryOfBoundedSum firstHigh outHigh correction k_w7_2
          hfirstHighLt houtHighLt hcorrectionLt houtChain hsumLt
      rw [hnormalized]
      have houtChain' := houtChain
      rw [hk, mul_zero, add_zero] at houtChain'
      have hadjustInt := congrArg (fun n : Nat => (n : Int)) hadjust
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hadjustInt
      push_cast
      clear * - houtChain' hadjustInt
      omega
  refine ⟨rfl, ⟨b_w4_2, b_w5_2, b_w6_2, b_w7_2⟩, ?_, ?_⟩
  · change value.low.toNat + splitRadix * outHigh =
      (normalize modulus.toNat value.toInt).toNat
    have hcast : ((normalize modulus.toNat value.toInt).toNat : Int) =
        (value.low.toNat + splitRadix * outHigh : Nat) := by
      rw [Int.toNat_of_nonneg hnormNonneg, hnormEq]
      push_cast
      rfl
    exact_mod_cast hcast.symm
  · exact houtHighLt
  -- END normalizeCoefficient conclusion

end PastaAsm.AArch64
