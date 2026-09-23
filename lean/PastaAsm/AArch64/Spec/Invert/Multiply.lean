/-
Copyright Supranational LLC (the routines, transcribed from Semolina v0.1.4).
Copyright (c) 2026 the pasta-asm contributors (the transcription and the proofs).
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.AArch64.Spec.Invert.Arithmetic

/-!
# Correctness of AArch64 signed coefficient multiplication

These proofs cover the factored sign preparation and product phases of the inversion driver's
nine-word signed multiplication block.
-/

namespace PastaAsm.AArch64

private theorem wideToNat_lt (value : WideLimbs) (hv : value.Bounded) :
    value.toNat < coefficientModulus := by
  simp only [WideLimbs.Bounded, regMod] at hv
  simp only [WideLimbs.toNat, coefficientModulus]
  omega

private theorem asr63_of_low {w : Nat} (hw : w < 2^63) : asr w 63 = 0 := by
  unfold asr
  have hw64 : w < 2^64 := hw.trans (by decide)
  rw [word_eq_of_lt (by simpa only [regMod] using hw64)]
  dsimp only
  rw [if_pos hw, Nat.div_eq_of_lt hw]

private theorem asr63_of_high {w : Nat} (hw : w < 2^64) (hhigh : 2^63 ≤ w) :
    asr w 63 = 2^64 - 1 := by
  unfold asr
  rw [word_eq_of_lt hw, if_neg (by omega)]
  have hdiv : w / 2^63 = 1 := by omega
  rw [hdiv]
  norm_num [word, regMod]

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

private theorem sub_zero {w : Nat} (hw : w < 2^64) : sub w 0 = w := by
  unfold sub subc
  simp only [regMod, Nat.reduceSubDiff, Nat.sub_zero]
  omega

private theorem signedMagnitude_low {w : Nat} (hw : w < 2^64) (hlow : w < 2^63) :
    sub (eor w (asr w 63)) (asr w 63) = w := by
  rw [asr63_of_low hlow, eor_zero hw, sub_zero hw]

private theorem signedMagnitude_high {w : Nat} (hw : w < 2^64) (hhigh : 2^63 ≤ w) :
    sub (eor w (asr w 63)) (asr w 63) = 2^64 - w := by
  rw [asr63_of_high hw hhigh, eor_allOnes hw]
  unfold sub subc
  simp only [regMod, Nat.reduceSubDiff]
  have hwpos : 0 < w := by omega
  have hcalc : 2^64 - 1 - w + 2^64 - (2^64 - 1) - 0 = 2^64 - w := by omega
  rw [hcalc, Nat.mod_eq_of_lt (by omega)]

private theorem complementWide_eq (value : WideLimbs) (hv : value.Bounded) :
    eor value.l0 (2^64 - 1) +
        2^64 * eor value.l1 (2^64 - 1) +
        2^128 * eor value.l2 (2^64 - 1) +
        2^192 * eor value.l3 (2^64 - 1) +
        2^256 * eor value.l4 (2^64 - 1) +
        2^320 * eor value.l5 (2^64 - 1) +
        2^384 * eor value.l6 (2^64 - 1) +
        2^448 * eor value.l7 (2^64 - 1) +
        2^512 * eor value.l8 (2^64 - 1) + value.toNat + 1 =
      coefficientModulus := by
  rw [eor_allOnes hv.1, eor_allOnes hv.2.1, eor_allOnes hv.2.2.1,
    eor_allOnes hv.2.2.2.1, eor_allOnes hv.2.2.2.2.1,
    eor_allOnes hv.2.2.2.2.2.1, eor_allOnes hv.2.2.2.2.2.2.1,
    eor_allOnes hv.2.2.2.2.2.2.2.1, eor_allOnes hv.2.2.2.2.2.2.2.2]
  set_option exponentiation.threshold 600 in
    simp only [WideLimbs.toNat, coefficientModulus]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hv
  simp only [regMod] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  have c0 : 2^64 - 1 - value.l0 + value.l0 = 2^64 - 1 := by omega
  have c1 : 2^64 - 1 - value.l1 + value.l1 = 2^64 - 1 := by omega
  have c2 : 2^64 - 1 - value.l2 + value.l2 = 2^64 - 1 := by omega
  have c3 : 2^64 - 1 - value.l3 + value.l3 = 2^64 - 1 := by omega
  have c4 : 2^64 - 1 - value.l4 + value.l4 = 2^64 - 1 := by omega
  have c5 : 2^64 - 1 - value.l5 + value.l5 = 2^64 - 1 := by omega
  have c6 : 2^64 - 1 - value.l6 + value.l6 = 2^64 - 1 := by omega
  have c7 : 2^64 - 1 - value.l7 + value.l7 = 2^64 - 1 := by omega
  have c8 : 2^64 - 1 - value.l8 + value.l8 = 2^64 - 1 := by omega
  calc
    _ = (2^64 - 1 - value.l0 + value.l0) +
        2^64 * (2^64 - 1 - value.l1 + value.l1) +
        2^128 * (2^64 - 1 - value.l2 + value.l2) +
        2^192 * (2^64 - 1 - value.l3 + value.l3) +
        2^256 * (2^64 - 1 - value.l4 + value.l4) +
        2^320 * (2^64 - 1 - value.l5 + value.l5) +
        2^384 * (2^64 - 1 - value.l6 + value.l6) +
        2^448 * (2^64 - 1 - value.l7 + value.l7) +
        2^512 * (2^64 - 1 - value.l8 + value.l8) + 1 := by
          set_option exponentiation.threshold 600 in ring
    _ = _ := by
      rw [c0, c1, c2, c3, c4, c5, c6, c7, c8]
      set_option exponentiation.threshold 600 in norm_num

private def preparedValue (r : MulSignedPrepared) : Nat :=
  r.l0 + 2^64 * r.l1 + 2^128 * r.l2 + 2^192 * r.l3 +
    2^256 * r.l4 + 2^320 * r.l5 + 2^384 * r.l6 + 2^448 * r.l7 + 2^512 * r.l8

-- BEGIN mulSignedPrepare_spec statement
/-- The preparation phase computes the scalar magnitude and conditionally replaces the nine-word
input by its two's-complement negation. The final witness is the carry discarded above bit 575. -/
theorem mulSignedPrepare_spec (value : WideLimbs) (scalar : Nat)
    (hv : value.Bounded) (hscalar : scalar < 2^64) :
    ∀ r, r = mulSignedPrepare value scalar →
      r.Bounded ∧
        ((scalar < 2^63 ∧ r.magnitude = scalar ∧ preparedValue r = value.toNat) ∨
          (2^63 ≤ scalar ∧ r.magnitude = 2^64 - scalar ∧
            ∃ carry, carry ≤ 1 ∧
              preparedValue r + value.toNat + coefficientModulus * carry =
                coefficientModulus)) := by
  intro r hr
-- END mulSignedPrepare_spec statement
  -- generated skeleton for `mulSignedPrepare`: do not edit between the annotations
  unfold mulSignedPrepare at hr
  lift_lets -merge at hr
  -- scalar': argument
  extract_lets -merge +onlyGivenNames scalar' at hr
  have e_scalar' : scalar' = scalar := rfl
  clear_value scalar'
  have b_scalar' : scalar' < 2^64 := by rw [e_scalar']; exact hscalar
  -- o0: argument
  extract_lets -merge +onlyGivenNames o0 at hr
  have e_o0 : o0 = value.l0 := rfl
  clear_value o0
  have b_o0 : o0 < 2^64 := by rw [e_o0]; exact hv.1
  -- o1: argument
  extract_lets -merge +onlyGivenNames o1 at hr
  have e_o1 : o1 = value.l1 := rfl
  clear_value o1
  have b_o1 : o1 < 2^64 := by rw [e_o1]; exact hv.2.1
  -- o2: argument
  extract_lets -merge +onlyGivenNames o2 at hr
  have e_o2 : o2 = value.l2 := rfl
  clear_value o2
  have b_o2 : o2 < 2^64 := by rw [e_o2]; exact hv.2.2.1
  -- o3: argument
  extract_lets -merge +onlyGivenNames o3 at hr
  have e_o3 : o3 = value.l3 := rfl
  clear_value o3
  have b_o3 : o3 < 2^64 := by rw [e_o3]; exact hv.2.2.2.1
  -- o4: argument
  extract_lets -merge +onlyGivenNames o4 at hr
  have e_o4 : o4 = value.l4 := rfl
  clear_value o4
  have b_o4 : o4 < 2^64 := by rw [e_o4]; exact hv.2.2.2.2.1
  -- o5: argument
  extract_lets -merge +onlyGivenNames o5 at hr
  have e_o5 : o5 = value.l5 := rfl
  clear_value o5
  have b_o5 : o5 < 2^64 := by rw [e_o5]; exact hv.2.2.2.2.2.1
  -- o6: argument
  extract_lets -merge +onlyGivenNames o6 at hr
  have e_o6 : o6 = value.l6 := rfl
  clear_value o6
  have b_o6 : o6 < 2^64 := by rw [e_o6]; exact hv.2.2.2.2.2.2.1
  -- o7: argument
  extract_lets -merge +onlyGivenNames o7 at hr
  have e_o7 : o7 = value.l7 := rfl
  clear_value o7
  have b_o7 : o7 < 2^64 := by rw [e_o7]; exact hv.2.2.2.2.2.2.2.1
  -- o8: argument
  extract_lets -merge +onlyGivenNames o8 at hr
  have e_o8 : o8 = value.l8 := rfl
  clear_value o8
  have b_o8 : o8 < 2^64 := by rw [e_o8]; exact hv.2.2.2.2.2.2.2.2
  -- sign: asr sign,scalar,#63
  extract_lets -merge +onlyGivenNames sign at hr
  have e_sign : sign = asr scalar' 63 := rfl
  clear_value sign
  have b_sign : sign < 2^64 := by rw [e_sign]; exact asr_lt _ _
  -- mag: eor mag,scalar,sign
  extract_lets -merge +onlyGivenNames mag at hr
  have e_mag : mag = eor scalar' sign := rfl
  clear_value mag
  have b_mag : mag < 2^64 := by rw [e_mag]; exact eor_lt _ _
  -- mag_1: sub mag,mag,sign
  extract_lets -merge +onlyGivenNames mag_1 at hr
  have e_mag_1 : mag_1 = sub mag sign := rfl
  clear_value mag_1
  have b_mag_1 : mag_1 < 2^64 := by rw [e_mag_1]; exact sub_lt _ _
  -- o0_1: eor o0,o0,sign
  extract_lets -merge +onlyGivenNames o0_1 at hr
  have e_o0_1 : o0_1 = eor o0 sign := rfl
  clear_value o0_1
  have b_o0_1 : o0_1 < 2^64 := by rw [e_o0_1]; exact eor_lt _ _
  -- o1_1: eor o1,o1,sign
  extract_lets -merge +onlyGivenNames o1_1 at hr
  have e_o1_1 : o1_1 = eor o1 sign := rfl
  clear_value o1_1
  have b_o1_1 : o1_1 < 2^64 := by rw [e_o1_1]; exact eor_lt _ _
  -- o2_1: eor o2,o2,sign
  extract_lets -merge +onlyGivenNames o2_1 at hr
  have e_o2_1 : o2_1 = eor o2 sign := rfl
  clear_value o2_1
  have b_o2_1 : o2_1 < 2^64 := by rw [e_o2_1]; exact eor_lt _ _
  -- o3_1: eor o3,o3,sign
  extract_lets -merge +onlyGivenNames o3_1 at hr
  have e_o3_1 : o3_1 = eor o3 sign := rfl
  clear_value o3_1
  have b_o3_1 : o3_1 < 2^64 := by rw [e_o3_1]; exact eor_lt _ _
  -- o4_1: eor o4,o4,sign
  extract_lets -merge +onlyGivenNames o4_1 at hr
  have e_o4_1 : o4_1 = eor o4 sign := rfl
  clear_value o4_1
  have b_o4_1 : o4_1 < 2^64 := by rw [e_o4_1]; exact eor_lt _ _
  -- o5_1: eor o5,o5,sign
  extract_lets -merge +onlyGivenNames o5_1 at hr
  have e_o5_1 : o5_1 = eor o5 sign := rfl
  clear_value o5_1
  have b_o5_1 : o5_1 < 2^64 := by rw [e_o5_1]; exact eor_lt _ _
  -- o6_1: eor o6,o6,sign
  extract_lets -merge +onlyGivenNames o6_1 at hr
  have e_o6_1 : o6_1 = eor o6 sign := rfl
  clear_value o6_1
  have b_o6_1 : o6_1 < 2^64 := by rw [e_o6_1]; exact eor_lt _ _
  -- o7_1: eor o7,o7,sign
  extract_lets -merge +onlyGivenNames o7_1 at hr
  have e_o7_1 : o7_1 = eor o7 sign := rfl
  clear_value o7_1
  have b_o7_1 : o7_1 < 2^64 := by rw [e_o7_1]; exact eor_lt _ _
  -- o8_1: eor o8,o8,sign
  extract_lets -merge +onlyGivenNames o8_1 at hr
  have e_o8_1 : o8_1 = eor o8 sign := rfl
  clear_value o8_1
  have b_o8_1 : o8_1 < 2^64 := by rw [e_o8_1]; exact eor_lt _ _
  -- o0_2: adds o0,o0,sign,lsr #63
  extract_lets -merge +onlyGivenNames s o0_2 c at hr
  have e_o0_2 : o0_2 = (o0_1 + (lsr sign 63) + 0) % 2^64 := rfl
  have e_c : c = (o0_1 + (lsr sign 63) + 0) / 2^64 := rfl
  clear_value s o0_2 c
  have l_o0_2 : o0_2 + 2^64 * c = o0_1 + (lsr sign 63) + 0 := by
    rw [e_o0_2, e_c]; exact Nat.mod_add_div _ _
  have b_o0_2 : o0_2 < 2^64 := by rw [e_o0_2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c : c ≤ 1 := by
    rw [e_c]; exact addc_carry_le_one o0_1 (lsr sign 63) 0 b_o0_1 (lt_of_le_of_lt (Nat.div_le_self _ _) b_sign) (by decide)
  clear e_o0_2 e_c
  -- o1_2: adcs o1,o1,xzr
  extract_lets -merge +onlyGivenNames s_1 o1_2 c_1 at hr
  have e_o1_2 : o1_2 = (o1_1 + 0 + c) % 2^64 := rfl
  have e_c_1 : c_1 = (o1_1 + 0 + c) / 2^64 := rfl
  clear_value s_1 o1_2 c_1
  have l_o1_2 : o1_2 + 2^64 * c_1 = o1_1 + 0 + c := by
    rw [e_o1_2, e_c_1]; exact Nat.mod_add_div _ _
  have b_o1_2 : o1_2 < 2^64 := by rw [e_o1_2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_1 : c_1 ≤ 1 := by
    rw [e_c_1]; exact addc_carry_le_one o1_1 0 c b_o1_1 (by decide) b_c
  clear e_o1_2 e_c_1
  -- o2_2: adcs o2,o2,xzr
  extract_lets -merge +onlyGivenNames s_2 o2_2 c_2 at hr
  have e_o2_2 : o2_2 = (o2_1 + 0 + c_1) % 2^64 := rfl
  have e_c_2 : c_2 = (o2_1 + 0 + c_1) / 2^64 := rfl
  clear_value s_2 o2_2 c_2
  have l_o2_2 : o2_2 + 2^64 * c_2 = o2_1 + 0 + c_1 := by
    rw [e_o2_2, e_c_2]; exact Nat.mod_add_div _ _
  have b_o2_2 : o2_2 < 2^64 := by rw [e_o2_2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_2 : c_2 ≤ 1 := by
    rw [e_c_2]; exact addc_carry_le_one o2_1 0 c_1 b_o2_1 (by decide) b_c_1
  clear e_o2_2 e_c_2
  -- o3_2: adcs o3,o3,xzr
  extract_lets -merge +onlyGivenNames s_3 o3_2 c_3 at hr
  have e_o3_2 : o3_2 = (o3_1 + 0 + c_2) % 2^64 := rfl
  have e_c_3 : c_3 = (o3_1 + 0 + c_2) / 2^64 := rfl
  clear_value s_3 o3_2 c_3
  have l_o3_2 : o3_2 + 2^64 * c_3 = o3_1 + 0 + c_2 := by
    rw [e_o3_2, e_c_3]; exact Nat.mod_add_div _ _
  have b_o3_2 : o3_2 < 2^64 := by rw [e_o3_2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_3 : c_3 ≤ 1 := by
    rw [e_c_3]; exact addc_carry_le_one o3_1 0 c_2 b_o3_1 (by decide) b_c_2
  clear e_o3_2 e_c_3
  -- o4_2: adcs o4,o4,xzr
  extract_lets -merge +onlyGivenNames s_4 o4_2 c_4 at hr
  have e_o4_2 : o4_2 = (o4_1 + 0 + c_3) % 2^64 := rfl
  have e_c_4 : c_4 = (o4_1 + 0 + c_3) / 2^64 := rfl
  clear_value s_4 o4_2 c_4
  have l_o4_2 : o4_2 + 2^64 * c_4 = o4_1 + 0 + c_3 := by
    rw [e_o4_2, e_c_4]; exact Nat.mod_add_div _ _
  have b_o4_2 : o4_2 < 2^64 := by rw [e_o4_2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_4 : c_4 ≤ 1 := by
    rw [e_c_4]; exact addc_carry_le_one o4_1 0 c_3 b_o4_1 (by decide) b_c_3
  clear e_o4_2 e_c_4
  -- o5_2: adcs o5,o5,xzr
  extract_lets -merge +onlyGivenNames s_5 o5_2 c_5 at hr
  have e_o5_2 : o5_2 = (o5_1 + 0 + c_4) % 2^64 := rfl
  have e_c_5 : c_5 = (o5_1 + 0 + c_4) / 2^64 := rfl
  clear_value s_5 o5_2 c_5
  have l_o5_2 : o5_2 + 2^64 * c_5 = o5_1 + 0 + c_4 := by
    rw [e_o5_2, e_c_5]; exact Nat.mod_add_div _ _
  have b_o5_2 : o5_2 < 2^64 := by rw [e_o5_2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_5 : c_5 ≤ 1 := by
    rw [e_c_5]; exact addc_carry_le_one o5_1 0 c_4 b_o5_1 (by decide) b_c_4
  clear e_o5_2 e_c_5
  -- o6_2: adcs o6,o6,xzr
  extract_lets -merge +onlyGivenNames s_6 o6_2 c_6 at hr
  have e_o6_2 : o6_2 = (o6_1 + 0 + c_5) % 2^64 := rfl
  have e_c_6 : c_6 = (o6_1 + 0 + c_5) / 2^64 := rfl
  clear_value s_6 o6_2 c_6
  have l_o6_2 : o6_2 + 2^64 * c_6 = o6_1 + 0 + c_5 := by
    rw [e_o6_2, e_c_6]; exact Nat.mod_add_div _ _
  have b_o6_2 : o6_2 < 2^64 := by rw [e_o6_2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_6 : c_6 ≤ 1 := by
    rw [e_c_6]; exact addc_carry_le_one o6_1 0 c_5 b_o6_1 (by decide) b_c_5
  clear e_o6_2 e_c_6
  -- o7_2: adcs o7,o7,xzr
  extract_lets -merge +onlyGivenNames s_7 o7_2 c_7 at hr
  have e_o7_2 : o7_2 = (o7_1 + 0 + c_6) % 2^64 := rfl
  have e_c_7 : c_7 = (o7_1 + 0 + c_6) / 2^64 := rfl
  clear_value s_7 o7_2 c_7
  have l_o7_2 : o7_2 + 2^64 * c_7 = o7_1 + 0 + c_6 := by
    rw [e_o7_2, e_c_7]; exact Nat.mod_add_div _ _
  have b_o7_2 : o7_2 < 2^64 := by rw [e_o7_2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_7 : c_7 ≤ 1 := by
    rw [e_c_7]; exact addc_carry_le_one o7_1 0 c_6 b_o7_1 (by decide) b_c_6
  clear e_o7_2 e_c_7
  -- o8_2: adc o8,o8,xzr
  extract_lets -merge +onlyGivenNames o8_2 at hr
  have e_o8_2 : o8_2 = (o8_1 + 0 + c_7) % 2^64 := rfl
  clear_value o8_2
  have b_o8_2 : o8_2 < 2^64 := by rw [e_o8_2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨k_o8_2, b_k_o8_2, l_o8_2⟩ :
      ∃ k, k ≤ 1 ∧ o8_2 + 2^64 * k = o8_1 + 0 + c_7 :=
    ⟨(o8_1 + 0 + c_7) / 2^64, addc_carry_le_one o8_1 0 c_7 b_o8_1 (by decide) b_c_7,
      by rw [e_o8_2]; exact Nat.mod_add_div _ _⟩
  clear e_o8_2
  subst hr
  -- BEGIN mulSignedPrepare conclusion
  have hchain :
      o0_2 + 2^64 * o1_2 + 2^128 * o2_2 + 2^192 * o3_2 +
          2^256 * o4_2 + 2^320 * o5_2 + 2^384 * o6_2 +
          2^448 * o7_2 + 2^512 * o8_2 + coefficientModulus * k_o8_2 =
        o0_1 + 2^64 * o1_1 + 2^128 * o2_1 + 2^192 * o3_1 +
          2^256 * o4_1 + 2^320 * o5_1 + 2^384 * o6_1 +
          2^448 * o7_1 + 2^512 * o8_1 + lsr sign 63 := by
    simp only [coefficientModulus]
    clear * - l_o0_2 l_o1_2 l_o2_2 l_o3_2 l_o4_2 l_o5_2 l_o6_2 l_o7_2 l_o8_2
    omega
  refine ⟨⟨b_o0_2, b_o1_2, b_o2_2, b_o3_2, b_o4_2, b_o5_2, b_o6_2,
    b_o7_2, b_o8_2, b_mag_1⟩, ?_⟩
  by_cases hs : scalar < 2^63
  · left
    have hsign : sign = 0 := by rw [e_sign, e_scalar', asr63_of_low hs]
    have hmag : mag_1 = scalar := by
      rw [e_mag_1, e_mag, e_scalar', hsign, eor_zero hscalar, sub_zero hscalar]
    rw [e_o0_1, e_o1_1, e_o2_1, e_o3_1, e_o4_1, e_o5_1, e_o6_1, e_o7_1,
      e_o8_1, e_o0, e_o1, e_o2, e_o3, e_o4, e_o5, e_o6, e_o7, e_o8, hsign,
      eor_zero hv.1, eor_zero hv.2.1, eor_zero hv.2.2.1, eor_zero hv.2.2.2.1,
      eor_zero hv.2.2.2.2.1, eor_zero hv.2.2.2.2.2.1,
      eor_zero hv.2.2.2.2.2.2.1, eor_zero hv.2.2.2.2.2.2.2.1,
      eor_zero hv.2.2.2.2.2.2.2.2] at hchain
    norm_num [lsr] at hchain
    refine ⟨hs, hmag, ?_⟩
    simp only [preparedValue, WideLimbs.toNat]
    have hvlt := wideToNat_lt value hv
    simp only [WideLimbs.toNat] at hvlt
    clear * - hchain hvlt
    simp only [coefficientModulus] at hchain hvlt ⊢
    omega
  · right
    have hsge : 2^63 ≤ scalar := by omega
    have hsign : sign = 2^64 - 1 := by
      rw [e_sign, e_scalar', asr63_of_high hscalar hsge]
    have hasr : asr scalar 63 = 2^64 - 1 := asr63_of_high hscalar hsge
    have hmag : mag_1 = 2^64 - scalar := by
      rw [e_mag_1, e_mag, e_scalar', hsign]
      rw [← hasr]
      exact signedMagnitude_high hscalar hsge
    rw [e_o0_1, e_o1_1, e_o2_1, e_o3_1, e_o4_1, e_o5_1, e_o6_1, e_o7_1,
      e_o8_1, e_o0, e_o1, e_o2, e_o3, e_o4, e_o5, e_o6, e_o7, e_o8, hsign]
      at hchain
    have hlsr : lsr (2^64 - 1) 63 = 1 := by norm_num [lsr]
    rw [hlsr] at hchain
    have hcomplement := complementWide_eq value hv
    refine ⟨hsge, hmag, k_o8_2, b_k_o8_2, ?_⟩
    simp only [preparedValue]
    calc
      _ = (o0_2 + 2^64 * o1_2 + 2^128 * o2_2 + 2^192 * o3_2 +
            2^256 * o4_2 + 2^320 * o5_2 + 2^384 * o6_2 +
            2^448 * o7_2 + 2^512 * o8_2 + coefficientModulus * k_o8_2) +
          value.toNat := by
            set_option exponentiation.threshold 600 in ring
      _ = (eor value.l0 (2^64 - 1) +
            2^64 * eor value.l1 (2^64 - 1) +
            2^128 * eor value.l2 (2^64 - 1) +
            2^192 * eor value.l3 (2^64 - 1) +
            2^256 * eor value.l4 (2^64 - 1) +
            2^320 * eor value.l5 (2^64 - 1) +
            2^384 * eor value.l6 (2^64 - 1) +
            2^448 * eor value.l7 (2^64 - 1) +
            2^512 * eor value.l8 (2^64 - 1) + 1) + value.toNat := by rw [hchain]
      _ = coefficientModulus := by
        rw [← hcomplement]
        set_option exponentiation.threshold 600 in ring
  -- END mulSignedPrepare conclusion

-- BEGIN mulSignedFirst_spec statement
/-- The first product phase returns the exact low and high words of one limb product. -/
theorem mulSignedFirst_spec (limb magnitude : Nat)
    (hlimb : limb < 2^64) (hmagnitude : magnitude < 2^64) :
    ∀ r, r = mulSignedFirst limb magnitude →
      r.Bounded ∧ r.low + 2^64 * r.carry = limb * magnitude := by
  intro r hr
-- END mulSignedFirst_spec statement
  -- generated skeleton for `mulSignedFirst`: do not edit between the annotations
  unfold mulSignedFirst at hr
  lift_lets -merge at hr
  -- o0: phase argument
  extract_lets -merge +onlyGivenNames o0 at hr
  have e_o0 : o0 = limb := rfl
  clear_value o0
  have b_o0 : o0 < 2^64 := by rw [e_o0]; exact hlimb
  -- mag: phase argument
  extract_lets -merge +onlyGivenNames mag at hr
  have e_mag : mag = magnitude := rfl
  clear_value mag
  have b_mag : mag < 2^64 := by rw [e_mag]; exact hmagnitude
  -- carry: umulh carry,o0,mag
  extract_lets -merge +onlyGivenNames carry at hr
  have e_carry : carry = o0 * mag / 2^64 := rfl
  clear_value carry
  have p_carry : o0 * mag < 2^64 * 2^64 := Nat.mul_lt_mul'' b_o0 b_mag
  have b_carry : carry < 2^64 := by rw [e_carry]; exact Nat.div_lt_of_lt_mul p_carry
  obtain ⟨lo_carry, b_lo_carry, d_carry⟩ :
      ∃ lo, lo < 2^64 ∧ lo + 2^64 * carry = o0 * mag :=
    ⟨o0 * mag % 2^64, Nat.mod_lt _ (Nat.two_pow_pos _),
      by rw [e_carry]; exact Nat.mod_add_div _ _⟩
  clear e_carry
  -- o0_1: mul o0,o0,mag
  extract_lets -merge +onlyGivenNames o0_1 at hr
  have e_o0_1 : o0_1 = o0 * mag % 2^64 := rfl
  clear_value o0_1
  have b_o0_1 : o0_1 < 2^64 := by rw [e_o0_1]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  subst hr
  -- BEGIN mulSignedFirst conclusion
  refine ⟨⟨b_o0_1, b_carry⟩, ?_⟩
  change o0_1 + 2^64 * carry = limb * magnitude
  have hlo : lo_carry = o0 * mag % 2^64 := by
    have hcanonical := Nat.mod_add_div (o0 * mag) (2^64)
    clear * - d_carry hcanonical b_lo_carry
    omega
  rw [e_o0_1, ← hlo, d_carry, e_o0, e_mag]
  -- END mulSignedFirst conclusion

-- BEGIN mulSignedRound_spec statement
/-- A middle product phase adds the incoming carry and returns the next exact radix word. -/
theorem mulSignedRound_spec (limb magnitude productCarry : Nat)
    (hlimb : limb < 2^64) (hmagnitude : magnitude < 2^64)
    (hproductCarry : productCarry < 2^64) :
    ∀ r, r = mulSignedRound limb magnitude productCarry →
      r.Bounded ∧ r.low + 2^64 * r.carry = limb * magnitude + productCarry := by
  intro r hr
-- END mulSignedRound_spec statement
  -- generated skeleton for `mulSignedRound`: do not edit between the annotations
  unfold mulSignedRound at hr
  lift_lets -merge at hr
  -- o1: phase argument
  extract_lets -merge +onlyGivenNames o1 at hr
  have e_o1 : o1 = limb := rfl
  clear_value o1
  have b_o1 : o1 < 2^64 := by rw [e_o1]; exact hlimb
  -- mag: phase argument
  extract_lets -merge +onlyGivenNames mag at hr
  have e_mag : mag = magnitude := rfl
  clear_value mag
  have b_mag : mag < 2^64 := by rw [e_mag]; exact hmagnitude
  -- carry: phase argument
  extract_lets -merge +onlyGivenNames carry at hr
  have e_carry : carry = productCarry := rfl
  clear_value carry
  have b_carry : carry < 2^64 := by rw [e_carry]; exact hproductCarry
  -- hi: umulh hi,o1,mag
  extract_lets -merge +onlyGivenNames hi at hr
  have e_hi : hi = o1 * mag / 2^64 := rfl
  clear_value hi
  have p_hi : o1 * mag < 2^64 * 2^64 := Nat.mul_lt_mul'' b_o1 b_mag
  have b_hi : hi < 2^64 := by rw [e_hi]; exact Nat.div_lt_of_lt_mul p_hi
  obtain ⟨lo_hi, b_lo_hi, d_hi⟩ :
      ∃ lo, lo < 2^64 ∧ lo + 2^64 * hi = o1 * mag :=
    ⟨o1 * mag % 2^64, Nat.mod_lt _ (Nat.two_pow_pos _),
      by rw [e_hi]; exact Nat.mod_add_div _ _⟩
  clear e_hi
  -- o1_1: mul o1,o1,mag
  extract_lets -merge +onlyGivenNames o1_1 at hr
  have e_o1_1 : o1_1 = o1 * mag % 2^64 := rfl
  clear_value o1_1
  have b_o1_1 : o1_1 < 2^64 := by rw [e_o1_1]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- o1_2: adds o1,o1,carry
  extract_lets -merge +onlyGivenNames s o1_2 c at hr
  have e_o1_2 : o1_2 = (o1_1 + carry + 0) % 2^64 := rfl
  have e_c : c = (o1_1 + carry + 0) / 2^64 := rfl
  clear_value s o1_2 c
  have l_o1_2 : o1_2 + 2^64 * c = o1_1 + carry + 0 := by
    rw [e_o1_2, e_c]; exact Nat.mod_add_div _ _
  have b_o1_2 : o1_2 < 2^64 := by rw [e_o1_2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c : c ≤ 1 := by
    rw [e_c]; exact addc_carry_le_one o1_1 carry 0 b_o1_1 b_carry (by decide)
  clear e_o1_2 e_c
  -- carry_1: adc carry,hi,xzr
  extract_lets -merge +onlyGivenNames carry_1 at hr
  have e_carry_1 : carry_1 = (hi + 0 + c) % 2^64 := rfl
  clear_value carry_1
  have b_carry_1 : carry_1 < 2^64 := by rw [e_carry_1]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨k_carry_1, b_k_carry_1, l_carry_1⟩ :
      ∃ k, k ≤ 1 ∧ carry_1 + 2^64 * k = hi + 0 + c :=
    ⟨(hi + 0 + c) / 2^64, addc_carry_le_one hi 0 c b_hi (by decide) b_c,
      by rw [e_carry_1]; exact Nat.mod_add_div _ _⟩
  clear e_carry_1
  subst hr
  -- BEGIN mulSignedRound conclusion
  have htop : k_carry_1 = 0 := by
    have hmul := Nat.mul_le_mul (Nat.le_sub_one_of_lt b_o1) (Nat.le_sub_one_of_lt b_mag)
    have hcarry := Nat.le_sub_one_of_lt b_carry
    norm_num at hmul hcarry ⊢
    omega
  refine ⟨⟨b_o1_2, b_carry_1⟩, ?_⟩
  change o1_2 + 2^64 * carry_1 = limb * magnitude + productCarry
  rw [htop, mul_zero, add_zero] at l_carry_1
  have hlo : lo_hi = o1 * mag % 2^64 := by
    have hcanonical := Nat.mod_add_div (o1 * mag) (2^64)
    clear * - d_hi hcanonical b_lo_hi
    omega
  have hproduct : o1_1 + 2^64 * hi = o1 * mag := by
    rw [e_o1_1, ← hlo]
    exact d_hi
  have hlow : o1_2 + 2^64 * c = o1_1 + carry := by
    simpa only [add_zero] using l_o1_2
  have hhigh : carry_1 = hi + c := by
    simpa only [add_zero] using l_carry_1
  calc
    o1_2 + 2^64 * carry_1 = o1_2 + 2^64 * (hi + c) := by rw [hhigh]
    _ = (o1_2 + 2^64 * c) + 2^64 * hi := by ring
    _ = (o1_1 + carry) + 2^64 * hi := by rw [hlow]
    _ = (o1_1 + 2^64 * hi) + carry := by ring
    _ = limb * magnitude + productCarry := by rw [hproduct, e_o1, e_mag, e_carry]
  -- END mulSignedRound conclusion

-- BEGIN mulSignedLast_spec statement
/-- The final product phase returns the low word and exposes the discarded high word existentially. -/
theorem mulSignedLast_spec (limb magnitude productCarry : Nat)
    (hlimb : limb < 2^64) (hmagnitude : magnitude < 2^64)
    (hproductCarry : productCarry < 2^64) :
    ∀ r, r = mulSignedLast limb magnitude productCarry →
      r.Bounded ∧ ∃ carry, carry < 2^64 ∧
        r.low + 2^64 * carry = limb * magnitude + productCarry := by
  intro r hr
-- END mulSignedLast_spec statement
  -- generated skeleton for `mulSignedLast`: do not edit between the annotations
  unfold mulSignedLast at hr
  lift_lets -merge at hr
  -- o8: phase argument
  extract_lets -merge +onlyGivenNames o8 at hr
  have e_o8 : o8 = limb := rfl
  clear_value o8
  have b_o8 : o8 < 2^64 := by rw [e_o8]; exact hlimb
  -- mag: phase argument
  extract_lets -merge +onlyGivenNames mag at hr
  have e_mag : mag = magnitude := rfl
  clear_value mag
  have b_mag : mag < 2^64 := by rw [e_mag]; exact hmagnitude
  -- carry: phase argument
  extract_lets -merge +onlyGivenNames carry at hr
  have e_carry : carry = productCarry := rfl
  clear_value carry
  have b_carry : carry < 2^64 := by rw [e_carry]; exact hproductCarry
  -- o8_1: mul o8,o8,mag
  extract_lets -merge +onlyGivenNames o8_1 at hr
  have e_o8_1 : o8_1 = o8 * mag % 2^64 := rfl
  clear_value o8_1
  have b_o8_1 : o8_1 < 2^64 := by rw [e_o8_1]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- o8_2: add o8,o8,carry
  extract_lets -merge +onlyGivenNames o8_2 at hr
  have e_o8_2 : o8_2 = add o8_1 carry := rfl
  clear_value o8_2
  have b_o8_2 : o8_2 < 2^64 := by rw [e_o8_2]; exact add_lt _ _
  subst hr
  -- BEGIN mulSignedLast conclusion
  let discarded := (o8 * mag + carry) / 2^64
  have htotal : o8 * mag + carry < 2^64 * 2^64 := by
    have hmul := Nat.mul_le_mul (Nat.le_sub_one_of_lt b_o8) (Nat.le_sub_one_of_lt b_mag)
    have hcarry := Nat.le_sub_one_of_lt b_carry
    norm_num at hmul hcarry ⊢
    omega
  have bdiscarded : discarded < 2^64 := by
    exact Nat.div_lt_of_lt_mul htotal
  refine ⟨b_o8_2, discarded, bdiscarded, ?_⟩
  change o8_2 + 2^64 * discarded = limb * magnitude + productCarry
  have hlow : o8 * mag % 2^64 + carry ≡ o8 * mag + carry [MOD 2^64] := by
    exact (Nat.mod_modEq _ _).add_right carry
  have hout : o8_2 = (o8 * mag + carry) % 2^64 := by
    rw [e_o8_2, e_o8_1]
    unfold add addc
    simp only [regMod, Nat.add_zero]
    exact hlow
  rw [hout]
  exact (Nat.mod_add_div (o8 * mag + carry) (2^64)).trans (by rw [e_o8, e_mag, e_carry])
  -- END mulSignedLast conclusion

private theorem extendProductChain {acc carry base magnitude radix limb out next : Nat}
    (hacc : acc + radix * carry = base * magnitude)
    (hout : out + 2^64 * next = limb * magnitude + carry) :
    acc + radix * out + (radix * 2^64) * next =
      (base + radix * limb) * magnitude := by
  calc
    _ = acc + radix * (out + 2^64 * next) := by ring
    _ = acc + radix * (limb * magnitude + carry) := by rw [hout]
    _ = (acc + radix * carry) + radix * limb * magnitude := by ring
    _ = base * magnitude + radix * limb * magnitude := by rw [hacc]
    _ = _ := by ring

-- BEGIN mulSigned_spec statement
/-- Multiplication by a signed 64-bit scalar bitpattern modulo the nine-word coefficient width. -/
theorem mulSigned_spec (value : WideLimbs) (scalar : Nat)
    (hv : value.Bounded) (hscalar : scalar < 2^64) :
    ∀ r, r = mulSigned value scalar →
      r.Bounded ∧
        ((scalar < 2^63 ∧
            r.toNat ≡ value.toNat * scalar [MOD coefficientModulus]) ∨
          (2^63 ≤ scalar ∧
            r.toNat + value.toNat * (2^64 - scalar) ≡ 0
              [MOD coefficientModulus])) := by
  intro r hr
-- END mulSigned_spec statement
  -- generated skeleton for `mulSigned`: do not edit between the annotations
  unfold mulSigned at hr
  lift_lets -merge at hr
  -- prepared: factored prepare/sign-negation phase
  extract_lets -merge +onlyGivenNames prepared at hr
  have e_prepared : prepared = mulSignedPrepare value scalar := rfl
  clear_value prepared
  -- o0: prepare/sign-negation phase output
  extract_lets -merge +onlyGivenNames o0 at hr
  have e_o0 : o0 = prepared.l0 := rfl
  clear_value o0
  -- o1: prepare/sign-negation phase output
  extract_lets -merge +onlyGivenNames o1 at hr
  have e_o1 : o1 = prepared.l1 := rfl
  clear_value o1
  -- o2: prepare/sign-negation phase output
  extract_lets -merge +onlyGivenNames o2 at hr
  have e_o2 : o2 = prepared.l2 := rfl
  clear_value o2
  -- o3: prepare/sign-negation phase output
  extract_lets -merge +onlyGivenNames o3 at hr
  have e_o3 : o3 = prepared.l3 := rfl
  clear_value o3
  -- o4: prepare/sign-negation phase output
  extract_lets -merge +onlyGivenNames o4 at hr
  have e_o4 : o4 = prepared.l4 := rfl
  clear_value o4
  -- o5: prepare/sign-negation phase output
  extract_lets -merge +onlyGivenNames o5 at hr
  have e_o5 : o5 = prepared.l5 := rfl
  clear_value o5
  -- o6: prepare/sign-negation phase output
  extract_lets -merge +onlyGivenNames o6 at hr
  have e_o6 : o6 = prepared.l6 := rfl
  clear_value o6
  -- o7: prepare/sign-negation phase output
  extract_lets -merge +onlyGivenNames o7 at hr
  have e_o7 : o7 = prepared.l7 := rfl
  clear_value o7
  -- o8: prepare/sign-negation phase output
  extract_lets -merge +onlyGivenNames o8 at hr
  have e_o8 : o8 = prepared.l8 := rfl
  clear_value o8
  -- mag: prepare/sign-negation phase output
  extract_lets -merge +onlyGivenNames mag at hr
  have e_mag : mag = prepared.magnitude := rfl
  clear_value mag
  -- firstProduct: factored first product phase
  extract_lets -merge +onlyGivenNames firstProduct at hr
  have e_firstProduct : firstProduct = mulSignedFirst o0 mag := rfl
  clear_value firstProduct
  -- o0_1: first product phase output
  extract_lets -merge +onlyGivenNames o0_1 at hr
  have e_o0_1 : o0_1 = firstProduct.low := rfl
  clear_value o0_1
  -- carry: first product phase output
  extract_lets -merge +onlyGivenNames carry at hr
  have e_carry : carry = firstProduct.carry := rfl
  clear_value carry
  -- round1: factored product round 1
  extract_lets -merge +onlyGivenNames round1 at hr
  have e_round1 : round1 = mulSignedRound o1 mag carry := rfl
  clear_value round1
  -- o1_1: product round 1 output
  extract_lets -merge +onlyGivenNames o1_1 at hr
  have e_o1_1 : o1_1 = round1.low := rfl
  clear_value o1_1
  -- carry_1: product round 1 output
  extract_lets -merge +onlyGivenNames carry_1 at hr
  have e_carry_1 : carry_1 = round1.carry := rfl
  clear_value carry_1
  -- round2: factored product round 2
  extract_lets -merge +onlyGivenNames round2 at hr
  have e_round2 : round2 = mulSignedRound o2 mag carry_1 := rfl
  clear_value round2
  -- o2_1: product round 2 output
  extract_lets -merge +onlyGivenNames o2_1 at hr
  have e_o2_1 : o2_1 = round2.low := rfl
  clear_value o2_1
  -- carry_2: product round 2 output
  extract_lets -merge +onlyGivenNames carry_2 at hr
  have e_carry_2 : carry_2 = round2.carry := rfl
  clear_value carry_2
  -- round3: factored product round 3
  extract_lets -merge +onlyGivenNames round3 at hr
  have e_round3 : round3 = mulSignedRound o3 mag carry_2 := rfl
  clear_value round3
  -- o3_1: product round 3 output
  extract_lets -merge +onlyGivenNames o3_1 at hr
  have e_o3_1 : o3_1 = round3.low := rfl
  clear_value o3_1
  -- carry_3: product round 3 output
  extract_lets -merge +onlyGivenNames carry_3 at hr
  have e_carry_3 : carry_3 = round3.carry := rfl
  clear_value carry_3
  -- round4: factored product round 4
  extract_lets -merge +onlyGivenNames round4 at hr
  have e_round4 : round4 = mulSignedRound o4 mag carry_3 := rfl
  clear_value round4
  -- o4_1: product round 4 output
  extract_lets -merge +onlyGivenNames o4_1 at hr
  have e_o4_1 : o4_1 = round4.low := rfl
  clear_value o4_1
  -- carry_4: product round 4 output
  extract_lets -merge +onlyGivenNames carry_4 at hr
  have e_carry_4 : carry_4 = round4.carry := rfl
  clear_value carry_4
  -- round5: factored product round 5
  extract_lets -merge +onlyGivenNames round5 at hr
  have e_round5 : round5 = mulSignedRound o5 mag carry_4 := rfl
  clear_value round5
  -- o5_1: product round 5 output
  extract_lets -merge +onlyGivenNames o5_1 at hr
  have e_o5_1 : o5_1 = round5.low := rfl
  clear_value o5_1
  -- carry_5: product round 5 output
  extract_lets -merge +onlyGivenNames carry_5 at hr
  have e_carry_5 : carry_5 = round5.carry := rfl
  clear_value carry_5
  -- round6: factored product round 6
  extract_lets -merge +onlyGivenNames round6 at hr
  have e_round6 : round6 = mulSignedRound o6 mag carry_5 := rfl
  clear_value round6
  -- o6_1: product round 6 output
  extract_lets -merge +onlyGivenNames o6_1 at hr
  have e_o6_1 : o6_1 = round6.low := rfl
  clear_value o6_1
  -- carry_6: product round 6 output
  extract_lets -merge +onlyGivenNames carry_6 at hr
  have e_carry_6 : carry_6 = round6.carry := rfl
  clear_value carry_6
  -- round7: factored product round 7
  extract_lets -merge +onlyGivenNames round7 at hr
  have e_round7 : round7 = mulSignedRound o7 mag carry_6 := rfl
  clear_value round7
  -- o7_1: product round 7 output
  extract_lets -merge +onlyGivenNames o7_1 at hr
  have e_o7_1 : o7_1 = round7.low := rfl
  clear_value o7_1
  -- carry_7: product round 7 output
  extract_lets -merge +onlyGivenNames carry_7 at hr
  have e_carry_7 : carry_7 = round7.carry := rfl
  clear_value carry_7
  -- lastProduct: factored final product phase
  extract_lets -merge +onlyGivenNames lastProduct at hr
  have e_lastProduct : lastProduct = mulSignedLast o8 mag carry_7 := rfl
  clear_value lastProduct
  -- o8_1: final product phase output
  extract_lets -merge +onlyGivenNames o8_1 at hr
  have e_o8_1 : o8_1 = lastProduct.low := rfl
  clear_value o8_1
  subst hr
  -- BEGIN mulSigned conclusion
  obtain ⟨hprepared, hprepareCases⟩ :=
    mulSignedPrepare_spec value scalar hv hscalar prepared e_prepared
  have bo0 : o0 < 2^64 := by rw [e_o0]; exact hprepared.1
  have bo1 : o1 < 2^64 := by rw [e_o1]; exact hprepared.2.1
  have bo2 : o2 < 2^64 := by rw [e_o2]; exact hprepared.2.2.1
  have bo3 : o3 < 2^64 := by rw [e_o3]; exact hprepared.2.2.2.1
  have bo4 : o4 < 2^64 := by rw [e_o4]; exact hprepared.2.2.2.2.1
  have bo5 : o5 < 2^64 := by rw [e_o5]; exact hprepared.2.2.2.2.2.1
  have bo6 : o6 < 2^64 := by rw [e_o6]; exact hprepared.2.2.2.2.2.2.1
  have bo7 : o7 < 2^64 := by rw [e_o7]; exact hprepared.2.2.2.2.2.2.2.1
  have bo8 : o8 < 2^64 := by rw [e_o8]; exact hprepared.2.2.2.2.2.2.2.2.1
  have bmag : mag < 2^64 := by rw [e_mag]; exact hprepared.2.2.2.2.2.2.2.2.2
  obtain ⟨hfirst, hp0⟩ := mulSignedFirst_spec o0 mag bo0 bmag firstProduct e_firstProduct
  have bcarry : carry < 2^64 := by rw [e_carry]; exact hfirst.2
  obtain ⟨hround1, hp1⟩ := mulSignedRound_spec o1 mag carry bo1 bmag bcarry round1 e_round1
  have bcarry1 : carry_1 < 2^64 := by rw [e_carry_1]; exact hround1.2
  obtain ⟨hround2, hp2⟩ := mulSignedRound_spec o2 mag carry_1 bo2 bmag bcarry1 round2 e_round2
  have bcarry2 : carry_2 < 2^64 := by rw [e_carry_2]; exact hround2.2
  obtain ⟨hround3, hp3⟩ := mulSignedRound_spec o3 mag carry_2 bo3 bmag bcarry2 round3 e_round3
  have bcarry3 : carry_3 < 2^64 := by rw [e_carry_3]; exact hround3.2
  obtain ⟨hround4, hp4⟩ := mulSignedRound_spec o4 mag carry_3 bo4 bmag bcarry3 round4 e_round4
  have bcarry4 : carry_4 < 2^64 := by rw [e_carry_4]; exact hround4.2
  obtain ⟨hround5, hp5⟩ := mulSignedRound_spec o5 mag carry_4 bo5 bmag bcarry4 round5 e_round5
  have bcarry5 : carry_5 < 2^64 := by rw [e_carry_5]; exact hround5.2
  obtain ⟨hround6, hp6⟩ := mulSignedRound_spec o6 mag carry_5 bo6 bmag bcarry5 round6 e_round6
  have bcarry6 : carry_6 < 2^64 := by rw [e_carry_6]; exact hround6.2
  obtain ⟨hround7, hp7⟩ := mulSignedRound_spec o7 mag carry_6 bo7 bmag bcarry6 round7 e_round7
  have bcarry7 : carry_7 < 2^64 := by rw [e_carry_7]; exact hround7.2
  obtain ⟨hlast, topCarry, btopCarry, hp8⟩ :=
    mulSignedLast_spec o8 mag carry_7 bo8 bmag bcarry7 lastProduct e_lastProduct
  rw [← e_o0_1, ← e_carry] at hp0
  rw [← e_o1_1, ← e_carry_1] at hp1
  rw [← e_o2_1, ← e_carry_2] at hp2
  rw [← e_o3_1, ← e_carry_3] at hp3
  rw [← e_o4_1, ← e_carry_4] at hp4
  rw [← e_o5_1, ← e_carry_5] at hp5
  rw [← e_o6_1, ← e_carry_6] at hp6
  rw [← e_o7_1, ← e_carry_7] at hp7
  rw [← e_o8_1] at hp8
  have hproduct0 : o0_1 + 2^64 * carry = o0 * mag := hp0
  have hproduct1 := extendProductChain hproduct0 hp1
  have hproduct2 := extendProductChain hproduct1 hp2
  have hproduct3 := extendProductChain hproduct2 hp3
  have hproduct4 := extendProductChain hproduct3 hp4
  have hproduct5 := extendProductChain hproduct4 hp5
  have hproduct6 := extendProductChain hproduct5 hp6
  have hproduct7 := extendProductChain hproduct6 hp7
  have hproduct8 := extendProductChain hproduct7 hp8
  have hproduct :
      o0_1 + 2^64 * o1_1 + 2^128 * o2_1 + 2^192 * o3_1 +
          2^256 * o4_1 + 2^320 * o5_1 + 2^384 * o6_1 +
          2^448 * o7_1 + 2^512 * o8_1 + coefficientModulus * topCarry =
        preparedValue prepared * mag := by
    simp only [preparedValue, coefficientModulus]
    rw [← e_o0, ← e_o1, ← e_o2, ← e_o3, ← e_o4, ← e_o5, ← e_o6, ← e_o7,
      ← e_o8]
    simpa only [pow_succ] using hproduct8
  have bout0 : o0_1 < 2^64 := by rw [e_o0_1]; exact hfirst.1
  have bout1 : o1_1 < 2^64 := by rw [e_o1_1]; exact hround1.1
  have bout2 : o2_1 < 2^64 := by rw [e_o2_1]; exact hround2.1
  have bout3 : o3_1 < 2^64 := by rw [e_o3_1]; exact hround3.1
  have bout4 : o4_1 < 2^64 := by rw [e_o4_1]; exact hround4.1
  have bout5 : o5_1 < 2^64 := by rw [e_o5_1]; exact hround5.1
  have bout6 : o6_1 < 2^64 := by rw [e_o6_1]; exact hround6.1
  have bout7 : o7_1 < 2^64 := by rw [e_o7_1]; exact hround7.1
  have bout8 : o8_1 < 2^64 := by rw [e_o8_1]; exact hlast
  refine ⟨⟨bout0, bout1, bout2, bout3, bout4, bout5, bout6, bout7, bout8⟩, ?_⟩
  rcases hprepareCases with ⟨hs, hmag, hvalue⟩ | ⟨hs, hmag, carryNeg, bcarryNeg, hvalue⟩
  · left
    refine ⟨hs, ?_⟩
    have hout :
        o0_1 + 2^64 * o1_1 + 2^128 * o2_1 + 2^192 * o3_1 +
            2^256 * o4_1 + 2^320 * o5_1 + 2^384 * o6_1 +
            2^448 * o7_1 + 2^512 * o8_1 ≡ preparedValue prepared * mag
          [MOD coefficientModulus] :=
      modEq_of_add_mul _ _ topCarry 0 _
        (by simpa only [zero_mul, add_zero, Nat.mul_comm] using hproduct)
    rw [e_mag, hmag] at hout
    set_option exponentiation.threshold 600 in
      simpa only [WideLimbs.toNat, hvalue] using hout
  · right
    refine ⟨hs, ?_⟩
    have hpreparedMod : preparedValue prepared + value.toNat ≡ 0
        [MOD coefficientModulus] :=
      modEq_of_add_mul _ _ carryNeg 1 _ (by simpa [Nat.mul_comm] using hvalue)
    have hout :
        o0_1 + 2^64 * o1_1 + 2^128 * o2_1 + 2^192 * o3_1 +
            2^256 * o4_1 + 2^320 * o5_1 + 2^384 * o6_1 +
            2^448 * o7_1 + 2^512 * o8_1 ≡ preparedValue prepared * mag
          [MOD coefficientModulus] :=
      modEq_of_add_mul _ _ topCarry 0 _
        (by simpa only [zero_mul, add_zero, Nat.mul_comm] using hproduct)
    rw [e_mag, hmag] at hout
    have hsumMul := Nat.ModEq.mul_right (2^64 - scalar) hpreparedMod
    set_option exponentiation.threshold 600 in
      simpa only [WideLimbs.toNat] using
        hout.add_right (value.toNat * (2^64 - scalar)) |>.trans (by
          calc
            preparedValue prepared * (2^64 - scalar) + value.toNat * (2^64 - scalar)
                = (preparedValue prepared + value.toNat) * (2^64 - scalar) := by ring
            _ ≡ 0 * (2^64 - scalar) [MOD coefficientModulus] := hsumMul
            _ = 0 := by ring)
  -- END mulSigned conclusion

end PastaAsm.AArch64
