/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.X86_64.Spec.Invert.Arithmetic
import PastaAsm.X86_64.Compositions
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.NormNum

/-!
# Correctness of the x86-64 inversion arithmetic compositions

The Rust inversion driver composes the generated one-limb helpers into five- and nine-word
loops.  These theorems expose the actual carry threaded through each loop and give numeric
specifications modulo the corresponding fixed-width representation.
-/

set_option exponentiation.threshold 600

namespace PastaAsm

namespace WideLimbs

/-- Unsigned interpretation of the first five words used by `update_ab`. -/
def toNat5 (x : WideLimbs) : Nat :=
  x.l0 + 2^64 * x.l1 + 2^128 * x.l2 + 2^192 * x.l3 + 2^256 * x.l4

end WideLimbs

namespace X86_64

/-- The modulus of the five-word temporary used by `update_ab`. -/
abbrev updateModulus : Nat := 2^320

/-- The modulus of the nine-word wrapping coefficient representation. -/
abbrev coefficientModulus : Nat := 2^576

private theorem bt_zero : bt 0 0 = 0 := by
  norm_num [bt, bit, lsr, word, regMod]

private theorem bt_eq_self_of_le_one {c : Nat} (hc : c ≤ 1) : bt c 0 = c := by
  obtain rfl | rfl : c = 0 ∨ c = 1 := by omega
  · exact bt_zero
  · norm_num [bt, bit, lsr, word, regMod]

/-- Five-word addition exposes the actual carry discarded above word four and reconstructs the
full sum exactly.  The upper four output words are zero by construction. -/
theorem addWords5_spec (lhs rhs : PastaAsm.WideLimbs)
    (hlhs : lhs.Bounded) (hrhs : rhs.Bounded) :
    (addWords5 lhs rhs).Bounded ∧
      ∃ carry, carry ≤ 1 ∧
        (addWords5 lhs rhs).toNat5 + updateModulus * carry =
          lhs.toNat5 + rhs.toNat5 := by
  let s0 := addWordsLimb lhs.l0 rhs.l0 0
  let s1 := addWordsLimb lhs.l1 rhs.l1 s0.carry
  let s2 := addWordsLimb lhs.l2 rhs.l2 s1.carry
  let s3 := addWordsLimb lhs.l3 rhs.l3 s2.carry
  let s4 := addWordsLimb lhs.l4 rhs.l4 s3.carry
  obtain ⟨b0, bc0, h0⟩ := addWordsLimb_spec lhs.l0 rhs.l0 0 hlhs.1 hrhs.1 (by decide) s0 rfl
  obtain ⟨b1, bc1, h1⟩ := addWordsLimb_spec lhs.l1 rhs.l1 s0.carry hlhs.2.1 hrhs.2.1
    (by omega) s1 rfl
  obtain ⟨b2, bc2, h2⟩ := addWordsLimb_spec lhs.l2 rhs.l2 s1.carry hlhs.2.2.1 hrhs.2.2.1
    (by omega) s2 rfl
  obtain ⟨b3, bc3, h3⟩ := addWordsLimb_spec lhs.l3 rhs.l3 s2.carry hlhs.2.2.2.1 hrhs.2.2.2.1
    (by omega) s3 rfl
  obtain ⟨b4, bc4, h4⟩ := addWordsLimb_spec lhs.l4 rhs.l4 s3.carry hlhs.2.2.2.2.1 hrhs.2.2.2.2.1
    (by omega) s4 rfl
  rw [bt_zero] at h0
  rw [bt_eq_self_of_le_one bc0] at h1
  rw [bt_eq_self_of_le_one bc1] at h2
  rw [bt_eq_self_of_le_one bc2] at h3
  rw [bt_eq_self_of_le_one bc3] at h4
  have hout : addWords5 lhs rhs =
      (⟨s0.value, s1.value, s2.value, s3.value, s4.value, 0, 0, 0, 0⟩ : PastaAsm.WideLimbs) := by
    rfl
  rw [hout]
  refine ⟨⟨b0, b1, b2, b3, b4, by norm_num [regMod], by norm_num [regMod],
    by norm_num [regMod], by norm_num [regMod]⟩, s4.carry, bc4, ?_⟩
  simp only [PastaAsm.WideLimbs.toNat5, updateModulus]
  clear * - h0 h1 h2 h3 h4
  omega

/-- Nine-word addition exposes the actual carry discarded above word eight and reconstructs the
full sum exactly. -/
theorem addWords9_spec (lhs rhs : PastaAsm.WideLimbs)
    (hlhs : lhs.Bounded) (hrhs : rhs.Bounded) :
    (addWords9 lhs rhs).Bounded ∧
      ∃ carry, carry ≤ 1 ∧
        (addWords9 lhs rhs).toNat + coefficientModulus * carry =
          lhs.toNat + rhs.toNat := by
  let s0 := addWordsLimb lhs.l0 rhs.l0 0
  let s1 := addWordsLimb lhs.l1 rhs.l1 s0.carry
  let s2 := addWordsLimb lhs.l2 rhs.l2 s1.carry
  let s3 := addWordsLimb lhs.l3 rhs.l3 s2.carry
  let s4 := addWordsLimb lhs.l4 rhs.l4 s3.carry
  let s5 := addWordsLimb lhs.l5 rhs.l5 s4.carry
  let s6 := addWordsLimb lhs.l6 rhs.l6 s5.carry
  let s7 := addWordsLimb lhs.l7 rhs.l7 s6.carry
  let s8 := addWordsLimb lhs.l8 rhs.l8 s7.carry
  obtain ⟨b0, bc0, h0⟩ := addWordsLimb_spec lhs.l0 rhs.l0 0 hlhs.1 hrhs.1 (by decide) s0 rfl
  obtain ⟨b1, bc1, h1⟩ := addWordsLimb_spec lhs.l1 rhs.l1 s0.carry hlhs.2.1 hrhs.2.1
    (by omega) s1 rfl
  obtain ⟨b2, bc2, h2⟩ := addWordsLimb_spec lhs.l2 rhs.l2 s1.carry hlhs.2.2.1 hrhs.2.2.1
    (by omega) s2 rfl
  obtain ⟨b3, bc3, h3⟩ := addWordsLimb_spec lhs.l3 rhs.l3 s2.carry hlhs.2.2.2.1 hrhs.2.2.2.1
    (by omega) s3 rfl
  obtain ⟨b4, bc4, h4⟩ := addWordsLimb_spec lhs.l4 rhs.l4 s3.carry hlhs.2.2.2.2.1 hrhs.2.2.2.2.1
    (by omega) s4 rfl
  obtain ⟨b5, bc5, h5⟩ := addWordsLimb_spec lhs.l5 rhs.l5 s4.carry hlhs.2.2.2.2.2.1 hrhs.2.2.2.2.2.1
    (by omega) s5 rfl
  obtain ⟨b6, bc6, h6⟩ := addWordsLimb_spec lhs.l6 rhs.l6 s5.carry hlhs.2.2.2.2.2.2.1 hrhs.2.2.2.2.2.2.1
    (by omega) s6 rfl
  obtain ⟨b7, bc7, h7⟩ := addWordsLimb_spec lhs.l7 rhs.l7 s6.carry hlhs.2.2.2.2.2.2.2.1 hrhs.2.2.2.2.2.2.2.1
    (by omega) s7 rfl
  obtain ⟨b8, bc8, h8⟩ := addWordsLimb_spec lhs.l8 rhs.l8 s7.carry hlhs.2.2.2.2.2.2.2.2 hrhs.2.2.2.2.2.2.2.2
    (by omega) s8 rfl
  rw [bt_zero] at h0
  rw [bt_eq_self_of_le_one bc0] at h1
  rw [bt_eq_self_of_le_one bc1] at h2
  rw [bt_eq_self_of_le_one bc2] at h3
  rw [bt_eq_self_of_le_one bc3] at h4
  rw [bt_eq_self_of_le_one bc4] at h5
  rw [bt_eq_self_of_le_one bc5] at h6
  rw [bt_eq_self_of_le_one bc6] at h7
  rw [bt_eq_self_of_le_one bc7] at h8
  have hout : addWords9 lhs rhs =
      (⟨s0.value, s1.value, s2.value, s3.value, s4.value,
        s5.value, s6.value, s7.value, s8.value⟩ : PastaAsm.WideLimbs) := by
    rfl
  rw [hout]
  refine ⟨⟨b0, b1, b2, b3, b4, b5, b6, b7, b8⟩, s8.carry, bc8, ?_⟩
  simp only [PastaAsm.WideLimbs.toNat, coefficientModulus]
  clear * - h0 h1 h2 h3 h4 h5 h6 h7 h8
  omega

/-- Five-word addition computes its numeric sum modulo `2^320`. -/
theorem addWords5_modEq (lhs rhs : PastaAsm.WideLimbs)
    (hlhs : lhs.Bounded) (hrhs : rhs.Bounded) :
    (addWords5 lhs rhs).toNat5 ≡ lhs.toNat5 + rhs.toNat5 [MOD updateModulus] := by
  obtain ⟨_, carry, _, h⟩ := addWords5_spec lhs rhs hlhs hrhs
  exact modEq_of_add_mul _ _ carry 0 _ (by simpa [Nat.mul_comm] using h)

/-- Nine-word addition computes its numeric sum modulo `2^576`. -/
theorem addWords9_modEq (lhs rhs : PastaAsm.WideLimbs)
    (hlhs : lhs.Bounded) (hrhs : rhs.Bounded) :
    (addWords9 lhs rhs).toNat ≡ lhs.toNat + rhs.toNat [MOD coefficientModulus] := by
  obtain ⟨_, carry, _, h⟩ := addWords9_spec lhs rhs hlhs hrhs
  exact modEq_of_add_mul _ _ carry 0 _ (by simpa [Nat.mul_comm] using h)

private theorem mulSignedLimb_spec_noTop
    (limb sign negateCarry magnitude productCarry : Nat)
    (hlimb : limb < 2^64) (hsign : sign < 2^64) (hnegateCarry : negateCarry < 2^64)
    (hmagnitude : magnitude < 2^64) (hproductCarry : productCarry < 2^64) :
    ∀ r, r = mulSignedLimb limb sign negateCarry magnitude productCarry →
      r.low < 2^64 ∧ r.high < 2^64 ∧ r.negateCarry ≤ 1 ∧
        ∃ transformed, transformed < 2^64 ∧
          transformed + 2^64 * r.negateCarry = bitXor limb sign + negateCarry ∧
          r.low + 2^64 * r.high = transformed * magnitude + productCarry := by
  intro r hr
  obtain ⟨blow, bhigh, bneg, transformed, topCarry, btransformed, btop,
    htransform, hproduct⟩ := mulSignedLimb_spec limb sign negateCarry magnitude productCarry
      hlimb hsign hnegateCarry hmagnitude hproductCarry r hr
  have hmul := Nat.mul_le_mul (Nat.le_sub_one_of_lt btransformed)
    (Nat.le_sub_one_of_lt hmagnitude)
  have hpc := Nat.le_sub_one_of_lt hproductCarry
  have htop : topCarry = 0 := by
    norm_num at hmul hpc ⊢
    omega
  refine ⟨blow, bhigh, bneg, transformed, btransformed, htransform, ?_⟩
  rw [htop, mul_zero, add_zero] at hproduct
  exact hproduct

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

private theorem extendTransformChain {acc carry base bit radix transformed next xorLimb : Nat}
    (hacc : acc + radix * carry = base + bit)
    (hstep : transformed + 2^64 * next = xorLimb + carry) :
    acc + radix * transformed + (radix * 2^64) * next =
      base + radix * xorLimb + bit := by
  calc
    _ = acc + radix * (transformed + 2^64 * next) := by ring
    _ = acc + radix * (xorLimb + carry) := by rw [hstep]
    _ = (acc + radix * carry) + radix * xorLimb := by ring
    _ = (base + bit) + radix * xorLimb := by rw [hacc]
    _ = _ := by ring

private theorem signedScalar_bounds (scalar : Nat) :
    (signedScalar scalar).sign < 2^64 ∧
      (signedScalar scalar).signBit < 2^64 ∧
      (signedScalar scalar).magnitude < 2^64 := by
  unfold signedScalar
  dsimp only
  split
  · exact ⟨by norm_num [regMod], by norm_num, word_lt _⟩
  · exact ⟨by norm_num [regMod], by norm_num [regMod], word_lt _⟩

/-- The five helper invocations preserve two exact loop invariants.  `transformed` is the complete
five-word two's-complement preprocessing of the input; `productCarry` is the actual high product
word discarded by `mulSigned5`, and `negateCarry` is the actual final preprocessing carry. -/
theorem mulSigned5_bridge (value : PastaAsm.WideLimbs) (scalar : Nat) (hv : value.Bounded) :
    (mulSigned5 value scalar).Bounded ∧
      ∃ transformed productCarry negateCarry,
        transformed < updateModulus ∧ productCarry < 2^64 ∧ negateCarry ≤ 1 ∧
        transformed + updateModulus * negateCarry =
          bitXor value.l0 (signedScalar scalar).sign +
            2^64 * bitXor value.l1 (signedScalar scalar).sign +
            2^128 * bitXor value.l2 (signedScalar scalar).sign +
            2^192 * bitXor value.l3 (signedScalar scalar).sign +
            2^256 * bitXor value.l4 (signedScalar scalar).sign +
            (signedScalar scalar).signBit ∧
        (mulSigned5 value scalar).toNat5 + updateModulus * productCarry =
          transformed * (signedScalar scalar).magnitude := by
  let ss := signedScalar scalar
  let s0 := mulSignedLimb value.l0 ss.sign ss.signBit ss.magnitude 0
  let s1 := mulSignedLimb value.l1 ss.sign s0.negateCarry ss.magnitude s0.high
  let s2 := mulSignedLimb value.l2 ss.sign s1.negateCarry ss.magnitude s1.high
  let s3 := mulSignedLimb value.l3 ss.sign s2.negateCarry ss.magnitude s2.high
  let s4 := mulSignedLimb value.l4 ss.sign s3.negateCarry ss.magnitude s3.high
  obtain ⟨bsign, bsignBit, bmag⟩ := signedScalar_bounds scalar
  change ss.sign < 2^64 at bsign
  change ss.signBit < 2^64 at bsignBit
  change ss.magnitude < 2^64 at bmag
  obtain ⟨bl0, bh0, bn0, t0, bt0, ht0, hp0⟩ :=
    mulSignedLimb_spec_noTop value.l0 ss.sign ss.signBit ss.magnitude 0
      hv.1 bsign bsignBit bmag (by decide) s0 rfl
  obtain ⟨bl1, bh1, bn1, t1, bt1, ht1, hp1⟩ :=
    mulSignedLimb_spec_noTop value.l1 ss.sign s0.negateCarry ss.magnitude s0.high
      hv.2.1 bsign (by omega) bmag bh0 s1 rfl
  obtain ⟨bl2, bh2, bn2, t2, bt2, ht2, hp2⟩ :=
    mulSignedLimb_spec_noTop value.l2 ss.sign s1.negateCarry ss.magnitude s1.high
      hv.2.2.1 bsign (by omega) bmag bh1 s2 rfl
  obtain ⟨bl3, bh3, bn3, t3, bt3, ht3, hp3⟩ :=
    mulSignedLimb_spec_noTop value.l3 ss.sign s2.negateCarry ss.magnitude s2.high
      hv.2.2.2.1 bsign (by omega) bmag bh2 s3 rfl
  obtain ⟨bl4, bh4, bn4, t4, bt4, ht4, hp4⟩ :=
    mulSignedLimb_spec_noTop value.l4 ss.sign s3.negateCarry ss.magnitude s3.high
      hv.2.2.2.2.1 bsign (by omega) bmag bh3 s4 rfl
  have htransform0 : t0 + 2^64 * s0.negateCarry =
      bitXor value.l0 ss.sign + ss.signBit := ht0
  have htransform1 := extendTransformChain htransform0 ht1
  have htransform2 := extendTransformChain htransform1 ht2
  have htransform3 := extendTransformChain htransform2 ht3
  have htransform4 := extendTransformChain htransform3 ht4
  have hproduct0 : s0.low + 2^64 * s0.high = t0 * ss.magnitude := by
    simpa using hp0
  have hproduct1 := extendProductChain hproduct0 hp1
  have hproduct2 := extendProductChain hproduct1 hp2
  have hproduct3 := extendProductChain hproduct2 hp3
  have hproduct4 := extendProductChain hproduct3 hp4
  have hout : mulSigned5 value scalar =
      (⟨s0.low, s1.low, s2.low, s3.low, s4.low, 0, 0, 0, 0⟩ : PastaAsm.WideLimbs) := by
    rfl
  rw [hout]
  refine ⟨⟨bl0, bl1, bl2, bl3, bl4, by norm_num [regMod], by norm_num [regMod],
    by norm_num [regMod], by norm_num [regMod]⟩,
    t0 + 2^64 * t1 + 2^128 * t2 + 2^192 * t3 + 2^256 * t4,
    s4.high, s4.negateCarry, ?_, bh4, bn4, ?_, ?_⟩
  · simp only [updateModulus]
    clear * - bt0 bt1 bt2 bt3 bt4
    omega
  · change t0 + 2^64 * t1 + 2^128 * t2 + 2^192 * t3 + 2^256 * t4 +
      updateModulus * s4.negateCarry =
        bitXor value.l0 ss.sign + 2^64 * bitXor value.l1 ss.sign +
          2^128 * bitXor value.l2 ss.sign + 2^192 * bitXor value.l3 ss.sign +
          2^256 * bitXor value.l4 ss.sign + ss.signBit
    simpa only [updateModulus, pow_succ] using htransform4
  · simp only [PastaAsm.WideLimbs.toNat5, updateModulus]
    simpa only [pow_succ] using hproduct4

/-- The nine helper invocations preserve the same exact preprocessing and multiplication invariants
at coefficient width. -/
theorem mulSigned9_bridge (value : PastaAsm.WideLimbs) (scalar : Nat) (hv : value.Bounded) :
    (mulSigned9 value scalar).Bounded ∧
      ∃ transformed productCarry negateCarry,
        transformed < coefficientModulus ∧ productCarry < 2^64 ∧ negateCarry ≤ 1 ∧
        transformed + coefficientModulus * negateCarry =
          bitXor value.l0 (signedScalar scalar).sign +
            2^64 * bitXor value.l1 (signedScalar scalar).sign +
            2^128 * bitXor value.l2 (signedScalar scalar).sign +
            2^192 * bitXor value.l3 (signedScalar scalar).sign +
            2^256 * bitXor value.l4 (signedScalar scalar).sign +
            2^320 * bitXor value.l5 (signedScalar scalar).sign +
            2^384 * bitXor value.l6 (signedScalar scalar).sign +
            2^448 * bitXor value.l7 (signedScalar scalar).sign +
            2^512 * bitXor value.l8 (signedScalar scalar).sign +
            (signedScalar scalar).signBit ∧
        (mulSigned9 value scalar).toNat + coefficientModulus * productCarry =
          transformed * (signedScalar scalar).magnitude := by
  let ss := signedScalar scalar
  let s0 := mulSignedLimb value.l0 ss.sign ss.signBit ss.magnitude 0
  let s1 := mulSignedLimb value.l1 ss.sign s0.negateCarry ss.magnitude s0.high
  let s2 := mulSignedLimb value.l2 ss.sign s1.negateCarry ss.magnitude s1.high
  let s3 := mulSignedLimb value.l3 ss.sign s2.negateCarry ss.magnitude s2.high
  let s4 := mulSignedLimb value.l4 ss.sign s3.negateCarry ss.magnitude s3.high
  let s5 := mulSignedLimb value.l5 ss.sign s4.negateCarry ss.magnitude s4.high
  let s6 := mulSignedLimb value.l6 ss.sign s5.negateCarry ss.magnitude s5.high
  let s7 := mulSignedLimb value.l7 ss.sign s6.negateCarry ss.magnitude s6.high
  let s8 := mulSignedLimb value.l8 ss.sign s7.negateCarry ss.magnitude s7.high
  obtain ⟨bsign, bsignBit, bmag⟩ := signedScalar_bounds scalar
  change ss.sign < 2^64 at bsign
  change ss.signBit < 2^64 at bsignBit
  change ss.magnitude < 2^64 at bmag
  obtain ⟨bl0, bh0, bn0, t0, bt0, ht0, hp0⟩ :=
    mulSignedLimb_spec_noTop value.l0 ss.sign ss.signBit ss.magnitude 0
      hv.1 bsign bsignBit bmag (by decide) s0 rfl
  obtain ⟨bl1, bh1, bn1, t1, bt1, ht1, hp1⟩ :=
    mulSignedLimb_spec_noTop value.l1 ss.sign s0.negateCarry ss.magnitude s0.high
      hv.2.1 bsign (by omega) bmag bh0 s1 rfl
  obtain ⟨bl2, bh2, bn2, t2, bt2, ht2, hp2⟩ :=
    mulSignedLimb_spec_noTop value.l2 ss.sign s1.negateCarry ss.magnitude s1.high
      hv.2.2.1 bsign (by omega) bmag bh1 s2 rfl
  obtain ⟨bl3, bh3, bn3, t3, bt3, ht3, hp3⟩ :=
    mulSignedLimb_spec_noTop value.l3 ss.sign s2.negateCarry ss.magnitude s2.high
      hv.2.2.2.1 bsign (by omega) bmag bh2 s3 rfl
  obtain ⟨bl4, bh4, bn4, t4, bt4, ht4, hp4⟩ :=
    mulSignedLimb_spec_noTop value.l4 ss.sign s3.negateCarry ss.magnitude s3.high
      hv.2.2.2.2.1 bsign (by omega) bmag bh3 s4 rfl
  obtain ⟨bl5, bh5, bn5, t5, bt5, ht5, hp5⟩ :=
    mulSignedLimb_spec_noTop value.l5 ss.sign s4.negateCarry ss.magnitude s4.high
      hv.2.2.2.2.2.1 bsign (by omega) bmag bh4 s5 rfl
  obtain ⟨bl6, bh6, bn6, t6, bt6, ht6, hp6⟩ :=
    mulSignedLimb_spec_noTop value.l6 ss.sign s5.negateCarry ss.magnitude s5.high
      hv.2.2.2.2.2.2.1 bsign (by omega) bmag bh5 s6 rfl
  obtain ⟨bl7, bh7, bn7, t7, bt7, ht7, hp7⟩ :=
    mulSignedLimb_spec_noTop value.l7 ss.sign s6.negateCarry ss.magnitude s6.high
      hv.2.2.2.2.2.2.2.1 bsign (by omega) bmag bh6 s7 rfl
  obtain ⟨bl8, bh8, bn8, t8, bt8, ht8, hp8⟩ :=
    mulSignedLimb_spec_noTop value.l8 ss.sign s7.negateCarry ss.magnitude s7.high
      hv.2.2.2.2.2.2.2.2 bsign (by omega) bmag bh7 s8 rfl
  have htransform0 : t0 + 2^64 * s0.negateCarry =
      bitXor value.l0 ss.sign + ss.signBit := ht0
  have htransform1 := extendTransformChain htransform0 ht1
  have htransform2 := extendTransformChain htransform1 ht2
  have htransform3 := extendTransformChain htransform2 ht3
  have htransform4 := extendTransformChain htransform3 ht4
  have htransform5 := extendTransformChain htransform4 ht5
  have htransform6 := extendTransformChain htransform5 ht6
  have htransform7 := extendTransformChain htransform6 ht7
  have htransform8 := extendTransformChain htransform7 ht8
  have hproduct0 : s0.low + 2^64 * s0.high = t0 * ss.magnitude := by
    simpa using hp0
  have hproduct1 := extendProductChain hproduct0 hp1
  have hproduct2 := extendProductChain hproduct1 hp2
  have hproduct3 := extendProductChain hproduct2 hp3
  have hproduct4 := extendProductChain hproduct3 hp4
  have hproduct5 := extendProductChain hproduct4 hp5
  have hproduct6 := extendProductChain hproduct5 hp6
  have hproduct7 := extendProductChain hproduct6 hp7
  have hproduct8 := extendProductChain hproduct7 hp8
  have hout : mulSigned9 value scalar =
      (⟨s0.low, s1.low, s2.low, s3.low, s4.low, s5.low, s6.low, s7.low, s8.low⟩ :
        PastaAsm.WideLimbs) := by
    rfl
  rw [hout]
  refine ⟨⟨bl0, bl1, bl2, bl3, bl4, bl5, bl6, bl7, bl8⟩,
    t0 + 2^64 * t1 + 2^128 * t2 + 2^192 * t3 + 2^256 * t4 +
      2^320 * t5 + 2^384 * t6 + 2^448 * t7 + 2^512 * t8,
    s8.high, s8.negateCarry, ?_, bh8, bn8, ?_, ?_⟩
  · simp only [coefficientModulus]
    clear * - bt0 bt1 bt2 bt3 bt4 bt5 bt6 bt7 bt8
    omega
  · change t0 + 2^64 * t1 + 2^128 * t2 + 2^192 * t3 + 2^256 * t4 +
      2^320 * t5 + 2^384 * t6 + 2^448 * t7 + 2^512 * t8 +
      coefficientModulus * s8.negateCarry =
        bitXor value.l0 ss.sign + 2^64 * bitXor value.l1 ss.sign +
          2^128 * bitXor value.l2 ss.sign + 2^192 * bitXor value.l3 ss.sign +
          2^256 * bitXor value.l4 ss.sign + 2^320 * bitXor value.l5 ss.sign +
          2^384 * bitXor value.l6 ss.sign + 2^448 * bitXor value.l7 ss.sign +
          2^512 * bitXor value.l8 ss.sign + ss.signBit
    simpa only [coefficientModulus, pow_succ] using htransform8
  · simp only [PastaAsm.WideLimbs.toNat, coefficientModulus]
    simpa only [pow_succ] using hproduct8

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

private theorem bitXor_zero_of_lt {x : Nat} (hx : x < 2^64) : bitXor x 0 = x := by
  unfold bitXor
  rw [word_eq_of_lt hx, word_zero, Nat.xor_zero, word_eq_of_lt hx]

private theorem bitXor_allOnes {x : Nat} (hx : x < 2^64) :
    bitXor x (2^64 - 1) = 2^64 - 1 - x := by
  unfold bitXor
  rw [word_eq_of_lt hx]
  have hall : 2^64 - 1 < regMod := by simp only [regMod]; omega
  rw [word_eq_of_lt hall, natXor_allOnes hx]
  exact word_eq_of_lt (by simp only [regMod]; omega)

private theorem signedScalar_nonnegative {scalar : Nat} (hscalar : scalar < 2^64)
    (hsign : scalar < 2^63) : signedScalar scalar = ⟨0, 0, scalar⟩ := by
  unfold signedScalar
  dsimp only
  rw [word_eq_of_lt hscalar, if_pos hsign]
  norm_num [word, regMod]
  simpa only [Nat.reducePow] using hscalar

private theorem signedScalar_negative {scalar : Nat} (hscalar : scalar < 2^64)
    (hsign : 2^63 ≤ scalar) : signedScalar scalar = ⟨2^64 - 1, 1, 2^64 - scalar⟩ := by
  have hnlt : ¬ scalar < 2^63 := by omega
  have hpos : 0 < scalar := by omega
  unfold signedScalar
  dsimp only
  rw [word_eq_of_lt hscalar, if_neg hnlt]
  simp only [regMod]
  rw [natXor_allOnes hscalar]
  have hadd : 2^64 - 1 - scalar + (2^64 - 1) % 2 = 2^64 - scalar := by
    norm_num
    omega
  rw [hadd]
  have hmag : 2^64 - scalar < 2^64 := by omega
  rw [word_eq_of_lt hmag]

private theorem complementFive_eq (value : PastaAsm.WideLimbs) (hv : value.Bounded) :
    bitXor value.l0 (2^64 - 1) +
        2^64 * bitXor value.l1 (2^64 - 1) +
        2^128 * bitXor value.l2 (2^64 - 1) +
        2^192 * bitXor value.l3 (2^64 - 1) +
        2^256 * bitXor value.l4 (2^64 - 1) + value.toNat5 + 1 =
      updateModulus := by
  rw [bitXor_allOnes hv.1, bitXor_allOnes hv.2.1, bitXor_allOnes hv.2.2.1,
    bitXor_allOnes hv.2.2.2.1, bitXor_allOnes hv.2.2.2.2.1]
  simp only [PastaAsm.WideLimbs.toNat5, updateModulus]
  obtain ⟨h0, h1, h2, h3, h4, _⟩ := hv
  simp only [regMod] at h0 h1 h2 h3 h4
  have c0 : 2^64 - 1 - value.l0 + value.l0 = 2^64 - 1 := by omega
  have c1 : 2^64 - 1 - value.l1 + value.l1 = 2^64 - 1 := by omega
  have c2 : 2^64 - 1 - value.l2 + value.l2 = 2^64 - 1 := by omega
  have c3 : 2^64 - 1 - value.l3 + value.l3 = 2^64 - 1 := by omega
  have c4 : 2^64 - 1 - value.l4 + value.l4 = 2^64 - 1 := by omega
  calc
    _ = (2^64 - 1 - value.l0 + value.l0) +
        2^64 * (2^64 - 1 - value.l1 + value.l1) +
        2^128 * (2^64 - 1 - value.l2 + value.l2) +
        2^192 * (2^64 - 1 - value.l3 + value.l3) +
        2^256 * (2^64 - 1 - value.l4 + value.l4) + 1 := by ring
    _ = _ := by
      rw [c0, c1, c2, c3, c4]
      set_option exponentiation.threshold 400 in norm_num

/-- Multiplication by a signed 64-bit scalar bitpattern modulo the five-word `update_ab`
representation.  The negative case states congruence to `-value * (2^64 - scalar)`. -/
theorem mulSigned5_spec (value : PastaAsm.WideLimbs) (scalar : Nat)
    (hv : value.Bounded) (hscalar : scalar < 2^64) :
    (mulSigned5 value scalar).Bounded ∧
      ((scalar < 2^63 ∧
          (mulSigned5 value scalar).toNat5 ≡ value.toNat5 * scalar [MOD updateModulus]) ∨
        (2^63 ≤ scalar ∧
          (mulSigned5 value scalar).toNat5 + value.toNat5 * (2^64 - scalar) ≡ 0
            [MOD updateModulus])) := by
  obtain ⟨hb, transformed, productCarry, negateCarry, bt, bpc, bnc,
    htransform, hproduct⟩ := mulSigned5_bridge value scalar hv
  refine ⟨hb, ?_⟩
  by_cases hs : scalar < 2^63
  · left
    have hss := signedScalar_nonnegative hscalar hs
    rw [hss] at htransform hproduct
    rw [bitXor_zero_of_lt hv.1, bitXor_zero_of_lt hv.2.1,
      bitXor_zero_of_lt hv.2.2.1, bitXor_zero_of_lt hv.2.2.2.1,
      bitXor_zero_of_lt hv.2.2.2.2.1] at htransform
    have htransformed : transformed ≡ value.toNat5 [MOD updateModulus] :=
      modEq_of_add_mul _ _ negateCarry 0 _ (by
        simpa only [PastaAsm.WideLimbs.toNat5, add_zero, zero_mul, Nat.mul_comm] using htransform)
    have hout : (mulSigned5 value scalar).toNat5 ≡ transformed * scalar
        [MOD updateModulus] :=
      modEq_of_add_mul _ _ productCarry 0 _
        (by simpa only [zero_mul, add_zero, Nat.mul_comm] using hproduct)
    exact ⟨hs, hout.trans (Nat.ModEq.mul_right scalar htransformed)⟩
  · right
    have hsge : 2^63 ≤ scalar := by omega
    have hss := signedScalar_negative hscalar hsge
    rw [hss] at htransform hproduct
    have hcomplement := complementFive_eq value hv
    have hneg : transformed + value.toNat5 + updateModulus * negateCarry =
        updateModulus := by
      calc
        _ = (transformed + updateModulus * negateCarry) + value.toNat5 := by ring
        _ = (bitXor value.l0 (2^64 - 1) +
              2^64 * bitXor value.l1 (2^64 - 1) +
              2^128 * bitXor value.l2 (2^64 - 1) +
              2^192 * bitXor value.l3 (2^64 - 1) +
              2^256 * bitXor value.l4 (2^64 - 1) + 1) + value.toNat5 := by
                rw [htransform]
        _ = updateModulus := by
          rw [← hcomplement]
          ring
    have hsum : transformed + value.toNat5 ≡ 0 [MOD updateModulus] :=
      modEq_of_add_mul _ _ negateCarry 1 _ (by simpa [Nat.mul_comm] using hneg)
    have hout : (mulSigned5 value scalar).toNat5 ≡
        transformed * (2^64 - scalar) [MOD updateModulus] :=
      modEq_of_add_mul _ _ productCarry 0 _
        (by simpa only [zero_mul, add_zero, Nat.mul_comm] using hproduct)
    have hsumMul := Nat.ModEq.mul_right (2^64 - scalar) hsum
    refine ⟨hsge, ?_⟩
    calc
      (mulSigned5 value scalar).toNat5 + value.toNat5 * (2^64 - scalar)
          ≡ transformed * (2^64 - scalar) + value.toNat5 * (2^64 - scalar)
              [MOD updateModulus] := Nat.ModEq.add_right _ hout
      _ = (transformed + value.toNat5) * (2^64 - scalar) := by ring
      _ ≡ 0 * (2^64 - scalar) [MOD updateModulus] := hsumMul
      _ = 0 := by ring

private theorem complementNine_eq (value : PastaAsm.WideLimbs) (hv : value.Bounded) :
    bitXor value.l0 (2^64 - 1) +
        2^64 * bitXor value.l1 (2^64 - 1) +
        2^128 * bitXor value.l2 (2^64 - 1) +
        2^192 * bitXor value.l3 (2^64 - 1) +
        2^256 * bitXor value.l4 (2^64 - 1) +
        2^320 * bitXor value.l5 (2^64 - 1) +
        2^384 * bitXor value.l6 (2^64 - 1) +
        2^448 * bitXor value.l7 (2^64 - 1) +
        2^512 * bitXor value.l8 (2^64 - 1) + value.toNat + 1 =
      coefficientModulus := by
  rw [bitXor_allOnes hv.1, bitXor_allOnes hv.2.1, bitXor_allOnes hv.2.2.1,
    bitXor_allOnes hv.2.2.2.1, bitXor_allOnes hv.2.2.2.2.1,
    bitXor_allOnes hv.2.2.2.2.2.1, bitXor_allOnes hv.2.2.2.2.2.2.1,
    bitXor_allOnes hv.2.2.2.2.2.2.2.1, bitXor_allOnes hv.2.2.2.2.2.2.2.2]
  simp only [PastaAsm.WideLimbs.toNat, coefficientModulus]
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
        2^512 * (2^64 - 1 - value.l8 + value.l8) + 1 := by ring
    _ = _ := by
      rw [c0, c1, c2, c3, c4, c5, c6, c7, c8]
      set_option exponentiation.threshold 600 in norm_num

/-- Multiplication by a signed 64-bit scalar bitpattern modulo the nine-word coefficient
representation.  This is the composition contract consumed by coefficient linear combinations. -/
theorem mulSigned9_spec (value : PastaAsm.WideLimbs) (scalar : Nat)
    (hv : value.Bounded) (hscalar : scalar < 2^64) :
    (mulSigned9 value scalar).Bounded ∧
      ((scalar < 2^63 ∧
          (mulSigned9 value scalar).toNat ≡ value.toNat * scalar [MOD coefficientModulus]) ∨
        (2^63 ≤ scalar ∧
          (mulSigned9 value scalar).toNat + value.toNat * (2^64 - scalar) ≡ 0
            [MOD coefficientModulus])) := by
  obtain ⟨hb, transformed, productCarry, negateCarry, bt, bpc, bnc,
    htransform, hproduct⟩ := mulSigned9_bridge value scalar hv
  refine ⟨hb, ?_⟩
  by_cases hs : scalar < 2^63
  · left
    have hss := signedScalar_nonnegative hscalar hs
    rw [hss] at htransform hproduct
    rw [bitXor_zero_of_lt hv.1, bitXor_zero_of_lt hv.2.1,
      bitXor_zero_of_lt hv.2.2.1, bitXor_zero_of_lt hv.2.2.2.1,
      bitXor_zero_of_lt hv.2.2.2.2.1, bitXor_zero_of_lt hv.2.2.2.2.2.1,
      bitXor_zero_of_lt hv.2.2.2.2.2.2.1, bitXor_zero_of_lt hv.2.2.2.2.2.2.2.1,
      bitXor_zero_of_lt hv.2.2.2.2.2.2.2.2] at htransform
    have htransformed : transformed ≡ value.toNat [MOD coefficientModulus] :=
      modEq_of_add_mul _ _ negateCarry 0 _ (by
        simpa only [PastaAsm.WideLimbs.toNat, add_zero, zero_mul, Nat.mul_comm] using htransform)
    have hout : (mulSigned9 value scalar).toNat ≡ transformed * scalar
        [MOD coefficientModulus] :=
      modEq_of_add_mul _ _ productCarry 0 _
        (by simpa only [zero_mul, add_zero, Nat.mul_comm] using hproduct)
    exact ⟨hs, hout.trans (Nat.ModEq.mul_right scalar htransformed)⟩
  · right
    have hsge : 2^63 ≤ scalar := by omega
    have hss := signedScalar_negative hscalar hsge
    rw [hss] at htransform hproduct
    have hcomplement := complementNine_eq value hv
    have hneg : transformed + value.toNat + coefficientModulus * negateCarry =
        coefficientModulus := by
      calc
        _ = (transformed + coefficientModulus * negateCarry) + value.toNat := by ring
        _ = (bitXor value.l0 (2^64 - 1) +
              2^64 * bitXor value.l1 (2^64 - 1) +
              2^128 * bitXor value.l2 (2^64 - 1) +
              2^192 * bitXor value.l3 (2^64 - 1) +
              2^256 * bitXor value.l4 (2^64 - 1) +
              2^320 * bitXor value.l5 (2^64 - 1) +
              2^384 * bitXor value.l6 (2^64 - 1) +
              2^448 * bitXor value.l7 (2^64 - 1) +
              2^512 * bitXor value.l8 (2^64 - 1) + 1) + value.toNat := by
                rw [htransform]
        _ = coefficientModulus := by
          rw [← hcomplement]
          ring
    have hsum : transformed + value.toNat ≡ 0 [MOD coefficientModulus] :=
      modEq_of_add_mul _ _ negateCarry 1 _ (by simpa [Nat.mul_comm] using hneg)
    have hout : (mulSigned9 value scalar).toNat ≡
        transformed * (2^64 - scalar) [MOD coefficientModulus] :=
      modEq_of_add_mul _ _ productCarry 0 _
        (by simpa only [zero_mul, add_zero, Nat.mul_comm] using hproduct)
    have hsumMul := Nat.ModEq.mul_right (2^64 - scalar) hsum
    refine ⟨hsge, ?_⟩
    calc
      (mulSigned9 value scalar).toNat + value.toNat * (2^64 - scalar)
          ≡ transformed * (2^64 - scalar) + value.toNat * (2^64 - scalar)
              [MOD coefficientModulus] := Nat.ModEq.add_right _ hout
      _ = (transformed + value.toNat) * (2^64 - scalar) := by ring
      _ ≡ 0 * (2^64 - scalar) [MOD coefficientModulus] := hsumMul
      _ = 0 := by ring

end X86_64

end PastaAsm
