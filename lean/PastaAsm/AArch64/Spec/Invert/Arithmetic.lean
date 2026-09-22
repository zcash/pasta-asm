/-
Copyright Supranational LLC (the routines, transcribed from Semolina v0.1.4).
Copyright (c) 2026 the pasta-asm contributors (the transcription and the proofs).
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.Spec
import PastaAsm.AArch64.Transcription

/-!
# Correctness of AArch64 inversion arithmetic helpers

These proofs cover the straight-line fixed-width arithmetic helpers used by the inversion driver.
-/

namespace PastaAsm.AArch64

/-- The modulus of the nine-word wrapping coefficient representation, `2^576`. -/
abbrev coefficientModulus : Nat := 2^256 * 2^256 * 2^64

-- BEGIN reduceOnce_spec statement
/-- One conditional subtraction returns the input below the modulus and its exact difference
otherwise. The statement covers every pair of bounded four-limb values; the inversion driver's
`value < 2 * modulus` invariant is only needed by a caller to conclude that the output is reduced. -/
theorem reduceOnce_spec (value modulus : Limbs) (hv : value.Bounded) (hm : modulus.Bounded) :
    ∀ r, r = reduceOnce value modulus →
      r.Bounded ∧
        ((value.toNat < modulus.toNat ∧ r.toNat = value.toNat) ∨
          (modulus.toNat ≤ value.toNat ∧ r.toNat + modulus.toNat = value.toNat)) := by
  intro r hr
-- END reduceOnce_spec statement
  -- generated skeleton for `reduceOnce`: do not edit between the annotations
  unfold reduceOnce at hr
  lift_lets -merge at hr
  -- r0: argument
  extract_lets -merge +onlyGivenNames r0 at hr
  have e_r0 : r0 = value.l0 := rfl
  clear_value r0
  have b_r0 : r0 < 2^64 := by rw [e_r0]; exact hv.1
  -- r1: argument
  extract_lets -merge +onlyGivenNames r1 at hr
  have e_r1 : r1 = value.l1 := rfl
  clear_value r1
  have b_r1 : r1 < 2^64 := by rw [e_r1]; exact hv.2.1
  -- r2: argument
  extract_lets -merge +onlyGivenNames r2 at hr
  have e_r2 : r2 = value.l2 := rfl
  clear_value r2
  have b_r2 : r2 < 2^64 := by rw [e_r2]; exact hv.2.2.1
  -- r3: argument
  extract_lets -merge +onlyGivenNames r3 at hr
  have e_r3 : r3 = value.l3 := rfl
  clear_value r3
  have b_r3 : r3 < 2^64 := by rw [e_r3]; exact hv.2.2.2
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
  -- p2: argument
  extract_lets -merge +onlyGivenNames p2 at hr
  have e_p2 : p2 = modulus.l2 := rfl
  clear_value p2
  have b_p2 : p2 < 2^64 := by rw [e_p2]; exact hm.2.2.1
  -- p3: argument
  extract_lets -merge +onlyGivenNames p3 at hr
  have e_p3 : p3 = modulus.l3 := rfl
  clear_value p3
  have b_p3 : p3 < 2^64 := by rw [e_p3]; exact hm.2.2.2
  -- t0: subs t0,r0,p0
  extract_lets -merge +onlyGivenNames s t0 c at hr
  have e_t0 : t0 = (r0 + 2^64 - p0 - (1 - 1)) % 2^64 := rfl
  have e_c : c = (r0 + 2^64 - p0 - (1 - 1)) / 2^64 := rfl
  clear_value s t0 c
  have l_t0 : t0 + 2^64 * c + p0 + 1 = r0 + 2^64 + 1 := by
    rw [e_t0, e_c]; exact subc_lin r0 p0 1 b_p0 (by decide)
  have b_t0 : t0 < 2^64 := by rw [e_t0]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c : c ≤ 1 := by
    rw [e_c]; exact subc_carry_le_one r0 p0 1 b_r0
  clear e_t0 e_c
  -- t1: sbcs t1,r1,p1
  extract_lets -merge +onlyGivenNames s_1 t1 c_1 at hr
  have e_t1 : t1 = (r1 + 2^64 - p1 - (1 - c)) % 2^64 := rfl
  have e_c_1 : c_1 = (r1 + 2^64 - p1 - (1 - c)) / 2^64 := rfl
  clear_value s_1 t1 c_1
  have l_t1 : t1 + 2^64 * c_1 + p1 + 1 = r1 + 2^64 + c := by
    rw [e_t1, e_c_1]; exact subc_lin r1 p1 c b_p1 b_c
  have b_t1 : t1 < 2^64 := by rw [e_t1]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_1 : c_1 ≤ 1 := by
    rw [e_c_1]; exact subc_carry_le_one r1 p1 c b_r1
  clear e_t1 e_c_1
  -- t2: sbcs t2,r2,p2
  extract_lets -merge +onlyGivenNames s_2 t2 c_2 at hr
  have e_t2 : t2 = (r2 + 2^64 - p2 - (1 - c_1)) % 2^64 := rfl
  have e_c_2 : c_2 = (r2 + 2^64 - p2 - (1 - c_1)) / 2^64 := rfl
  clear_value s_2 t2 c_2
  have l_t2 : t2 + 2^64 * c_2 + p2 + 1 = r2 + 2^64 + c_1 := by
    rw [e_t2, e_c_2]; exact subc_lin r2 p2 c_1 b_p2 b_c_1
  have b_t2 : t2 < 2^64 := by rw [e_t2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_2 : c_2 ≤ 1 := by
    rw [e_c_2]; exact subc_carry_le_one r2 p2 c_1 b_r2
  clear e_t2 e_c_2
  -- t3: sbcs t3,r3,p3
  extract_lets -merge +onlyGivenNames s_3 t3 c_3 at hr
  have e_t3 : t3 = (r3 + 2^64 - p3 - (1 - c_2)) % 2^64 := rfl
  have e_c_3 : c_3 = (r3 + 2^64 - p3 - (1 - c_2)) / 2^64 := rfl
  clear_value s_3 t3 c_3
  have l_t3 : t3 + 2^64 * c_3 + p3 + 1 = r3 + 2^64 + c_2 := by
    rw [e_t3, e_c_3]; exact subc_lin r3 p3 c_2 b_p3 b_c_2
  have b_t3 : t3 < 2^64 := by rw [e_t3]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_3 : c_3 ≤ 1 := by
    rw [e_c_3]; exact subc_carry_le_one r3 p3 c_2 b_r3
  clear e_t3 e_c_3
  -- r0_1: csel r0,t0,r0,cs
  extract_lets -merge +onlyGivenNames r0_1 at hr
  have e_r0_1 : r0_1 = (if c_3 = 0 then r0 else t0) := rfl
  clear_value r0_1
  have b_r0_1 : r0_1 < 2^64 := by
    rw [e_r0_1]; split <;> first | exact b_r0 | exact b_t0
  -- r1_1: csel r1,t1,r1,cs
  extract_lets -merge +onlyGivenNames r1_1 at hr
  have e_r1_1 : r1_1 = (if c_3 = 0 then r1 else t1) := rfl
  clear_value r1_1
  have b_r1_1 : r1_1 < 2^64 := by
    rw [e_r1_1]; split <;> first | exact b_r1 | exact b_t1
  -- r2_1: csel r2,t2,r2,cs
  extract_lets -merge +onlyGivenNames r2_1 at hr
  have e_r2_1 : r2_1 = (if c_3 = 0 then r2 else t2) := rfl
  clear_value r2_1
  have b_r2_1 : r2_1 < 2^64 := by
    rw [e_r2_1]; split <;> first | exact b_r2 | exact b_t2
  -- r3_1: csel r3,t3,r3,cs
  extract_lets -merge +onlyGivenNames r3_1 at hr
  have e_r3_1 : r3_1 = (if c_3 = 0 then r3 else t3) := rfl
  clear_value r3_1
  have b_r3_1 : r3_1 < 2^64 := by
    rw [e_r3_1]; split <;> first | exact b_r3 | exact b_t3
  subst hr
  -- BEGIN reduceOnce conclusion
  have hV : value.toNat = r0 + 2^64 * r1 + 2^128 * r2 + 2^192 * r3 := by
    rw [e_r0, e_r1, e_r2, e_r3]; rfl
  have hP : modulus.toNat = p0 + 2^64 * p1 + 2^128 * p2 + 2^192 * p3 := by
    rw [e_p0, e_p1, e_p2, e_p3]; rfl
  have hD : t0 + 2^64 * t1 + 2^128 * t2 + 2^192 * t3 + modulus.toNat + 2^256 * c_3
      = value.toNat + 2^256 := by
    rw [hV, hP]
    clear * - l_t0 l_t1 l_t2 l_t3
    omega
  refine ⟨⟨b_r0_1, b_r1_1, b_r2_1, b_r3_1⟩, ?_⟩
  show (value.toNat < modulus.toNat ∧
      r0_1 + 2^64 * r1_1 + 2^128 * r2_1 + 2^192 * r3_1 = value.toNat) ∨
    (modulus.toNat ≤ value.toNat ∧
      r0_1 + 2^64 * r1_1 + 2^128 * r2_1 + 2^192 * r3_1 + modulus.toNat = value.toNat)
  obtain hc | hc : c_3 = 0 ∨ c_3 = 1 := by clear * - b_c_3; omega
  · rw [if_pos hc] at e_r0_1 e_r1_1 e_r2_1 e_r3_1
    left
    clear * - hV hP hD hc e_r0_1 e_r1_1 e_r2_1 e_r3_1
      b_t0 b_t1 b_t2 b_t3 b_r0 b_r1 b_r2 b_r3 b_p0 b_p1 b_p2 b_p3
    omega
  · rw [if_neg (by clear * - hc; omega)] at e_r0_1 e_r1_1 e_r2_1 e_r3_1
    right
    clear * - hD hc e_r0_1 e_r1_1 e_r2_1 e_r3_1
    omega
  -- END reduceOnce conclusion

-- BEGIN addWords_spec statement
/-- Nine-word addition is exact modulo `2^576`: the returned words and the one discarded carry
reconstruct the full sum. -/
theorem addWords_spec (lhs rhs : WideLimbs) (hlhs : lhs.Bounded) (hrhs : rhs.Bounded) :
    ∀ r, r = addWords lhs rhs →
      r.Bounded ∧ ∃ carry, carry ≤ 1 ∧
        r.toNat + coefficientModulus * carry = lhs.toNat + rhs.toNat := by
  intro r hr
-- END addWords_spec statement
  -- generated skeleton for `addWords`: do not edit between the annotations
  unfold addWords at hr
  lift_lets -merge at hr
  -- o0: argument
  extract_lets -merge +onlyGivenNames o0 at hr
  have e_o0 : o0 = lhs.l0 := rfl
  clear_value o0
  have b_o0 : o0 < 2^64 := by rw [e_o0]; exact hlhs.1
  -- o1: argument
  extract_lets -merge +onlyGivenNames o1 at hr
  have e_o1 : o1 = lhs.l1 := rfl
  clear_value o1
  have b_o1 : o1 < 2^64 := by rw [e_o1]; exact hlhs.2.1
  -- o2: argument
  extract_lets -merge +onlyGivenNames o2 at hr
  have e_o2 : o2 = lhs.l2 := rfl
  clear_value o2
  have b_o2 : o2 < 2^64 := by rw [e_o2]; exact hlhs.2.2.1
  -- o3: argument
  extract_lets -merge +onlyGivenNames o3 at hr
  have e_o3 : o3 = lhs.l3 := rfl
  clear_value o3
  have b_o3 : o3 < 2^64 := by rw [e_o3]; exact hlhs.2.2.2.1
  -- o4: argument
  extract_lets -merge +onlyGivenNames o4 at hr
  have e_o4 : o4 = lhs.l4 := rfl
  clear_value o4
  have b_o4 : o4 < 2^64 := by rw [e_o4]; exact hlhs.2.2.2.2.1
  -- o5: argument
  extract_lets -merge +onlyGivenNames o5 at hr
  have e_o5 : o5 = lhs.l5 := rfl
  clear_value o5
  have b_o5 : o5 < 2^64 := by rw [e_o5]; exact hlhs.2.2.2.2.2.1
  -- o6: argument
  extract_lets -merge +onlyGivenNames o6 at hr
  have e_o6 : o6 = lhs.l6 := rfl
  clear_value o6
  have b_o6 : o6 < 2^64 := by rw [e_o6]; exact hlhs.2.2.2.2.2.2.1
  -- o7: argument
  extract_lets -merge +onlyGivenNames o7 at hr
  have e_o7 : o7 = lhs.l7 := rfl
  clear_value o7
  have b_o7 : o7 < 2^64 := by rw [e_o7]; exact hlhs.2.2.2.2.2.2.2.1
  -- o8: argument
  extract_lets -merge +onlyGivenNames o8 at hr
  have e_o8 : o8 = lhs.l8 := rfl
  clear_value o8
  have b_o8 : o8 < 2^64 := by rw [e_o8]; exact hlhs.2.2.2.2.2.2.2.2
  -- r0: argument
  extract_lets -merge +onlyGivenNames r0 at hr
  have e_r0 : r0 = rhs.l0 := rfl
  clear_value r0
  have b_r0 : r0 < 2^64 := by rw [e_r0]; exact hrhs.1
  -- r1: argument
  extract_lets -merge +onlyGivenNames r1 at hr
  have e_r1 : r1 = rhs.l1 := rfl
  clear_value r1
  have b_r1 : r1 < 2^64 := by rw [e_r1]; exact hrhs.2.1
  -- r2: argument
  extract_lets -merge +onlyGivenNames r2 at hr
  have e_r2 : r2 = rhs.l2 := rfl
  clear_value r2
  have b_r2 : r2 < 2^64 := by rw [e_r2]; exact hrhs.2.2.1
  -- r3: argument
  extract_lets -merge +onlyGivenNames r3 at hr
  have e_r3 : r3 = rhs.l3 := rfl
  clear_value r3
  have b_r3 : r3 < 2^64 := by rw [e_r3]; exact hrhs.2.2.2.1
  -- r4: argument
  extract_lets -merge +onlyGivenNames r4 at hr
  have e_r4 : r4 = rhs.l4 := rfl
  clear_value r4
  have b_r4 : r4 < 2^64 := by rw [e_r4]; exact hrhs.2.2.2.2.1
  -- r5: argument
  extract_lets -merge +onlyGivenNames r5 at hr
  have e_r5 : r5 = rhs.l5 := rfl
  clear_value r5
  have b_r5 : r5 < 2^64 := by rw [e_r5]; exact hrhs.2.2.2.2.2.1
  -- r6: argument
  extract_lets -merge +onlyGivenNames r6 at hr
  have e_r6 : r6 = rhs.l6 := rfl
  clear_value r6
  have b_r6 : r6 < 2^64 := by rw [e_r6]; exact hrhs.2.2.2.2.2.2.1
  -- r7: argument
  extract_lets -merge +onlyGivenNames r7 at hr
  have e_r7 : r7 = rhs.l7 := rfl
  clear_value r7
  have b_r7 : r7 < 2^64 := by rw [e_r7]; exact hrhs.2.2.2.2.2.2.2.1
  -- r8: argument
  extract_lets -merge +onlyGivenNames r8 at hr
  have e_r8 : r8 = rhs.l8 := rfl
  clear_value r8
  have b_r8 : r8 < 2^64 := by rw [e_r8]; exact hrhs.2.2.2.2.2.2.2.2
  -- o0_1: adds o0,o0,r0
  extract_lets -merge +onlyGivenNames s o0_1 c at hr
  have e_o0_1 : o0_1 = (o0 + r0 + 0) % 2^64 := rfl
  have e_c : c = (o0 + r0 + 0) / 2^64 := rfl
  clear_value s o0_1 c
  have l_o0_1 : o0_1 + 2^64 * c = o0 + r0 + 0 := by
    rw [e_o0_1, e_c]; exact Nat.mod_add_div _ _
  have b_o0_1 : o0_1 < 2^64 := by rw [e_o0_1]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c : c ≤ 1 := by
    rw [e_c]; exact addc_carry_le_one o0 r0 0 b_o0 b_r0 (by decide)
  clear e_o0_1 e_c
  -- o1_1: adcs o1,o1,r1
  extract_lets -merge +onlyGivenNames s_1 o1_1 c_1 at hr
  have e_o1_1 : o1_1 = (o1 + r1 + c) % 2^64 := rfl
  have e_c_1 : c_1 = (o1 + r1 + c) / 2^64 := rfl
  clear_value s_1 o1_1 c_1
  have l_o1_1 : o1_1 + 2^64 * c_1 = o1 + r1 + c := by
    rw [e_o1_1, e_c_1]; exact Nat.mod_add_div _ _
  have b_o1_1 : o1_1 < 2^64 := by rw [e_o1_1]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_1 : c_1 ≤ 1 := by
    rw [e_c_1]; exact addc_carry_le_one o1 r1 c b_o1 b_r1 b_c
  clear e_o1_1 e_c_1
  -- o2_1: adcs o2,o2,r2
  extract_lets -merge +onlyGivenNames s_2 o2_1 c_2 at hr
  have e_o2_1 : o2_1 = (o2 + r2 + c_1) % 2^64 := rfl
  have e_c_2 : c_2 = (o2 + r2 + c_1) / 2^64 := rfl
  clear_value s_2 o2_1 c_2
  have l_o2_1 : o2_1 + 2^64 * c_2 = o2 + r2 + c_1 := by
    rw [e_o2_1, e_c_2]; exact Nat.mod_add_div _ _
  have b_o2_1 : o2_1 < 2^64 := by rw [e_o2_1]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_2 : c_2 ≤ 1 := by
    rw [e_c_2]; exact addc_carry_le_one o2 r2 c_1 b_o2 b_r2 b_c_1
  clear e_o2_1 e_c_2
  -- o3_1: adcs o3,o3,r3
  extract_lets -merge +onlyGivenNames s_3 o3_1 c_3 at hr
  have e_o3_1 : o3_1 = (o3 + r3 + c_2) % 2^64 := rfl
  have e_c_3 : c_3 = (o3 + r3 + c_2) / 2^64 := rfl
  clear_value s_3 o3_1 c_3
  have l_o3_1 : o3_1 + 2^64 * c_3 = o3 + r3 + c_2 := by
    rw [e_o3_1, e_c_3]; exact Nat.mod_add_div _ _
  have b_o3_1 : o3_1 < 2^64 := by rw [e_o3_1]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_3 : c_3 ≤ 1 := by
    rw [e_c_3]; exact addc_carry_le_one o3 r3 c_2 b_o3 b_r3 b_c_2
  clear e_o3_1 e_c_3
  -- o4_1: adcs o4,o4,r4
  extract_lets -merge +onlyGivenNames s_4 o4_1 c_4 at hr
  have e_o4_1 : o4_1 = (o4 + r4 + c_3) % 2^64 := rfl
  have e_c_4 : c_4 = (o4 + r4 + c_3) / 2^64 := rfl
  clear_value s_4 o4_1 c_4
  have l_o4_1 : o4_1 + 2^64 * c_4 = o4 + r4 + c_3 := by
    rw [e_o4_1, e_c_4]; exact Nat.mod_add_div _ _
  have b_o4_1 : o4_1 < 2^64 := by rw [e_o4_1]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_4 : c_4 ≤ 1 := by
    rw [e_c_4]; exact addc_carry_le_one o4 r4 c_3 b_o4 b_r4 b_c_3
  clear e_o4_1 e_c_4
  -- o5_1: adcs o5,o5,r5
  extract_lets -merge +onlyGivenNames s_5 o5_1 c_5 at hr
  have e_o5_1 : o5_1 = (o5 + r5 + c_4) % 2^64 := rfl
  have e_c_5 : c_5 = (o5 + r5 + c_4) / 2^64 := rfl
  clear_value s_5 o5_1 c_5
  have l_o5_1 : o5_1 + 2^64 * c_5 = o5 + r5 + c_4 := by
    rw [e_o5_1, e_c_5]; exact Nat.mod_add_div _ _
  have b_o5_1 : o5_1 < 2^64 := by rw [e_o5_1]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_5 : c_5 ≤ 1 := by
    rw [e_c_5]; exact addc_carry_le_one o5 r5 c_4 b_o5 b_r5 b_c_4
  clear e_o5_1 e_c_5
  -- o6_1: adcs o6,o6,r6
  extract_lets -merge +onlyGivenNames s_6 o6_1 c_6 at hr
  have e_o6_1 : o6_1 = (o6 + r6 + c_5) % 2^64 := rfl
  have e_c_6 : c_6 = (o6 + r6 + c_5) / 2^64 := rfl
  clear_value s_6 o6_1 c_6
  have l_o6_1 : o6_1 + 2^64 * c_6 = o6 + r6 + c_5 := by
    rw [e_o6_1, e_c_6]; exact Nat.mod_add_div _ _
  have b_o6_1 : o6_1 < 2^64 := by rw [e_o6_1]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_6 : c_6 ≤ 1 := by
    rw [e_c_6]; exact addc_carry_le_one o6 r6 c_5 b_o6 b_r6 b_c_5
  clear e_o6_1 e_c_6
  -- o7_1: adcs o7,o7,r7
  extract_lets -merge +onlyGivenNames s_7 o7_1 c_7 at hr
  have e_o7_1 : o7_1 = (o7 + r7 + c_6) % 2^64 := rfl
  have e_c_7 : c_7 = (o7 + r7 + c_6) / 2^64 := rfl
  clear_value s_7 o7_1 c_7
  have l_o7_1 : o7_1 + 2^64 * c_7 = o7 + r7 + c_6 := by
    rw [e_o7_1, e_c_7]; exact Nat.mod_add_div _ _
  have b_o7_1 : o7_1 < 2^64 := by rw [e_o7_1]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_7 : c_7 ≤ 1 := by
    rw [e_c_7]; exact addc_carry_le_one o7 r7 c_6 b_o7 b_r7 b_c_6
  clear e_o7_1 e_c_7
  -- o8_1: adc o8,o8,r8
  extract_lets -merge +onlyGivenNames o8_1 at hr
  have e_o8_1 : o8_1 = (o8 + r8 + c_7) % 2^64 := rfl
  clear_value o8_1
  have b_o8_1 : o8_1 < 2^64 := by rw [e_o8_1]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨k_o8_1, b_k_o8_1, l_o8_1⟩ :
      ∃ k, k ≤ 1 ∧ o8_1 + 2^64 * k = o8 + r8 + c_7 :=
    ⟨(o8 + r8 + c_7) / 2^64, addc_carry_le_one o8 r8 c_7 b_o8 b_r8 b_c_7,
      by rw [e_o8_1]; exact Nat.mod_add_div _ _⟩
  clear e_o8_1
  subst hr
  -- BEGIN addWords conclusion
  refine ⟨⟨b_o0_1, b_o1_1, b_o2_1, b_o3_1, b_o4_1, b_o5_1, b_o6_1, b_o7_1, b_o8_1⟩,
    k_o8_1, b_k_o8_1, ?_⟩
  simp only [WideLimbs.toNat, coefficientModulus]
  rw [← e_o0, ← e_o1, ← e_o2, ← e_o3, ← e_o4, ← e_o5, ← e_o6, ← e_o7, ← e_o8,
    ← e_r0, ← e_r1, ← e_r2, ← e_r3, ← e_r4, ← e_r5, ← e_r6, ← e_r7, ← e_r8]
  clear * - l_o0_1 l_o1_1 l_o2_1 l_o3_1 l_o4_1 l_o5_1 l_o6_1 l_o7_1 l_o8_1
  omega
  -- END addWords conclusion

-- BEGIN inversion arithmetic corollaries
/-- `addWords` computes the sum modulo the nine-word representation modulus. -/
theorem addWords_modEq (lhs rhs : WideLimbs) (hlhs : lhs.Bounded) (hrhs : rhs.Bounded) :
    (addWords lhs rhs).toNat ≡ lhs.toNat + rhs.toNat [MOD coefficientModulus] := by
  obtain ⟨_, carry, _, h⟩ := addWords_spec lhs rhs hlhs hrhs _ rfl
  exact modEq_of_add_mul _ _ carry 0 _ (by simpa [Nat.mul_comm] using h)

/-- Under the inversion driver's one-subtraction precondition, `reduceOnce` returns a canonical
representative with the same residue. -/
theorem reduceOnce_spec_of_lt_two (value modulus : Limbs) (hv : value.Bounded)
    (hm : modulus.Bounded) (hlt : value.toNat < 2 * modulus.toNat) :
    (reduceOnce value modulus).Bounded ∧
      (reduceOnce value modulus).toNat < modulus.toNat ∧
      (reduceOnce value modulus).toNat ≡ value.toNat [MOD modulus.toNat] := by
  obtain ⟨hb, hcases⟩ := reduceOnce_spec value modulus hv hm _ rfl
  refine ⟨hb, ?_⟩
  rcases hcases with ⟨hbelow, heq⟩ | ⟨habove, heq⟩
  · exact ⟨by omega, by rw [heq]⟩
  · refine ⟨by omega, modEq_of_add_mul _ _ 1 0 _ ?_⟩
    simpa using heq
-- END inversion arithmetic corollaries

end PastaAsm.AArch64
