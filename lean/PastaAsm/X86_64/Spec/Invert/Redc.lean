/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.Fields
import PastaAsm.InversionNormalization
import PastaAsm.Spec
import PastaAsm.X86_64.Spec.Arithmetic
import PastaAsm.X86_64.Transcription
import Mathlib.Tactic.NormNum

/-!
# Correctness of x86-64 full-width Montgomery reduction

The generated trace is split into four uncorrected low-half cancellation rounds.  The block then
adds the original high half, retaining its fifth carry through the final conditional subtraction.
The result is a bounded lazy residue; it is deliberately not claimed to be canonical.
-/

namespace PastaAsm.X86_64

-- BEGIN redcMont arithmetic helpers
/-- The bounded low word in a radix split is the remainder. -/
private theorem redcMont_split_low {lo hi x : Nat} (hlo : lo < 2^64)
    (h : lo + 2^64 * hi = x) : lo = x % 2^64 := by
  rw [← h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo]

/-- A product of two 64-bit words has high word at most `2^64 - 2`. -/
private theorem redcMont_mul_high_le {a b lo hi : Nat} (ha : a < 2^64) (hb : b < 2^64)
    (h : lo + 2^64 * hi = a * b) : hi ≤ 2^64 - 2 := by
  have hp := Nat.mul_le_mul (Nat.le_sub_one_of_lt ha) (Nat.le_sub_one_of_lt hb)
  norm_num at hp
  omega

/-- One cancellation-and-shift phase of the full-width REDC schedule. -/
private theorem redcMont_step
    {x0 x1 x2 x3 q p0 p1 p3 p0lo p0hi p1lo p1hi p3lo p3hi
      u0 c0 u1 c1 v1 c2 v1hi c3 o0 c4 o1 c5 top c6
      v3 c7 v3hi c8 o2 c9 o3 c10 : Nat}
    (hc : x0 + p0lo = 2^64 * c0)
    (dp0 : p0lo + 2^64 * p0hi = q * p0)
    (dp1 : p1lo + 2^64 * p1hi = q * p1)
    (dp3 : p3lo + 2^64 * p3hi = q * p3)
    (lu0 : u0 + 2^64 * c0 = x0 + p0lo)
    (lu1 : u1 + 2^64 * c1 = u0 + p0hi + c0)
    (lv1 : v1 + 2^64 * c2 = x1 + p1lo)
    (lv1hi : v1hi + 2^64 * c3 = p1hi + c2)
    (lo0 : o0 + 2^64 * c4 = v1 + u1)
    (lo1 : o1 + 2^64 * c5 = x2 + v1hi + c4)
    (ltop : top + 2^64 * c6 = c5)
    (lv3 : v3 + 2^64 * c7 = x3 + p3lo)
    (lv3hi : v3hi + 2^64 * c8 = p3hi + c7)
    (lo2 : o2 + 2^64 * c9 = v3 + top)
    (lo3 : o3 + 2^64 * c10 = v3hi + c9)
    (hz : u0 = 0 ∧ c1 = 0 ∧ c3 = 0 ∧ c6 = 0 ∧ c8 = 0 ∧ c10 = 0) :
    2^64 * (o0 + 2^64 * o1 + 2^128 * o2 + 2^192 * o3) =
      (x0 + 2^64 * x1 + 2^128 * x2 + 2^192 * x3) +
        q * (p0 + 2^64 * p1 + 2^192 * p3) := by
  have hproduct : q * (p0 + 2^64 * p1 + 2^192 * p3) =
      q * p0 + 2^64 * (q * p1) + 2^192 * (q * p3) := by ring
  rw [hproduct]
  omega
-- END redcMont arithmetic helpers

-- BEGIN redcMont traced statement
set_option exponentiation.threshold 512 in
private theorem redcMont_spec_traced (product : WideLimbs) (modulus : Limbs) (inv : Nat)
    (hproduct : product.Bounded) (hm : modulus.Bounded)
    (hshape : modulus.l2 = 0 ∧ modulus.l3 = 2^62)
    (hinv : inv < 2^64) (hinvP : (inv * modulus.l0 + 1) % 2^64 = 0) :
    ∀ r, r = redcMont product modulus inv →
      r.Bounded ∧ 2^256 * r.toNat ≡ product.toNat [MOD modulus.toNat] := by
  intro r hr
-- END redcMont traced statement
  -- generated skeleton for `redcMont`: do not edit between the annotations
  unfold redcMont at hr
  lift_lets at hr
  -- inv': input inv
  extract_lets +onlyGivenNames inv' at hr
  have e_inv' : inv' = inv := rfl
  have b_inv' : inv' < 2^64 := by rw [e_inv']; exact hinv
  -- rax: mov rax, qword ptr [{value}]
  extract_lets +onlyGivenNames rax at hr
  have e_rax : rax = product.l0 := rfl
  have b_rax : rax < 2^64 := by rw [e_rax]; exact hproduct.1
  -- a1: mov {a1}, qword ptr [{value} + 8]
  extract_lets +onlyGivenNames a1 at hr
  have e_a1 : a1 = product.l1 := rfl
  have b_a1 : a1 < 2^64 := by rw [e_a1]; exact hproduct.2.1
  -- a2: mov {a2}, qword ptr [{value} + 16]
  extract_lets +onlyGivenNames a2 at hr
  have e_a2 : a2 = product.l2 := rfl
  have b_a2 : a2 < 2^64 := by rw [e_a2]; exact hproduct.2.2.1
  -- a3: mov {a3}, qword ptr [{value} + 24]
  extract_lets +onlyGivenNames a3 at hr
  have e_a3 : a3 = product.l3 := rfl
  have b_a3 : a3 < 2^64 := by rw [e_a3]; exact hproduct.2.2.2.1
  -- a4: mov {a4}, rax
  extract_lets +onlyGivenNames a4 at hr
  have e_a4 : a4 = rax := rfl
  have b_a4 : a4 < 2^64 := by rw [e_a4]; exact b_rax
  -- rax_1: imul rax, {inv}
  extract_lets +onlyGivenNames rax_1 at hr
  have e_rax_1 : rax_1 = rax * inv' % 2^64 := rfl
  have b_rax_1 : rax_1 < 2^64 := by rw [e_rax_1]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- q: mov {q}, rax
  extract_lets +onlyGivenNames q at hr
  have e_q : q = rax_1 := rfl
  have b_q : q < 2^64 := by rw [e_q]; exact b_rax_1
  -- rdx: mul qword ptr [{p}]
  extract_lets +onlyGivenNames rdx at hr
  have e_rdx : rdx = rax_1 * modulus.l0 / 2^64 := rfl
  have p_rdx : rax_1 * modulus.l0 < 2^64 * 2^64 := Nat.mul_lt_mul'' b_rax_1 hm.1
  have b_rdx : rdx < 2^64 := by rw [e_rdx]; exact Nat.div_lt_of_lt_mul p_rdx
  obtain ⟨lo_rdx, b_lo_rdx, d_rdx⟩ :
      ∃ lo, lo < 2^64 ∧ lo + 2^64 * rdx = rax_1 * modulus.l0 :=
    ⟨rax_1 * modulus.l0 % 2^64, Nat.mod_lt _ (Nat.two_pow_pos _),
      by rw [e_rdx]; exact Nat.mod_add_div _ _⟩
  clear e_rdx
  -- rax_2: None
  extract_lets +onlyGivenNames rax_2 at hr
  have e_rax_2 : rax_2 = rax_1 * modulus.l0 % 2^64 := rfl
  have b_rax_2 : rax_2 < 2^64 := by rw [e_rax_2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- a4_1: add {a4}, rax
  extract_lets +onlyGivenNames s a4_1 cf at hr
  have e_a4_1 : a4_1 = (addc a4 rax_2 0).1 := rfl
  have e_cf : cf = (addc a4 rax_2 0).2 := rfl
  have l_a4_1 : a4_1 + 2^64 * cf = a4 + rax_2 + 0 := by
    rw [e_a4_1, e_cf]; exact addc_lin a4 rax_2 0
  have b_a4_1 : a4_1 < 2^64 := by rw [e_a4_1]; exact addc_value_lt a4 rax_2 0
  have b_cf : cf ≤ 1 := by rw [e_cf]; exact addc_carry_le_one a4 rax_2 0 b_a4 b_rax_2 (by decide)
  clear e_a4_1 e_cf
  -- rax_3: mov rax, {q}
  extract_lets +onlyGivenNames rax_3 at hr
  have e_rax_3 : rax_3 = q := rfl
  have b_rax_3 : rax_3 < 2^64 := by rw [e_rax_3]; exact b_q
  -- a4_2: adc {a4}, rdx
  extract_lets +onlyGivenNames s_1 a4_2 cf_1 at hr
  have e_a4_2 : a4_2 = (addc a4_1 rdx cf).1 := rfl
  have e_cf_1 : cf_1 = (addc a4_1 rdx cf).2 := rfl
  have l_a4_2 : a4_2 + 2^64 * cf_1 = a4_1 + rdx + cf := by
    rw [e_a4_2, e_cf_1]; exact addc_lin a4_1 rdx cf
  have b_a4_2 : a4_2 < 2^64 := by rw [e_a4_2]; exact addc_value_lt a4_1 rdx cf
  have b_cf_1 : cf_1 ≤ 1 := by rw [e_cf_1]; exact addc_carry_le_one a4_1 rdx cf b_a4_1 b_rdx b_cf
  clear e_a4_2 e_cf_1
  -- rdx_1: mul qword ptr [{p} + 8]
  extract_lets +onlyGivenNames rdx_1 at hr
  have e_rdx_1 : rdx_1 = rax_3 * modulus.l1 / 2^64 := rfl
  have p_rdx_1 : rax_3 * modulus.l1 < 2^64 * 2^64 := Nat.mul_lt_mul'' b_rax_3 hm.2.1
  have b_rdx_1 : rdx_1 < 2^64 := by rw [e_rdx_1]; exact Nat.div_lt_of_lt_mul p_rdx_1
  obtain ⟨lo_rdx_1, b_lo_rdx_1, d_rdx_1⟩ :
      ∃ lo, lo < 2^64 ∧ lo + 2^64 * rdx_1 = rax_3 * modulus.l1 :=
    ⟨rax_3 * modulus.l1 % 2^64, Nat.mod_lt _ (Nat.two_pow_pos _),
      by rw [e_rdx_1]; exact Nat.mod_add_div _ _⟩
  clear e_rdx_1
  -- rax_4: None
  extract_lets +onlyGivenNames rax_4 at hr
  have e_rax_4 : rax_4 = rax_3 * modulus.l1 % 2^64 := rfl
  have b_rax_4 : rax_4 < 2^64 := by rw [e_rax_4]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- a1_1: add {a1}, rax
  extract_lets +onlyGivenNames s_2 a1_1 cf_2 at hr
  have e_a1_1 : a1_1 = (addc a1 rax_4 0).1 := rfl
  have e_cf_2 : cf_2 = (addc a1 rax_4 0).2 := rfl
  have l_a1_1 : a1_1 + 2^64 * cf_2 = a1 + rax_4 + 0 := by
    rw [e_a1_1, e_cf_2]; exact addc_lin a1 rax_4 0
  have b_a1_1 : a1_1 < 2^64 := by rw [e_a1_1]; exact addc_value_lt a1 rax_4 0
  have b_cf_2 : cf_2 ≤ 1 := by rw [e_cf_2]; exact addc_carry_le_one a1 rax_4 0 b_a1 b_rax_4 (by decide)
  clear e_a1_1 e_cf_2
  -- rdx_2: adc rdx, 0
  extract_lets +onlyGivenNames s_3 rdx_2 cf_3 at hr
  have e_rdx_2 : rdx_2 = (addc rdx_1 0 cf_2).1 := rfl
  have e_cf_3 : cf_3 = (addc rdx_1 0 cf_2).2 := rfl
  have l_rdx_2 : rdx_2 + 2^64 * cf_3 = rdx_1 + 0 + cf_2 := by
    rw [e_rdx_2, e_cf_3]; exact addc_lin rdx_1 0 cf_2
  have b_rdx_2 : rdx_2 < 2^64 := by rw [e_rdx_2]; exact addc_value_lt rdx_1 0 cf_2
  have b_cf_3 : cf_3 ≤ 1 := by rw [e_cf_3]; exact addc_carry_le_one rdx_1 0 cf_2 b_rdx_1 (by decide) b_cf_2
  clear e_rdx_2 e_cf_3
  -- hi: xor {hi}, {hi}
  extract_lets +onlyGivenNames hi cf_4 zf at hr
  have e_hi : hi = bitXor 0 0 := rfl
  have e_cf_4 : cf_4 = 0 := rfl
  have e_zf : zf = zeroFlag hi := rfl
  have b_hi : hi < 2^64 := by rw [e_hi]; exact bitXor_lt _ _
  have b_cf_4 : cf_4 ≤ 1 := by rw [e_cf_4]; decide
  have b_zf : zf ≤ 1 := by rw [e_zf]; exact zeroFlag_le_one _
  -- a1_2: add {a1}, {a4}
  extract_lets +onlyGivenNames s_4 a1_2 cf_5 at hr
  have e_a1_2 : a1_2 = (addc a1_1 a4_2 0).1 := rfl
  have e_cf_5 : cf_5 = (addc a1_1 a4_2 0).2 := rfl
  have l_a1_2 : a1_2 + 2^64 * cf_5 = a1_1 + a4_2 + 0 := by
    rw [e_a1_2, e_cf_5]; exact addc_lin a1_1 a4_2 0
  have b_a1_2 : a1_2 < 2^64 := by rw [e_a1_2]; exact addc_value_lt a1_1 a4_2 0
  have b_cf_5 : cf_5 ≤ 1 := by rw [e_cf_5]; exact addc_carry_le_one a1_1 a4_2 0 b_a1_1 b_a4_2 (by decide)
  clear e_a1_2 e_cf_5
  -- a2_1: adc {a2}, rdx
  extract_lets +onlyGivenNames s_5 a2_1 cf_6 at hr
  have e_a2_1 : a2_1 = (addc a2 rdx_2 cf_5).1 := rfl
  have e_cf_6 : cf_6 = (addc a2 rdx_2 cf_5).2 := rfl
  have l_a2_1 : a2_1 + 2^64 * cf_6 = a2 + rdx_2 + cf_5 := by
    rw [e_a2_1, e_cf_6]; exact addc_lin a2 rdx_2 cf_5
  have b_a2_1 : a2_1 < 2^64 := by rw [e_a2_1]; exact addc_value_lt a2 rdx_2 cf_5
  have b_cf_6 : cf_6 ≤ 1 := by rw [e_cf_6]; exact addc_carry_le_one a2 rdx_2 cf_5 b_a2 b_rdx_2 b_cf_5
  clear e_a2_1 e_cf_6
  -- hi_1: adc {hi}, 0
  extract_lets +onlyGivenNames s_6 hi_1 cf_7 at hr
  have e_hi_1 : hi_1 = (addc hi 0 cf_6).1 := rfl
  have e_cf_7 : cf_7 = (addc hi 0 cf_6).2 := rfl
  have l_hi_1 : hi_1 + 2^64 * cf_7 = hi + 0 + cf_6 := by
    rw [e_hi_1, e_cf_7]; exact addc_lin hi 0 cf_6
  have b_hi_1 : hi_1 < 2^64 := by rw [e_hi_1]; exact addc_value_lt hi 0 cf_6
  have b_cf_7 : cf_7 ≤ 1 := by rw [e_cf_7]; exact addc_carry_le_one hi 0 cf_6 b_hi (by decide) b_cf_6
  clear e_hi_1 e_cf_7
  -- a5: mov {a5}, {a1}
  extract_lets +onlyGivenNames a5 at hr
  have e_a5 : a5 = a1_2 := rfl
  have b_a5 : a5 < 2^64 := by rw [e_a5]; exact b_a1_2
  -- a1_3: imul {a1}, {inv}
  extract_lets +onlyGivenNames a1_3 at hr
  have e_a1_3 : a1_3 = a1_2 * inv' % 2^64 := rfl
  have b_a1_3 : a1_3 < 2^64 := by rw [e_a1_3]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- rdx_3: mul qword ptr [{p} + 24]
  extract_lets +onlyGivenNames rdx_3 at hr
  have e_rdx_3 : rdx_3 = rax_3 * modulus.l3 / 2^64 := rfl
  have p_rdx_3 : rax_3 * modulus.l3 < 2^64 * 2^64 := Nat.mul_lt_mul'' b_rax_3 hm.2.2.2
  have b_rdx_3 : rdx_3 < 2^64 := by rw [e_rdx_3]; exact Nat.div_lt_of_lt_mul p_rdx_3
  obtain ⟨lo_rdx_3, b_lo_rdx_3, d_rdx_3⟩ :
      ∃ lo, lo < 2^64 ∧ lo + 2^64 * rdx_3 = rax_3 * modulus.l3 :=
    ⟨rax_3 * modulus.l3 % 2^64, Nat.mod_lt _ (Nat.two_pow_pos _),
      by rw [e_rdx_3]; exact Nat.mod_add_div _ _⟩
  clear e_rdx_3
  -- rax_6: None
  extract_lets +onlyGivenNames rax_6 at hr
  have e_rax_6 : rax_6 = rax_3 * modulus.l3 % 2^64 := rfl
  have b_rax_6 : rax_6 < 2^64 := by rw [e_rax_6]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- a3_1: add {a3}, rax
  extract_lets +onlyGivenNames s_7 a3_1 cf_8 at hr
  have e_a3_1 : a3_1 = (addc a3 rax_6 0).1 := rfl
  have e_cf_8 : cf_8 = (addc a3 rax_6 0).2 := rfl
  have l_a3_1 : a3_1 + 2^64 * cf_8 = a3 + rax_6 + 0 := by
    rw [e_a3_1, e_cf_8]; exact addc_lin a3 rax_6 0
  have b_a3_1 : a3_1 < 2^64 := by rw [e_a3_1]; exact addc_value_lt a3 rax_6 0
  have b_cf_8 : cf_8 ≤ 1 := by rw [e_cf_8]; exact addc_carry_le_one a3 rax_6 0 b_a3 b_rax_6 (by decide)
  clear e_a3_1 e_cf_8
  -- rax_7: mov rax, {a1}
  extract_lets +onlyGivenNames rax_7 at hr
  have e_rax_7 : rax_7 = a1_3 := rfl
  have b_rax_7 : rax_7 < 2^64 := by rw [e_rax_7]; exact b_a1_3
  -- rdx_4: adc rdx, 0
  extract_lets +onlyGivenNames s_8 rdx_4 cf_9 at hr
  have e_rdx_4 : rdx_4 = (addc rdx_3 0 cf_8).1 := rfl
  have e_cf_9 : cf_9 = (addc rdx_3 0 cf_8).2 := rfl
  have l_rdx_4 : rdx_4 + 2^64 * cf_9 = rdx_3 + 0 + cf_8 := by
    rw [e_rdx_4, e_cf_9]; exact addc_lin rdx_3 0 cf_8
  have b_rdx_4 : rdx_4 < 2^64 := by rw [e_rdx_4]; exact addc_value_lt rdx_3 0 cf_8
  have b_cf_9 : cf_9 ≤ 1 := by rw [e_cf_9]; exact addc_carry_le_one rdx_3 0 cf_8 b_rdx_3 (by decide) b_cf_8
  clear e_rdx_4 e_cf_9
  -- a3_2: add {a3}, {hi}
  extract_lets +onlyGivenNames s_9 a3_2 cf_10 at hr
  have e_a3_2 : a3_2 = (addc a3_1 hi_1 0).1 := rfl
  have e_cf_10 : cf_10 = (addc a3_1 hi_1 0).2 := rfl
  have l_a3_2 : a3_2 + 2^64 * cf_10 = a3_1 + hi_1 + 0 := by
    rw [e_a3_2, e_cf_10]; exact addc_lin a3_1 hi_1 0
  have b_a3_2 : a3_2 < 2^64 := by rw [e_a3_2]; exact addc_value_lt a3_1 hi_1 0
  have b_cf_10 : cf_10 ≤ 1 := by rw [e_cf_10]; exact addc_carry_le_one a3_1 hi_1 0 b_a3_1 b_hi_1 (by decide)
  clear e_a3_2 e_cf_10
  -- rdx_5: adc rdx, 0
  extract_lets +onlyGivenNames s_10 rdx_5 cf_11 at hr
  have e_rdx_5 : rdx_5 = (addc rdx_4 0 cf_10).1 := rfl
  have e_cf_11 : cf_11 = (addc rdx_4 0 cf_10).2 := rfl
  have l_rdx_5 : rdx_5 + 2^64 * cf_11 = rdx_4 + 0 + cf_10 := by
    rw [e_rdx_5, e_cf_11]; exact addc_lin rdx_4 0 cf_10
  have b_rdx_5 : rdx_5 < 2^64 := by rw [e_rdx_5]; exact addc_value_lt rdx_4 0 cf_10
  have b_cf_11 : cf_11 ≤ 1 := by rw [e_cf_11]; exact addc_carry_le_one rdx_4 0 cf_10 b_rdx_4 (by decide) b_cf_10
  clear e_rdx_5 e_cf_11
  -- BEGIN redcMont round 0
  have hq_0 : rax_1 = mulLo inv' rax := by
    simp only [mulLo, e_rax_1, Nat.mul_comm]
  have hlo_0 : mulLo rax_1 modulus.l0 = rax_2 := by
    simp only [mulLo, e_rax_2]
  have hc_0 : rax + rax_2 = 2^64 * cf := by
    have h := neg_carry_cancel rax inv' modulus.l0 rax_1 b_rax b_inv' hm.1
      (by simpa only [e_inv'] using hinvP) hq_0
    rw [hlo_0] at h
    rw [e_a4] at l_a4_1
    omega
  have dp0_0 : rax_2 + 2^64 * rdx = rax_1 * modulus.l0 := by
    have hlo : lo_rdx = rax_2 := by
      rw [redcMont_split_low b_lo_rdx d_rdx, e_rax_2]
    simpa only [hlo] using d_rdx
  have dp1_0 : rax_4 + 2^64 * rdx_1 = rax_1 * modulus.l1 := by
    have hlo : lo_rdx_1 = rax_4 := by
      rw [redcMont_split_low b_lo_rdx_1 d_rdx_1, e_rax_4, e_rax_3, e_q]
    rw [e_rax_3, e_q] at d_rdx_1
    simpa only [hlo] using d_rdx_1
  have dp3_0 : rax_6 + 2^64 * rdx_3 = rax_1 * modulus.l3 := by
    have hlo : lo_rdx_3 = rax_6 := by
      rw [redcMont_split_low b_lo_rdx_3 d_rdx_3, e_rax_6, e_rax_3, e_q]
    rw [e_rax_3, e_q] at d_rdx_3
    simpa only [hlo] using d_rdx_3
  have top0_0 : rdx ≤ 2^64 - 2 :=
    redcMont_mul_high_le b_rax_1 hm.1 dp0_0
  have top1_0 : rdx_1 ≤ 2^64 - 2 :=
    redcMont_mul_high_le b_rax_1 hm.2.1 dp1_0
  have top3_0 : rdx_3 < 2^62 := by
    rw [hshape.2] at dp3_0
    clear * - dp3_0 b_rax_1
    omega
  have hi_zero : hi = 0 := by norm_num [e_hi, bitXor, word, regMod]
  have l_hi_1' : hi_1 + 2^64 * cf_7 = cf_6 := by simpa [hi_zero] using l_hi_1
  have l_a3_2' : a3_2 + 2^64 * cf_10 = a3_1 + hi_1 := by
    simpa [hi_zero] using l_a3_2
  have hz_0 : a4_1 = 0 ∧ cf_1 = 0 ∧ cf_3 = 0 ∧ cf_7 = 0 ∧ cf_9 = 0 ∧ cf_11 = 0 := by
    clear * - hc_0 l_a4_1 l_a4_2 l_rdx_2 l_hi_1' l_rdx_4 l_a3_2' l_rdx_5
      top0_0 top1_0 top3_0 b_cf b_cf_2 b_cf_6 b_cf_8 b_cf_10
    omega
  have I_0 : 2^64 * (a1_2 + 2^64 * a2_1 + 2^128 * a3_2 + 2^192 * rdx_5) =
      (rax + 2^64 * a1 + 2^128 * a2 + 2^192 * a3) +
        rax_1 * (modulus.l0 + 2^64 * modulus.l1 + 2^192 * modulus.l3) :=
    redcMont_step hc_0 dp0_0 dp1_0 dp3_0 l_a4_1 l_a4_2 l_a1_1 l_rdx_2
      l_a1_2 l_a2_1 l_hi_1' l_a3_1 l_rdx_4 l_a3_2' l_rdx_5 hz_0
  -- END redcMont round 0
  -- a4_3: mov {a4}, rdx
  extract_lets +onlyGivenNames a4_3 at hr
  have e_a4_3 : a4_3 = rdx_5 := rfl
  have b_a4_3 : a4_3 < 2^64 := by rw [e_a4_3]; exact b_rdx_5
  -- rdx_6: mul qword ptr [{p}]
  extract_lets +onlyGivenNames rdx_6 at hr
  have e_rdx_6 : rdx_6 = rax_7 * modulus.l0 / 2^64 := rfl
  have p_rdx_6 : rax_7 * modulus.l0 < 2^64 * 2^64 := Nat.mul_lt_mul'' b_rax_7 hm.1
  have b_rdx_6 : rdx_6 < 2^64 := by rw [e_rdx_6]; exact Nat.div_lt_of_lt_mul p_rdx_6
  obtain ⟨lo_rdx_6, b_lo_rdx_6, d_rdx_6⟩ :
      ∃ lo, lo < 2^64 ∧ lo + 2^64 * rdx_6 = rax_7 * modulus.l0 :=
    ⟨rax_7 * modulus.l0 % 2^64, Nat.mod_lt _ (Nat.two_pow_pos _),
      by rw [e_rdx_6]; exact Nat.mod_add_div _ _⟩
  clear e_rdx_6
  -- rax_8: None
  extract_lets +onlyGivenNames rax_8 at hr
  have e_rax_8 : rax_8 = rax_7 * modulus.l0 % 2^64 := rfl
  have b_rax_8 : rax_8 < 2^64 := by rw [e_rax_8]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- a5_1: add {a5}, rax
  extract_lets +onlyGivenNames s_11 a5_1 cf_12 at hr
  have e_a5_1 : a5_1 = (addc a5 rax_8 0).1 := rfl
  have e_cf_12 : cf_12 = (addc a5 rax_8 0).2 := rfl
  have l_a5_1 : a5_1 + 2^64 * cf_12 = a5 + rax_8 + 0 := by
    rw [e_a5_1, e_cf_12]; exact addc_lin a5 rax_8 0
  have b_a5_1 : a5_1 < 2^64 := by rw [e_a5_1]; exact addc_value_lt a5 rax_8 0
  have b_cf_12 : cf_12 ≤ 1 := by rw [e_cf_12]; exact addc_carry_le_one a5 rax_8 0 b_a5 b_rax_8 (by decide)
  clear e_a5_1 e_cf_12
  -- a5_2: adc {a5}, rdx
  extract_lets +onlyGivenNames s_12 a5_2 cf_13 at hr
  have e_a5_2 : a5_2 = (addc a5_1 rdx_6 cf_12).1 := rfl
  have e_cf_13 : cf_13 = (addc a5_1 rdx_6 cf_12).2 := rfl
  have l_a5_2 : a5_2 + 2^64 * cf_13 = a5_1 + rdx_6 + cf_12 := by
    rw [e_a5_2, e_cf_13]; exact addc_lin a5_1 rdx_6 cf_12
  have b_a5_2 : a5_2 < 2^64 := by rw [e_a5_2]; exact addc_value_lt a5_1 rdx_6 cf_12
  have b_cf_13 : cf_13 ≤ 1 := by rw [e_cf_13]; exact addc_carry_le_one a5_1 rdx_6 cf_12 b_a5_1 b_rdx_6 b_cf_12
  clear e_a5_2 e_cf_13
  -- rdx_7: mul qword ptr [{p} + 8]
  extract_lets +onlyGivenNames rdx_7 at hr
  have e_rdx_7 : rdx_7 = rax_7 * modulus.l1 / 2^64 := rfl
  have p_rdx_7 : rax_7 * modulus.l1 < 2^64 * 2^64 := Nat.mul_lt_mul'' b_rax_7 hm.2.1
  have b_rdx_7 : rdx_7 < 2^64 := by rw [e_rdx_7]; exact Nat.div_lt_of_lt_mul p_rdx_7
  obtain ⟨lo_rdx_7, b_lo_rdx_7, d_rdx_7⟩ :
      ∃ lo, lo < 2^64 ∧ lo + 2^64 * rdx_7 = rax_7 * modulus.l1 :=
    ⟨rax_7 * modulus.l1 % 2^64, Nat.mod_lt _ (Nat.two_pow_pos _),
      by rw [e_rdx_7]; exact Nat.mod_add_div _ _⟩
  clear e_rdx_7
  -- rax_10: None
  extract_lets +onlyGivenNames rax_10 at hr
  have e_rax_10 : rax_10 = rax_7 * modulus.l1 % 2^64 := rfl
  have b_rax_10 : rax_10 < 2^64 := by rw [e_rax_10]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- a2_2: add {a2}, rax
  extract_lets +onlyGivenNames s_13 a2_2 cf_14 at hr
  have e_a2_2 : a2_2 = (addc a2_1 rax_10 0).1 := rfl
  have e_cf_14 : cf_14 = (addc a2_1 rax_10 0).2 := rfl
  have l_a2_2 : a2_2 + 2^64 * cf_14 = a2_1 + rax_10 + 0 := by
    rw [e_a2_2, e_cf_14]; exact addc_lin a2_1 rax_10 0
  have b_a2_2 : a2_2 < 2^64 := by rw [e_a2_2]; exact addc_value_lt a2_1 rax_10 0
  have b_cf_14 : cf_14 ≤ 1 := by rw [e_cf_14]; exact addc_carry_le_one a2_1 rax_10 0 b_a2_1 b_rax_10 (by decide)
  clear e_a2_2 e_cf_14
  -- rdx_8: adc rdx, 0
  extract_lets +onlyGivenNames s_14 rdx_8 cf_15 at hr
  have e_rdx_8 : rdx_8 = (addc rdx_7 0 cf_14).1 := rfl
  have e_cf_15 : cf_15 = (addc rdx_7 0 cf_14).2 := rfl
  have l_rdx_8 : rdx_8 + 2^64 * cf_15 = rdx_7 + 0 + cf_14 := by
    rw [e_rdx_8, e_cf_15]; exact addc_lin rdx_7 0 cf_14
  have b_rdx_8 : rdx_8 < 2^64 := by rw [e_rdx_8]; exact addc_value_lt rdx_7 0 cf_14
  have b_cf_15 : cf_15 ≤ 1 := by rw [e_cf_15]; exact addc_carry_le_one rdx_7 0 cf_14 b_rdx_7 (by decide) b_cf_14
  clear e_rdx_8 e_cf_15
  -- a2_3: add {a2}, {a5}
  extract_lets +onlyGivenNames s_15 a2_3 cf_17 at hr
  have e_a2_3 : a2_3 = (addc a2_2 a5_2 0).1 := rfl
  have e_cf_17 : cf_17 = (addc a2_2 a5_2 0).2 := rfl
  have l_a2_3 : a2_3 + 2^64 * cf_17 = a2_2 + a5_2 + 0 := by
    rw [e_a2_3, e_cf_17]; exact addc_lin a2_2 a5_2 0
  have b_a2_3 : a2_3 < 2^64 := by rw [e_a2_3]; exact addc_value_lt a2_2 a5_2 0
  have b_cf_17 : cf_17 ≤ 1 := by rw [e_cf_17]; exact addc_carry_le_one a2_2 a5_2 0 b_a2_2 b_a5_2 (by decide)
  clear e_a2_3 e_cf_17
  -- a3_3: adc {a3}, rdx
  extract_lets +onlyGivenNames s_16 a3_3 cf_18 at hr
  have e_a3_3 : a3_3 = (addc a3_2 rdx_8 cf_17).1 := rfl
  have e_cf_18 : cf_18 = (addc a3_2 rdx_8 cf_17).2 := rfl
  have l_a3_3 : a3_3 + 2^64 * cf_18 = a3_2 + rdx_8 + cf_17 := by
    rw [e_a3_3, e_cf_18]; exact addc_lin a3_2 rdx_8 cf_17
  have b_a3_3 : a3_3 < 2^64 := by rw [e_a3_3]; exact addc_value_lt a3_2 rdx_8 cf_17
  have b_cf_18 : cf_18 ≤ 1 := by rw [e_cf_18]; exact addc_carry_le_one a3_2 rdx_8 cf_17 b_a3_2 b_rdx_8 b_cf_17
  clear e_a3_3 e_cf_18
  -- hi_3: adc {hi}, 0
  extract_lets +onlyGivenNames s_17 hi_3 cf_19 at hr
  have e_hi_3 : hi_3 = (addc hi 0 cf_18).1 := rfl
  have e_cf_19 : cf_19 = (addc hi 0 cf_18).2 := rfl
  have l_hi_3 : hi_3 + 2^64 * cf_19 = hi + 0 + cf_18 := by
    rw [e_hi_3, e_cf_19]; exact addc_lin hi 0 cf_18
  have b_hi_3 : hi_3 < 2^64 := by rw [e_hi_3]; exact addc_value_lt hi 0 cf_18
  have b_cf_19 : cf_19 ≤ 1 := by rw [e_cf_19]; exact addc_carry_le_one hi 0 cf_18 b_hi (by decide) b_cf_18
  clear e_hi_3 e_cf_19
  -- a6: mov {a6}, {a2}
  extract_lets +onlyGivenNames a6 at hr
  have e_a6 : a6 = a2_3 := rfl
  have b_a6 : a6 < 2^64 := by rw [e_a6]; exact b_a2_3
  -- a2_4: imul {a2}, {inv}
  extract_lets +onlyGivenNames a2_4 at hr
  have e_a2_4 : a2_4 = a2_3 * inv' % 2^64 := rfl
  have b_a2_4 : a2_4 < 2^64 := by rw [e_a2_4]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- rdx_9: mul qword ptr [{p} + 24]
  extract_lets +onlyGivenNames rdx_9 at hr
  have e_rdx_9 : rdx_9 = rax_7 * modulus.l3 / 2^64 := rfl
  have p_rdx_9 : rax_7 * modulus.l3 < 2^64 * 2^64 := Nat.mul_lt_mul'' b_rax_7 hm.2.2.2
  have b_rdx_9 : rdx_9 < 2^64 := by rw [e_rdx_9]; exact Nat.div_lt_of_lt_mul p_rdx_9
  obtain ⟨lo_rdx_9, b_lo_rdx_9, d_rdx_9⟩ :
      ∃ lo, lo < 2^64 ∧ lo + 2^64 * rdx_9 = rax_7 * modulus.l3 :=
    ⟨rax_7 * modulus.l3 % 2^64, Nat.mod_lt _ (Nat.two_pow_pos _),
      by rw [e_rdx_9]; exact Nat.mod_add_div _ _⟩
  clear e_rdx_9
  -- rax_12: None
  extract_lets +onlyGivenNames rax_12 at hr
  have e_rax_12 : rax_12 = rax_7 * modulus.l3 % 2^64 := rfl
  have b_rax_12 : rax_12 < 2^64 := by rw [e_rax_12]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- a4_4: add {a4}, rax
  extract_lets +onlyGivenNames s_18 a4_4 cf_20 at hr
  have e_a4_4 : a4_4 = (addc a4_3 rax_12 0).1 := rfl
  have e_cf_20 : cf_20 = (addc a4_3 rax_12 0).2 := rfl
  have l_a4_4 : a4_4 + 2^64 * cf_20 = a4_3 + rax_12 + 0 := by
    rw [e_a4_4, e_cf_20]; exact addc_lin a4_3 rax_12 0
  have b_a4_4 : a4_4 < 2^64 := by rw [e_a4_4]; exact addc_value_lt a4_3 rax_12 0
  have b_cf_20 : cf_20 ≤ 1 := by rw [e_cf_20]; exact addc_carry_le_one a4_3 rax_12 0 b_a4_3 b_rax_12 (by decide)
  clear e_a4_4 e_cf_20
  -- rax_13: mov rax, {a2}
  extract_lets +onlyGivenNames rax_13 at hr
  have e_rax_13 : rax_13 = a2_4 := rfl
  have b_rax_13 : rax_13 < 2^64 := by rw [e_rax_13]; exact b_a2_4
  -- rdx_10: adc rdx, 0
  extract_lets +onlyGivenNames s_19 rdx_10 cf_21 at hr
  have e_rdx_10 : rdx_10 = (addc rdx_9 0 cf_20).1 := rfl
  have e_cf_21 : cf_21 = (addc rdx_9 0 cf_20).2 := rfl
  have l_rdx_10 : rdx_10 + 2^64 * cf_21 = rdx_9 + 0 + cf_20 := by
    rw [e_rdx_10, e_cf_21]; exact addc_lin rdx_9 0 cf_20
  have b_rdx_10 : rdx_10 < 2^64 := by rw [e_rdx_10]; exact addc_value_lt rdx_9 0 cf_20
  have b_cf_21 : cf_21 ≤ 1 := by rw [e_cf_21]; exact addc_carry_le_one rdx_9 0 cf_20 b_rdx_9 (by decide) b_cf_20
  clear e_rdx_10 e_cf_21
  -- a4_5: add {a4}, {hi}
  extract_lets +onlyGivenNames s_20 a4_5 cf_22 at hr
  have e_a4_5 : a4_5 = (addc a4_4 hi_3 0).1 := rfl
  have e_cf_22 : cf_22 = (addc a4_4 hi_3 0).2 := rfl
  have l_a4_5 : a4_5 + 2^64 * cf_22 = a4_4 + hi_3 + 0 := by
    rw [e_a4_5, e_cf_22]; exact addc_lin a4_4 hi_3 0
  have b_a4_5 : a4_5 < 2^64 := by rw [e_a4_5]; exact addc_value_lt a4_4 hi_3 0
  have b_cf_22 : cf_22 ≤ 1 := by rw [e_cf_22]; exact addc_carry_le_one a4_4 hi_3 0 b_a4_4 b_hi_3 (by decide)
  clear e_a4_5 e_cf_22
  -- rdx_11: adc rdx, 0
  extract_lets +onlyGivenNames s_21 rdx_11 cf_23 at hr
  have e_rdx_11 : rdx_11 = (addc rdx_10 0 cf_22).1 := rfl
  have e_cf_23 : cf_23 = (addc rdx_10 0 cf_22).2 := rfl
  have l_rdx_11 : rdx_11 + 2^64 * cf_23 = rdx_10 + 0 + cf_22 := by
    rw [e_rdx_11, e_cf_23]; exact addc_lin rdx_10 0 cf_22
  have b_rdx_11 : rdx_11 < 2^64 := by rw [e_rdx_11]; exact addc_value_lt rdx_10 0 cf_22
  have b_cf_23 : cf_23 ≤ 1 := by rw [e_cf_23]; exact addc_carry_le_one rdx_10 0 cf_22 b_rdx_10 (by decide) b_cf_22
  clear e_rdx_11 e_cf_23
  -- a5_3: mov {a5}, rdx
  extract_lets +onlyGivenNames a5_3 at hr
  have e_a5_3 : a5_3 = rdx_11 := rfl
  have b_a5_3 : a5_3 < 2^64 := by rw [e_a5_3]; exact b_rdx_11
  -- rdx_12: mul qword ptr [{p}]
  extract_lets +onlyGivenNames rdx_12 at hr
  have e_rdx_12 : rdx_12 = rax_13 * modulus.l0 / 2^64 := rfl
  have p_rdx_12 : rax_13 * modulus.l0 < 2^64 * 2^64 := Nat.mul_lt_mul'' b_rax_13 hm.1
  have b_rdx_12 : rdx_12 < 2^64 := by rw [e_rdx_12]; exact Nat.div_lt_of_lt_mul p_rdx_12
  obtain ⟨lo_rdx_12, b_lo_rdx_12, d_rdx_12⟩ :
      ∃ lo, lo < 2^64 ∧ lo + 2^64 * rdx_12 = rax_13 * modulus.l0 :=
    ⟨rax_13 * modulus.l0 % 2^64, Nat.mod_lt _ (Nat.two_pow_pos _),
      by rw [e_rdx_12]; exact Nat.mod_add_div _ _⟩
  clear e_rdx_12
  -- rax_14: None
  extract_lets +onlyGivenNames rax_14 at hr
  have e_rax_14 : rax_14 = rax_13 * modulus.l0 % 2^64 := rfl
  have b_rax_14 : rax_14 < 2^64 := by rw [e_rax_14]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- a6_1: add {a6}, rax
  extract_lets +onlyGivenNames s_22 a6_1 cf_24 at hr
  have e_a6_1 : a6_1 = (addc a6 rax_14 0).1 := rfl
  have e_cf_24 : cf_24 = (addc a6 rax_14 0).2 := rfl
  have l_a6_1 : a6_1 + 2^64 * cf_24 = a6 + rax_14 + 0 := by
    rw [e_a6_1, e_cf_24]; exact addc_lin a6 rax_14 0
  have b_a6_1 : a6_1 < 2^64 := by rw [e_a6_1]; exact addc_value_lt a6 rax_14 0
  have b_cf_24 : cf_24 ≤ 1 := by rw [e_cf_24]; exact addc_carry_le_one a6 rax_14 0 b_a6 b_rax_14 (by decide)
  clear e_a6_1 e_cf_24
  -- a6_2: adc {a6}, rdx
  extract_lets +onlyGivenNames s_23 a6_2 cf_25 at hr
  have e_a6_2 : a6_2 = (addc a6_1 rdx_12 cf_24).1 := rfl
  have e_cf_25 : cf_25 = (addc a6_1 rdx_12 cf_24).2 := rfl
  have l_a6_2 : a6_2 + 2^64 * cf_25 = a6_1 + rdx_12 + cf_24 := by
    rw [e_a6_2, e_cf_25]; exact addc_lin a6_1 rdx_12 cf_24
  have b_a6_2 : a6_2 < 2^64 := by rw [e_a6_2]; exact addc_value_lt a6_1 rdx_12 cf_24
  have b_cf_25 : cf_25 ≤ 1 := by rw [e_cf_25]; exact addc_carry_le_one a6_1 rdx_12 cf_24 b_a6_1 b_rdx_12 b_cf_24
  clear e_a6_2 e_cf_25
  -- rdx_13: mul qword ptr [{p} + 8]
  extract_lets +onlyGivenNames rdx_13 at hr
  have e_rdx_13 : rdx_13 = rax_13 * modulus.l1 / 2^64 := rfl
  have p_rdx_13 : rax_13 * modulus.l1 < 2^64 * 2^64 := Nat.mul_lt_mul'' b_rax_13 hm.2.1
  have b_rdx_13 : rdx_13 < 2^64 := by rw [e_rdx_13]; exact Nat.div_lt_of_lt_mul p_rdx_13
  obtain ⟨lo_rdx_13, b_lo_rdx_13, d_rdx_13⟩ :
      ∃ lo, lo < 2^64 ∧ lo + 2^64 * rdx_13 = rax_13 * modulus.l1 :=
    ⟨rax_13 * modulus.l1 % 2^64, Nat.mod_lt _ (Nat.two_pow_pos _),
      by rw [e_rdx_13]; exact Nat.mod_add_div _ _⟩
  clear e_rdx_13
  -- rax_16: None
  extract_lets +onlyGivenNames rax_16 at hr
  have e_rax_16 : rax_16 = rax_13 * modulus.l1 % 2^64 := rfl
  have b_rax_16 : rax_16 < 2^64 := by rw [e_rax_16]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- a3_4: add {a3}, rax
  extract_lets +onlyGivenNames s_24 a3_4 cf_26 at hr
  have e_a3_4 : a3_4 = (addc a3_3 rax_16 0).1 := rfl
  have e_cf_26 : cf_26 = (addc a3_3 rax_16 0).2 := rfl
  have l_a3_4 : a3_4 + 2^64 * cf_26 = a3_3 + rax_16 + 0 := by
    rw [e_a3_4, e_cf_26]; exact addc_lin a3_3 rax_16 0
  have b_a3_4 : a3_4 < 2^64 := by rw [e_a3_4]; exact addc_value_lt a3_3 rax_16 0
  have b_cf_26 : cf_26 ≤ 1 := by rw [e_cf_26]; exact addc_carry_le_one a3_3 rax_16 0 b_a3_3 b_rax_16 (by decide)
  clear e_a3_4 e_cf_26
  -- rdx_14: adc rdx, 0
  extract_lets +onlyGivenNames s_25 rdx_14 cf_27 at hr
  have e_rdx_14 : rdx_14 = (addc rdx_13 0 cf_26).1 := rfl
  have e_cf_27 : cf_27 = (addc rdx_13 0 cf_26).2 := rfl
  have l_rdx_14 : rdx_14 + 2^64 * cf_27 = rdx_13 + 0 + cf_26 := by
    rw [e_rdx_14, e_cf_27]; exact addc_lin rdx_13 0 cf_26
  have b_rdx_14 : rdx_14 < 2^64 := by rw [e_rdx_14]; exact addc_value_lt rdx_13 0 cf_26
  have b_cf_27 : cf_27 ≤ 1 := by rw [e_cf_27]; exact addc_carry_le_one rdx_13 0 cf_26 b_rdx_13 (by decide) b_cf_26
  clear e_rdx_14 e_cf_27
  -- a3_5: add {a3}, {a6}
  extract_lets +onlyGivenNames s_26 a3_5 cf_29 at hr
  have e_a3_5 : a3_5 = (addc a3_4 a6_2 0).1 := rfl
  have e_cf_29 : cf_29 = (addc a3_4 a6_2 0).2 := rfl
  have l_a3_5 : a3_5 + 2^64 * cf_29 = a3_4 + a6_2 + 0 := by
    rw [e_a3_5, e_cf_29]; exact addc_lin a3_4 a6_2 0
  have b_a3_5 : a3_5 < 2^64 := by rw [e_a3_5]; exact addc_value_lt a3_4 a6_2 0
  have b_cf_29 : cf_29 ≤ 1 := by rw [e_cf_29]; exact addc_carry_le_one a3_4 a6_2 0 b_a3_4 b_a6_2 (by decide)
  clear e_a3_5 e_cf_29
  -- a4_6: adc {a4}, rdx
  extract_lets +onlyGivenNames s_27 a4_6 cf_30 at hr
  have e_a4_6 : a4_6 = (addc a4_5 rdx_14 cf_29).1 := rfl
  have e_cf_30 : cf_30 = (addc a4_5 rdx_14 cf_29).2 := rfl
  have l_a4_6 : a4_6 + 2^64 * cf_30 = a4_5 + rdx_14 + cf_29 := by
    rw [e_a4_6, e_cf_30]; exact addc_lin a4_5 rdx_14 cf_29
  have b_a4_6 : a4_6 < 2^64 := by rw [e_a4_6]; exact addc_value_lt a4_5 rdx_14 cf_29
  have b_cf_30 : cf_30 ≤ 1 := by rw [e_cf_30]; exact addc_carry_le_one a4_5 rdx_14 cf_29 b_a4_5 b_rdx_14 b_cf_29
  clear e_a4_6 e_cf_30
  -- hi_5: adc {hi}, 0
  extract_lets +onlyGivenNames s_28 hi_5 cf_31 at hr
  have e_hi_5 : hi_5 = (addc hi 0 cf_30).1 := rfl
  have e_cf_31 : cf_31 = (addc hi 0 cf_30).2 := rfl
  have l_hi_5 : hi_5 + 2^64 * cf_31 = hi + 0 + cf_30 := by
    rw [e_hi_5, e_cf_31]; exact addc_lin hi 0 cf_30
  have b_hi_5 : hi_5 < 2^64 := by rw [e_hi_5]; exact addc_value_lt hi 0 cf_30
  have b_cf_31 : cf_31 ≤ 1 := by rw [e_cf_31]; exact addc_carry_le_one hi 0 cf_30 b_hi (by decide) b_cf_30
  clear e_hi_5 e_cf_31
  -- q_1: mov {q}, {a3}
  extract_lets +onlyGivenNames q_1 at hr
  have e_q_1 : q_1 = a3_5 := rfl
  have b_q_1 : q_1 < 2^64 := by rw [e_q_1]; exact b_a3_5
  -- a3_6: imul {a3}, {inv}
  extract_lets +onlyGivenNames a3_6 at hr
  have e_a3_6 : a3_6 = a3_5 * inv' % 2^64 := rfl
  have b_a3_6 : a3_6 < 2^64 := by rw [e_a3_6]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- rdx_15: mul qword ptr [{p} + 24]
  extract_lets +onlyGivenNames rdx_15 at hr
  have e_rdx_15 : rdx_15 = rax_13 * modulus.l3 / 2^64 := rfl
  have p_rdx_15 : rax_13 * modulus.l3 < 2^64 * 2^64 := Nat.mul_lt_mul'' b_rax_13 hm.2.2.2
  have b_rdx_15 : rdx_15 < 2^64 := by rw [e_rdx_15]; exact Nat.div_lt_of_lt_mul p_rdx_15
  obtain ⟨lo_rdx_15, b_lo_rdx_15, d_rdx_15⟩ :
      ∃ lo, lo < 2^64 ∧ lo + 2^64 * rdx_15 = rax_13 * modulus.l3 :=
    ⟨rax_13 * modulus.l3 % 2^64, Nat.mod_lt _ (Nat.two_pow_pos _),
      by rw [e_rdx_15]; exact Nat.mod_add_div _ _⟩
  clear e_rdx_15
  -- rax_18: None
  extract_lets +onlyGivenNames rax_18 at hr
  have e_rax_18 : rax_18 = rax_13 * modulus.l3 % 2^64 := rfl
  have b_rax_18 : rax_18 < 2^64 := by rw [e_rax_18]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- a5_4: add {a5}, rax
  extract_lets +onlyGivenNames s_29 a5_4 cf_32 at hr
  have e_a5_4 : a5_4 = (addc a5_3 rax_18 0).1 := rfl
  have e_cf_32 : cf_32 = (addc a5_3 rax_18 0).2 := rfl
  have l_a5_4 : a5_4 + 2^64 * cf_32 = a5_3 + rax_18 + 0 := by
    rw [e_a5_4, e_cf_32]; exact addc_lin a5_3 rax_18 0
  have b_a5_4 : a5_4 < 2^64 := by rw [e_a5_4]; exact addc_value_lt a5_3 rax_18 0
  have b_cf_32 : cf_32 ≤ 1 := by rw [e_cf_32]; exact addc_carry_le_one a5_3 rax_18 0 b_a5_3 b_rax_18 (by decide)
  clear e_a5_4 e_cf_32
  -- rax_19: mov rax, {a3}
  extract_lets +onlyGivenNames rax_19 at hr
  have e_rax_19 : rax_19 = a3_6 := rfl
  have b_rax_19 : rax_19 < 2^64 := by rw [e_rax_19]; exact b_a3_6
  -- rdx_16: adc rdx, 0
  extract_lets +onlyGivenNames s_30 rdx_16 cf_33 at hr
  have e_rdx_16 : rdx_16 = (addc rdx_15 0 cf_32).1 := rfl
  have e_cf_33 : cf_33 = (addc rdx_15 0 cf_32).2 := rfl
  have l_rdx_16 : rdx_16 + 2^64 * cf_33 = rdx_15 + 0 + cf_32 := by
    rw [e_rdx_16, e_cf_33]; exact addc_lin rdx_15 0 cf_32
  have b_rdx_16 : rdx_16 < 2^64 := by rw [e_rdx_16]; exact addc_value_lt rdx_15 0 cf_32
  have b_cf_33 : cf_33 ≤ 1 := by rw [e_cf_33]; exact addc_carry_le_one rdx_15 0 cf_32 b_rdx_15 (by decide) b_cf_32
  clear e_rdx_16 e_cf_33
  -- a5_5: add {a5}, {hi}
  extract_lets +onlyGivenNames s_31 a5_5 cf_34 at hr
  have e_a5_5 : a5_5 = (addc a5_4 hi_5 0).1 := rfl
  have e_cf_34 : cf_34 = (addc a5_4 hi_5 0).2 := rfl
  have l_a5_5 : a5_5 + 2^64 * cf_34 = a5_4 + hi_5 + 0 := by
    rw [e_a5_5, e_cf_34]; exact addc_lin a5_4 hi_5 0
  have b_a5_5 : a5_5 < 2^64 := by rw [e_a5_5]; exact addc_value_lt a5_4 hi_5 0
  have b_cf_34 : cf_34 ≤ 1 := by rw [e_cf_34]; exact addc_carry_le_one a5_4 hi_5 0 b_a5_4 b_hi_5 (by decide)
  clear e_a5_5 e_cf_34
  -- rdx_17: adc rdx, 0
  extract_lets +onlyGivenNames s_32 rdx_17 cf_35 at hr
  have e_rdx_17 : rdx_17 = (addc rdx_16 0 cf_34).1 := rfl
  have e_cf_35 : cf_35 = (addc rdx_16 0 cf_34).2 := rfl
  have l_rdx_17 : rdx_17 + 2^64 * cf_35 = rdx_16 + 0 + cf_34 := by
    rw [e_rdx_17, e_cf_35]; exact addc_lin rdx_16 0 cf_34
  have b_rdx_17 : rdx_17 < 2^64 := by rw [e_rdx_17]; exact addc_value_lt rdx_16 0 cf_34
  have b_cf_35 : cf_35 ≤ 1 := by rw [e_cf_35]; exact addc_carry_le_one rdx_16 0 cf_34 b_rdx_16 (by decide) b_cf_34
  clear e_rdx_17 e_cf_35
  -- a6_3: mov {a6}, rdx
  extract_lets +onlyGivenNames a6_3 at hr
  have e_a6_3 : a6_3 = rdx_17 := rfl
  have b_a6_3 : a6_3 < 2^64 := by rw [e_a6_3]; exact b_rdx_17
  -- rdx_18: mul qword ptr [{p}]
  extract_lets +onlyGivenNames rdx_18 at hr
  have e_rdx_18 : rdx_18 = rax_19 * modulus.l0 / 2^64 := rfl
  have p_rdx_18 : rax_19 * modulus.l0 < 2^64 * 2^64 := Nat.mul_lt_mul'' b_rax_19 hm.1
  have b_rdx_18 : rdx_18 < 2^64 := by rw [e_rdx_18]; exact Nat.div_lt_of_lt_mul p_rdx_18
  obtain ⟨lo_rdx_18, b_lo_rdx_18, d_rdx_18⟩ :
      ∃ lo, lo < 2^64 ∧ lo + 2^64 * rdx_18 = rax_19 * modulus.l0 :=
    ⟨rax_19 * modulus.l0 % 2^64, Nat.mod_lt _ (Nat.two_pow_pos _),
      by rw [e_rdx_18]; exact Nat.mod_add_div _ _⟩
  clear e_rdx_18
  -- rax_20: None
  extract_lets +onlyGivenNames rax_20 at hr
  have e_rax_20 : rax_20 = rax_19 * modulus.l0 % 2^64 := rfl
  have b_rax_20 : rax_20 < 2^64 := by rw [e_rax_20]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- q_2: add {q}, rax
  extract_lets +onlyGivenNames s_33 q_2 cf_36 at hr
  have e_q_2 : q_2 = (addc q_1 rax_20 0).1 := rfl
  have e_cf_36 : cf_36 = (addc q_1 rax_20 0).2 := rfl
  have l_q_2 : q_2 + 2^64 * cf_36 = q_1 + rax_20 + 0 := by
    rw [e_q_2, e_cf_36]; exact addc_lin q_1 rax_20 0
  have b_q_2 : q_2 < 2^64 := by rw [e_q_2]; exact addc_value_lt q_1 rax_20 0
  have b_cf_36 : cf_36 ≤ 1 := by rw [e_cf_36]; exact addc_carry_le_one q_1 rax_20 0 b_q_1 b_rax_20 (by decide)
  clear e_q_2 e_cf_36
  -- q_3: adc {q}, rdx
  extract_lets +onlyGivenNames s_34 q_3 cf_37 at hr
  have e_q_3 : q_3 = (addc q_2 rdx_18 cf_36).1 := rfl
  have e_cf_37 : cf_37 = (addc q_2 rdx_18 cf_36).2 := rfl
  have l_q_3 : q_3 + 2^64 * cf_37 = q_2 + rdx_18 + cf_36 := by
    rw [e_q_3, e_cf_37]; exact addc_lin q_2 rdx_18 cf_36
  have b_q_3 : q_3 < 2^64 := by rw [e_q_3]; exact addc_value_lt q_2 rdx_18 cf_36
  have b_cf_37 : cf_37 ≤ 1 := by rw [e_cf_37]; exact addc_carry_le_one q_2 rdx_18 cf_36 b_q_2 b_rdx_18 b_cf_36
  clear e_q_3 e_cf_37
  -- rdx_19: mul qword ptr [{p} + 8]
  extract_lets +onlyGivenNames rdx_19 at hr
  have e_rdx_19 : rdx_19 = rax_19 * modulus.l1 / 2^64 := rfl
  have p_rdx_19 : rax_19 * modulus.l1 < 2^64 * 2^64 := Nat.mul_lt_mul'' b_rax_19 hm.2.1
  have b_rdx_19 : rdx_19 < 2^64 := by rw [e_rdx_19]; exact Nat.div_lt_of_lt_mul p_rdx_19
  obtain ⟨lo_rdx_19, b_lo_rdx_19, d_rdx_19⟩ :
      ∃ lo, lo < 2^64 ∧ lo + 2^64 * rdx_19 = rax_19 * modulus.l1 :=
    ⟨rax_19 * modulus.l1 % 2^64, Nat.mod_lt _ (Nat.two_pow_pos _),
      by rw [e_rdx_19]; exact Nat.mod_add_div _ _⟩
  clear e_rdx_19
  -- rax_22: None
  extract_lets +onlyGivenNames rax_22 at hr
  have e_rax_22 : rax_22 = rax_19 * modulus.l1 % 2^64 := rfl
  have b_rax_22 : rax_22 < 2^64 := by rw [e_rax_22]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- a4_7: add {a4}, rax
  extract_lets +onlyGivenNames s_35 a4_7 cf_38 at hr
  have e_a4_7 : a4_7 = (addc a4_6 rax_22 0).1 := rfl
  have e_cf_38 : cf_38 = (addc a4_6 rax_22 0).2 := rfl
  have l_a4_7 : a4_7 + 2^64 * cf_38 = a4_6 + rax_22 + 0 := by
    rw [e_a4_7, e_cf_38]; exact addc_lin a4_6 rax_22 0
  have b_a4_7 : a4_7 < 2^64 := by rw [e_a4_7]; exact addc_value_lt a4_6 rax_22 0
  have b_cf_38 : cf_38 ≤ 1 := by rw [e_cf_38]; exact addc_carry_le_one a4_6 rax_22 0 b_a4_6 b_rax_22 (by decide)
  clear e_a4_7 e_cf_38
  -- rdx_20: adc rdx, 0
  extract_lets +onlyGivenNames s_36 rdx_20 cf_39 at hr
  have e_rdx_20 : rdx_20 = (addc rdx_19 0 cf_38).1 := rfl
  have e_cf_39 : cf_39 = (addc rdx_19 0 cf_38).2 := rfl
  have l_rdx_20 : rdx_20 + 2^64 * cf_39 = rdx_19 + 0 + cf_38 := by
    rw [e_rdx_20, e_cf_39]; exact addc_lin rdx_19 0 cf_38
  have b_rdx_20 : rdx_20 < 2^64 := by rw [e_rdx_20]; exact addc_value_lt rdx_19 0 cf_38
  have b_cf_39 : cf_39 ≤ 1 := by rw [e_cf_39]; exact addc_carry_le_one rdx_19 0 cf_38 b_rdx_19 (by decide) b_cf_38
  clear e_rdx_20 e_cf_39
  -- a4_8: add {a4}, {q}
  extract_lets +onlyGivenNames s_37 a4_8 cf_41 at hr
  have e_a4_8 : a4_8 = (addc a4_7 q_3 0).1 := rfl
  have e_cf_41 : cf_41 = (addc a4_7 q_3 0).2 := rfl
  have l_a4_8 : a4_8 + 2^64 * cf_41 = a4_7 + q_3 + 0 := by
    rw [e_a4_8, e_cf_41]; exact addc_lin a4_7 q_3 0
  have b_a4_8 : a4_8 < 2^64 := by rw [e_a4_8]; exact addc_value_lt a4_7 q_3 0
  have b_cf_41 : cf_41 ≤ 1 := by rw [e_cf_41]; exact addc_carry_le_one a4_7 q_3 0 b_a4_7 b_q_3 (by decide)
  clear e_a4_8 e_cf_41
  -- a5_6: adc {a5}, rdx
  extract_lets +onlyGivenNames s_38 a5_6 cf_42 at hr
  have e_a5_6 : a5_6 = (addc a5_5 rdx_20 cf_41).1 := rfl
  have e_cf_42 : cf_42 = (addc a5_5 rdx_20 cf_41).2 := rfl
  have l_a5_6 : a5_6 + 2^64 * cf_42 = a5_5 + rdx_20 + cf_41 := by
    rw [e_a5_6, e_cf_42]; exact addc_lin a5_5 rdx_20 cf_41
  have b_a5_6 : a5_6 < 2^64 := by rw [e_a5_6]; exact addc_value_lt a5_5 rdx_20 cf_41
  have b_cf_42 : cf_42 ≤ 1 := by rw [e_cf_42]; exact addc_carry_le_one a5_5 rdx_20 cf_41 b_a5_5 b_rdx_20 b_cf_41
  clear e_a5_6 e_cf_42
  -- hi_7: adc {hi}, 0
  extract_lets +onlyGivenNames s_39 hi_7 cf_43 at hr
  have e_hi_7 : hi_7 = (addc hi 0 cf_42).1 := rfl
  have e_cf_43 : cf_43 = (addc hi 0 cf_42).2 := rfl
  have l_hi_7 : hi_7 + 2^64 * cf_43 = hi + 0 + cf_42 := by
    rw [e_hi_7, e_cf_43]; exact addc_lin hi 0 cf_42
  have b_hi_7 : hi_7 < 2^64 := by rw [e_hi_7]; exact addc_value_lt hi 0 cf_42
  have b_cf_43 : cf_43 ≤ 1 := by rw [e_cf_43]; exact addc_carry_le_one hi 0 cf_42 b_hi (by decide) b_cf_42
  clear e_hi_7 e_cf_43
  -- rdx_21: mul qword ptr [{p} + 24]
  extract_lets +onlyGivenNames rdx_21 at hr
  have e_rdx_21 : rdx_21 = rax_19 * modulus.l3 / 2^64 := rfl
  have p_rdx_21 : rax_19 * modulus.l3 < 2^64 * 2^64 := Nat.mul_lt_mul'' b_rax_19 hm.2.2.2
  have b_rdx_21 : rdx_21 < 2^64 := by rw [e_rdx_21]; exact Nat.div_lt_of_lt_mul p_rdx_21
  obtain ⟨lo_rdx_21, b_lo_rdx_21, d_rdx_21⟩ :
      ∃ lo, lo < 2^64 ∧ lo + 2^64 * rdx_21 = rax_19 * modulus.l3 :=
    ⟨rax_19 * modulus.l3 % 2^64, Nat.mod_lt _ (Nat.two_pow_pos _),
      by rw [e_rdx_21]; exact Nat.mod_add_div _ _⟩
  clear e_rdx_21
  -- rax_24: None
  extract_lets +onlyGivenNames rax_24 at hr
  have e_rax_24 : rax_24 = rax_19 * modulus.l3 % 2^64 := rfl
  have b_rax_24 : rax_24 < 2^64 := by rw [e_rax_24]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- a6_4: add {a6}, rax
  extract_lets +onlyGivenNames s_40 a6_4 cf_44 at hr
  have e_a6_4 : a6_4 = (addc a6_3 rax_24 0).1 := rfl
  have e_cf_44 : cf_44 = (addc a6_3 rax_24 0).2 := rfl
  have l_a6_4 : a6_4 + 2^64 * cf_44 = a6_3 + rax_24 + 0 := by
    rw [e_a6_4, e_cf_44]; exact addc_lin a6_3 rax_24 0
  have b_a6_4 : a6_4 < 2^64 := by rw [e_a6_4]; exact addc_value_lt a6_3 rax_24 0
  have b_cf_44 : cf_44 ≤ 1 := by rw [e_cf_44]; exact addc_carry_le_one a6_3 rax_24 0 b_a6_3 b_rax_24 (by decide)
  clear e_a6_4 e_cf_44
  -- rax_25: mov rax, {a4}
  extract_lets +onlyGivenNames rax_25 at hr
  have e_rax_25 : rax_25 = a4_8 := rfl
  have b_rax_25 : rax_25 < 2^64 := by rw [e_rax_25]; exact b_a4_8
  -- rdx_22: adc rdx, 0
  extract_lets +onlyGivenNames s_41 rdx_22 cf_45 at hr
  have e_rdx_22 : rdx_22 = (addc rdx_21 0 cf_44).1 := rfl
  have e_cf_45 : cf_45 = (addc rdx_21 0 cf_44).2 := rfl
  have l_rdx_22 : rdx_22 + 2^64 * cf_45 = rdx_21 + 0 + cf_44 := by
    rw [e_rdx_22, e_cf_45]; exact addc_lin rdx_21 0 cf_44
  have b_rdx_22 : rdx_22 < 2^64 := by rw [e_rdx_22]; exact addc_value_lt rdx_21 0 cf_44
  have b_cf_45 : cf_45 ≤ 1 := by rw [e_cf_45]; exact addc_carry_le_one rdx_21 0 cf_44 b_rdx_21 (by decide) b_cf_44
  clear e_rdx_22 e_cf_45
  -- a6_5: add {a6}, {hi}
  extract_lets +onlyGivenNames s_42 a6_5 cf_46 at hr
  have e_a6_5 : a6_5 = (addc a6_4 hi_7 0).1 := rfl
  have e_cf_46 : cf_46 = (addc a6_4 hi_7 0).2 := rfl
  have l_a6_5 : a6_5 + 2^64 * cf_46 = a6_4 + hi_7 + 0 := by
    rw [e_a6_5, e_cf_46]; exact addc_lin a6_4 hi_7 0
  have b_a6_5 : a6_5 < 2^64 := by rw [e_a6_5]; exact addc_value_lt a6_4 hi_7 0
  have b_cf_46 : cf_46 ≤ 1 := by rw [e_cf_46]; exact addc_carry_le_one a6_4 hi_7 0 b_a6_4 b_hi_7 (by decide)
  clear e_a6_5 e_cf_46
  -- rdx_23: adc rdx, 0
  extract_lets +onlyGivenNames s_43 rdx_23 cf_47 at hr
  have e_rdx_23 : rdx_23 = (addc rdx_22 0 cf_46).1 := rfl
  have e_cf_47 : cf_47 = (addc rdx_22 0 cf_46).2 := rfl
  have l_rdx_23 : rdx_23 + 2^64 * cf_47 = rdx_22 + 0 + cf_46 := by
    rw [e_rdx_23, e_cf_47]; exact addc_lin rdx_22 0 cf_46
  have b_rdx_23 : rdx_23 < 2^64 := by rw [e_rdx_23]; exact addc_value_lt rdx_22 0 cf_46
  have b_cf_47 : cf_47 ≤ 1 := by rw [e_cf_47]; exact addc_carry_le_one rdx_22 0 cf_46 b_rdx_22 (by decide) b_cf_46
  clear e_rdx_23 e_cf_47
  -- q_4: mov {q}, rdx
  extract_lets +onlyGivenNames q_4 at hr
  have e_q_4 : q_4 = rdx_23 := rfl
  have b_q_4 : q_4 < 2^64 := by rw [e_q_4]; exact b_rdx_23
  -- a4_9: add {a4}, qword ptr [{value} + 32]
  extract_lets +onlyGivenNames s_44 a4_9 cf_48 at hr
  have e_a4_9 : a4_9 = (addc a4_8 product.l4 0).1 := rfl
  have e_cf_48 : cf_48 = (addc a4_8 product.l4 0).2 := rfl
  have l_a4_9 : a4_9 + 2^64 * cf_48 = a4_8 + product.l4 + 0 := by
    rw [e_a4_9, e_cf_48]; exact addc_lin a4_8 product.l4 0
  have b_a4_9 : a4_9 < 2^64 := by rw [e_a4_9]; exact addc_value_lt a4_8 product.l4 0
  have b_cf_48 : cf_48 ≤ 1 := by rw [e_cf_48]; exact addc_carry_le_one a4_8 product.l4 0 b_a4_8 hproduct.2.2.2.2.1 (by decide)
  clear e_a4_9 e_cf_48
  -- a5_7: adc {a5}, qword ptr [{value} + 40]
  extract_lets +onlyGivenNames s_45 a5_7 cf_49 at hr
  have e_a5_7 : a5_7 = (addc a5_6 product.l5 cf_48).1 := rfl
  have e_cf_49 : cf_49 = (addc a5_6 product.l5 cf_48).2 := rfl
  have l_a5_7 : a5_7 + 2^64 * cf_49 = a5_6 + product.l5 + cf_48 := by
    rw [e_a5_7, e_cf_49]; exact addc_lin a5_6 product.l5 cf_48
  have b_a5_7 : a5_7 < 2^64 := by rw [e_a5_7]; exact addc_value_lt a5_6 product.l5 cf_48
  have b_cf_49 : cf_49 ≤ 1 := by rw [e_cf_49]; exact addc_carry_le_one a5_6 product.l5 cf_48 b_a5_6 hproduct.2.2.2.2.2.1 b_cf_48
  clear e_a5_7 e_cf_49
  -- rax_26: mov rax, {a4}
  extract_lets +onlyGivenNames rax_26 at hr
  have e_rax_26 : rax_26 = a4_9 := rfl
  have b_rax_26 : rax_26 < 2^64 := by rw [e_rax_26]; exact b_a4_9
  -- a6_6: adc {a6}, qword ptr [{value} + 48]
  extract_lets +onlyGivenNames s_46 a6_6 cf_50 at hr
  have e_a6_6 : a6_6 = (addc a6_5 product.l6 cf_49).1 := rfl
  have e_cf_50 : cf_50 = (addc a6_5 product.l6 cf_49).2 := rfl
  have l_a6_6 : a6_6 + 2^64 * cf_50 = a6_5 + product.l6 + cf_49 := by
    rw [e_a6_6, e_cf_50]; exact addc_lin a6_5 product.l6 cf_49
  have b_a6_6 : a6_6 < 2^64 := by rw [e_a6_6]; exact addc_value_lt a6_5 product.l6 cf_49
  have b_cf_50 : cf_50 ≤ 1 := by rw [e_cf_50]; exact addc_carry_le_one a6_5 product.l6 cf_49 b_a6_5 hproduct.2.2.2.2.2.2.1 b_cf_49
  clear e_a6_6 e_cf_50
  -- a1_4: mov {a1}, {a5}
  extract_lets +onlyGivenNames a1_4 at hr
  have e_a1_4 : a1_4 = a5_7 := rfl
  have b_a1_4 : a1_4 < 2^64 := by rw [e_a1_4]; exact b_a5_7
  -- q_5: adc {q}, qword ptr [{value} + 56]
  extract_lets +onlyGivenNames s_47 q_5 cf_51 at hr
  have e_q_5 : q_5 = (addc q_4 product.l7 cf_50).1 := rfl
  have e_cf_51 : cf_51 = (addc q_4 product.l7 cf_50).2 := rfl
  have l_q_5 : q_5 + 2^64 * cf_51 = q_4 + product.l7 + cf_50 := by
    rw [e_q_5, e_cf_51]; exact addc_lin q_4 product.l7 cf_50
  have b_q_5 : q_5 < 2^64 := by rw [e_q_5]; exact addc_value_lt q_4 product.l7 cf_50
  have b_cf_51 : cf_51 ≤ 1 := by rw [e_cf_51]; exact addc_carry_le_one q_4 product.l7 cf_50 b_q_4 hproduct.2.2.2.2.2.2.2 b_cf_50
  clear e_q_5 e_cf_51
  -- value: sbb {value}, {value}
  extract_lets +onlyGivenNames s_48 value cf_52 at hr
  have e_value : value = (sbb 0 0 cf_51).1 := rfl
  have e_cf_52 : cf_52 = (sbb 0 0 cf_51).2 := rfl
  have l_value : value + 0 + cf_51 = 0 + 2^64 * cf_52 := by
    rw [e_value, e_cf_52]; exact sbb_lin 0 0 cf_51 (by decide) (by decide) b_cf_51
  have b_value : value < 2^64 := by rw [e_value]; exact sbb_value_lt 0 0 cf_51
  have b_cf_52 : cf_52 ≤ 1 := by rw [e_cf_52]; exact sbb_borrow_le_one 0 0 cf_51
  clear e_value e_cf_52
  -- a2_5: mov {a2}, {a6}
  extract_lets +onlyGivenNames a2_5 at hr
  have e_a2_5 : a2_5 = a6_6 := rfl
  have b_a2_5 : a2_5 < 2^64 := by rw [e_a2_5]; exact b_a6_6
  -- a4_10: sub {a4}, qword ptr [{p}]
  extract_lets +onlyGivenNames s_49 a4_10 cf_53 at hr
  have e_a4_10 : a4_10 = (sbb a4_9 modulus.l0 0).1 := rfl
  have e_cf_53 : cf_53 = (sbb a4_9 modulus.l0 0).2 := rfl
  have l_a4_10 : a4_10 + modulus.l0 + 0 = a4_9 + 2^64 * cf_53 := by
    rw [e_a4_10, e_cf_53]; exact sbb_lin a4_9 modulus.l0 0 b_a4_9 hm.1 (by decide)
  have b_a4_10 : a4_10 < 2^64 := by rw [e_a4_10]; exact sbb_value_lt a4_9 modulus.l0 0
  have b_cf_53 : cf_53 ≤ 1 := by rw [e_cf_53]; exact sbb_borrow_le_one a4_9 modulus.l0 0
  clear e_a4_10 e_cf_53
  -- a5_8: sbb {a5}, qword ptr [{p} + 8]
  extract_lets +onlyGivenNames s_50 a5_8 cf_54 at hr
  have e_a5_8 : a5_8 = (sbb a5_7 modulus.l1 cf_53).1 := rfl
  have e_cf_54 : cf_54 = (sbb a5_7 modulus.l1 cf_53).2 := rfl
  have l_a5_8 : a5_8 + modulus.l1 + cf_53 = a5_7 + 2^64 * cf_54 := by
    rw [e_a5_8, e_cf_54]; exact sbb_lin a5_7 modulus.l1 cf_53 b_a5_7 hm.2.1 b_cf_53
  have b_a5_8 : a5_8 < 2^64 := by rw [e_a5_8]; exact sbb_value_lt a5_7 modulus.l1 cf_53
  have b_cf_54 : cf_54 ≤ 1 := by rw [e_cf_54]; exact sbb_borrow_le_one a5_7 modulus.l1 cf_53
  clear e_a5_8 e_cf_54
  -- a6_7: sbb {a6}, qword ptr [{p} + 16]
  extract_lets +onlyGivenNames s_51 a6_7 cf_55 at hr
  have e_a6_7 : a6_7 = (sbb a6_6 modulus.l2 cf_54).1 := rfl
  have e_cf_55 : cf_55 = (sbb a6_6 modulus.l2 cf_54).2 := rfl
  have l_a6_7 : a6_7 + modulus.l2 + cf_54 = a6_6 + 2^64 * cf_55 := by
    rw [e_a6_7, e_cf_55]; exact sbb_lin a6_6 modulus.l2 cf_54 b_a6_6 hm.2.2.1 b_cf_54
  have b_a6_7 : a6_7 < 2^64 := by rw [e_a6_7]; exact sbb_value_lt a6_6 modulus.l2 cf_54
  have b_cf_55 : cf_55 ≤ 1 := by rw [e_cf_55]; exact sbb_borrow_le_one a6_6 modulus.l2 cf_54
  clear e_a6_7 e_cf_55
  -- a3_7: mov {a3}, {q}
  extract_lets +onlyGivenNames a3_7 at hr
  have e_a3_7 : a3_7 = q_5 := rfl
  have b_a3_7 : a3_7 < 2^64 := by rw [e_a3_7]; exact b_q_5
  -- q_6: sbb {q}, qword ptr [{p} + 24]
  extract_lets +onlyGivenNames s_52 q_6 cf_56 at hr
  have e_q_6 : q_6 = (sbb q_5 modulus.l3 cf_55).1 := rfl
  have e_cf_56 : cf_56 = (sbb q_5 modulus.l3 cf_55).2 := rfl
  have l_q_6 : q_6 + modulus.l3 + cf_55 = q_5 + 2^64 * cf_56 := by
    rw [e_q_6, e_cf_56]; exact sbb_lin q_5 modulus.l3 cf_55 b_q_5 hm.2.2.2 b_cf_55
  have b_q_6 : q_6 < 2^64 := by rw [e_q_6]; exact sbb_value_lt q_5 modulus.l3 cf_55
  have b_cf_56 : cf_56 ≤ 1 := by rw [e_cf_56]; exact sbb_borrow_le_one q_5 modulus.l3 cf_55
  clear e_q_6 e_cf_56
  -- value_1: sbb {value}, 0
  extract_lets +onlyGivenNames s_53 value_1 cf_57 at hr
  have e_value_1 : value_1 = (sbb value 0 cf_56).1 := rfl
  have e_cf_57 : cf_57 = (sbb value 0 cf_56).2 := rfl
  have l_value_1 : value_1 + 0 + cf_56 = value + 2^64 * cf_57 := by
    rw [e_value_1, e_cf_57]; exact sbb_lin value 0 cf_56 b_value (by decide) b_cf_56
  have b_value_1 : value_1 < 2^64 := by rw [e_value_1]; exact sbb_value_lt value 0 cf_56
  have b_cf_57 : cf_57 ≤ 1 := by rw [e_cf_57]; exact sbb_borrow_le_one value 0 cf_56
  clear e_value_1 e_cf_57
  -- rax_27: cmovnc rax, {a4}
  extract_lets +onlyGivenNames rax_27 at hr
  have e_rax_27 : rax_27 = (if cf_57 = 0 then a4_10 else rax_26) := rfl
  have b_rax_27 : rax_27 < 2^64 := by
    rw [e_rax_27]; split <;> first | exact b_a4_10 | exact b_rax_26
  -- a1_5: cmovnc {a1}, {a5}
  extract_lets +onlyGivenNames a1_5 at hr
  have e_a1_5 : a1_5 = (if cf_57 = 0 then a5_8 else a1_4) := rfl
  have b_a1_5 : a1_5 < 2^64 := by
    rw [e_a1_5]; split <;> first | exact b_a5_8 | exact b_a1_4
  -- a2_6: cmovnc {a2}, {a6}
  extract_lets +onlyGivenNames a2_6 at hr
  have e_a2_6 : a2_6 = (if cf_57 = 0 then a6_7 else a2_5) := rfl
  have b_a2_6 : a2_6 < 2^64 := by
    rw [e_a2_6]; split <;> first | exact b_a6_7 | exact b_a2_5
  -- a3_8: cmovnc {a3}, {q}
  extract_lets +onlyGivenNames a3_8 at hr
  have e_a3_8 : a3_8 = (if cf_57 = 0 then q_6 else a3_7) := rfl
  have b_a3_8 : a3_8 < 2^64 := by
    rw [e_a3_8]; split <;> first | exact b_q_6 | exact b_a3_7
  subst hr
  -- BEGIN redcMont staged conclusion
  sorry
  -- END redcMont staged conclusion

-- BEGIN redcMont public statement
/-- Full-width REDC returns a bounded lazy residue representing the eight-limb input scaled by
`R⁻¹` modulo the Pasta-shaped modulus.  The result is not claimed canonical. -/
theorem redcMont_spec (product : WideLimbs) (modulus : Limbs) (inv : Nat)
    (hproduct : product.Bounded) (hm : modulus.Bounded)
    (hshape : modulus.l2 = 0 ∧ modulus.l3 = 2^62)
    (hinv_lt : inv < 2^64) (hinv : (inv * modulus.l0 + 1) % 2^64 = 0) :
    let out := redcMont product modulus inv
    out.Bounded ∧ R * out.toNat ≡ product.toNat [MOD modulus.toNat] := by
  dsimp only
  change (redcMont product modulus inv).Bounded ∧
    2^256 * (redcMont product modulus inv).toNat ≡ product.toNat [MOD modulus.toNat]
  exact redcMont_spec_traced product modulus inv hproduct hm hshape hinv_lt hinv _ rfl
-- END redcMont public statement

end PastaAsm.X86_64
