/-
Copyright Supranational LLC (the routines, transcribed from Semolina v0.1.4).
Copyright (c) 2026 the pasta-asm contributors (the transcription and the proofs).
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.Spec
import PastaAsm.InversionNormalization
import PastaAsm.AArch64.Transcription
import Mathlib.Tactic.NormNum

/-!
# Correctness of the transcribed full-width Montgomery reduction block

See the parent module's documentation for details.
-/

namespace PastaAsm.AArch64

-- BEGIN redcMont_spec lemmas
/-- One uncorrected cancellation round, stated over the linear facts emitted by the generated
skeleton. The explicit limit rules out both discarded carries. -/
private theorem redcMont_step
    {a0 a1 a2 a3 q p p0 p1 lo t0 t1lo t1hi n1 c1 n2 c2 n3 c3 t3lo t3hi
      r4 k4 o0 c4 o1 c5 o2 c6 o3 k3 cs : Nat}
    (hc : a0 + lo = 2^64 * cs)
    (d0 : lo + 2^64 * t0 = p0 * q)
    (d1 : t1lo + 2^64 * t1hi = p1 * q)
    (l1 : n1 + 2^64 * c1 = a1 + t1lo + cs)
    (l2 : n2 + 2^64 * c2 = a2 + 0 + c1)
    (l3 : n3 + 2^64 * c3 = a3 + t3lo + c2)
    (sh : t3lo + 2^64 * t3hi = q * 2^62)
    (l4 : r4 + 2^64 * k4 = 0 + 0 + c3)
    (lo0 : o0 + 2^64 * c4 = n1 + t0 + 0)
    (lo1 : o1 + 2^64 * c5 = n2 + t1hi + c4)
    (lo2 : o2 + 2^64 * c6 = n3 + 0 + c5)
    (lo3 : o3 + 2^64 * k3 = r4 + t3hi + c6)
    (hqp : q * p = p0 * q + 2^64 * (p1 * q) + 2^254 * q)
    (hlimit : (a0 + 2^64 * a1 + 2^128 * a2 + 2^192 * a3) + q * p < 2^320) :
    k4 = 0 ∧ k3 = 0 ∧
      2^64 * (o0 + 2^64 * o1 + 2^128 * o2 + 2^192 * o3) =
        (a0 + 2^64 * a1 + 2^128 * a2 + 2^192 * a3) + q * p := by
  omega

/-- Four one-word cancellation equations compose to the full `2^256` cancellation. -/
private theorem redcMont_compose4 {lo p q0 q1 q2 q3 y1 y2 y3 y4 : Nat}
    (h0 : 2^64 * y1 = lo + q0 * p)
    (h1 : 2^64 * y2 = y1 + q1 * p)
    (h2 : 2^64 * y3 = y2 + q2 * p)
    (h3 : 2^64 * y4 = y3 + q3 * p) :
    2^256 * y4 = lo + q0 * p + 2^64 * (q1 * p) +
      2^128 * (q2 * p) + 2^192 * (q3 * p) := by
  omega

/-- The uncorrected low-half reduction is at most the modulus. -/
private theorem redcMont_reduced_le {lo p m y : Nat}
    (hp : 0 < p) (hlo : lo < 2^256) (hm : m < 2^256)
    (hc : y * 2^256 = lo + m * p) : y ≤ p := by
  have hmp : m * p < 2^256 * p := Nat.mul_lt_mul_of_pos_right hm hp
  have hsum : lo + m * p < 2^256 + 2^256 * p := Nat.add_lt_add hlo hmp
  have hy : y * 2^256 < (p + 1) * 2^256 := by
    rw [hc]
    calc
      lo + m * p < 2^256 + 2^256 * p := hsum
      _ = (p + 1) * 2^256 := by ring
  have hy' : y < p + 1 := (Nat.mul_lt_mul_right (Nat.two_pow_pos 256)).mp hy
  omega

/-- The five-limb subtraction and select implements the shared carry-aware correction. -/
private theorem redcMont_tail {R p candidate low top diff borrow final out : Nat}
    (hcandlt : candidate < R + p)
    (hcand : candidate = low + R * top) (htop : top ≤ 1)
    (hdiff : diff + p + R * borrow = low + R)
    (hborrow : borrow ≤ 1) (hdiffBound : diff < R)
    (hfinal : (final = 1 ∧ 1 ≤ top + borrow) ∨
      (final = 0 ∧ top + borrow < 1))
    (hout : out = if final = 0 then low else diff) :
    out = PastaAsm.REDC.carryCorrect candidate p := by
  unfold PastaAsm.REDC.carryCorrect
  obtain rfl | htop : top = 0 ∨ top = 1 := by omega
  · obtain rfl | hborrow : borrow = 0 ∨ borrow = 1 := by omega
    · simp only [Nat.mul_zero, add_zero] at hcand hdiff hfinal
      have hfinal : final = 0 := by omega
      rw [if_pos hfinal] at hout
      have hlt : candidate < p := by omega
      rw [if_pos hlt]
      omega
    · subst hborrow
      simp only [Nat.mul_zero, Nat.mul_one, add_zero, zero_add] at hcand hdiff hfinal
      have hfinal : final = 1 := by omega
      rw [if_neg (by omega)] at hout
      have hge : p ≤ candidate := by omega
      rw [if_neg (by omega)]
      omega
  · subst htop
    obtain rfl | hborrow : borrow = 0 ∨ borrow = 1 := by omega
    · simp only [Nat.mul_zero, Nat.mul_one, add_zero] at hcand hdiff hfinal
      have hfinal : final = 1 := by omega
      rw [if_neg (by omega)] at hout
      have hge : p ≤ candidate := by omega
      rw [if_neg (by omega)]
      omega
    · subst hborrow
      simp only [Nat.mul_one] at hcand hdiff
      omega
-- END redcMont_spec lemmas

-- BEGIN redcMont_spec statement
/-- Full-width Montgomery reduction by the inline block. The result is a bounded four-limb lazy
residue; it is intentionally not claimed to be canonical. -/
theorem redcMont_spec (low high modulus : Limbs) (inv : Nat)
    (hlow : low.Bounded) (hhigh : high.Bounded) (hm : modulus.Bounded)
    (hshape : modulus.l2 = 0 ∧ modulus.l3 = 2^62)
    (hinv_lt : inv < 2^64) (hinv : (inv * modulus.l0 + 1) % 2^64 = 0) :
    ∀ out, out = redcMont low high modulus inv →
      out.Bounded ∧
        2^256 * out.toNat ≡ low.toNat + 2^256 * high.toNat [MOD modulus.toNat] := by
  intro out hr
  have hinv_spec := hinv
  have hinv : inv < 2^64 := hinv_lt
-- END redcMont_spec statement
  -- generated skeleton for `redcMont`: do not edit between the annotations
  unfold redcMont at hr
  lift_lets at hr
  -- r0: argument
  extract_lets +onlyGivenNames r0 at hr
  have e_r0 : r0 = low.l0 := rfl
  clear_value r0
  have b_r0 : r0 < 2^64 := by rw [e_r0]; exact hlow.1
  -- r1: argument
  extract_lets +onlyGivenNames r1 at hr
  have e_r1 : r1 = low.l1 := rfl
  clear_value r1
  have b_r1 : r1 < 2^64 := by rw [e_r1]; exact hlow.2.1
  -- r2: argument
  extract_lets +onlyGivenNames r2 at hr
  have e_r2 : r2 = low.l2 := rfl
  clear_value r2
  have b_r2 : r2 < 2^64 := by rw [e_r2]; exact hlow.2.2.1
  -- r3: argument
  extract_lets +onlyGivenNames r3 at hr
  have e_r3 : r3 = low.l3 := rfl
  clear_value r3
  have b_r3 : r3 < 2^64 := by rw [e_r3]; exact hlow.2.2.2
  -- h0: argument
  extract_lets +onlyGivenNames h0 at hr
  have e_h0 : h0 = high.l0 := rfl
  clear_value h0
  have b_h0 : h0 < 2^64 := by rw [e_h0]; exact hhigh.1
  -- h1: argument
  extract_lets +onlyGivenNames h1 at hr
  have e_h1 : h1 = high.l1 := rfl
  clear_value h1
  have b_h1 : h1 < 2^64 := by rw [e_h1]; exact hhigh.2.1
  -- h2: argument
  extract_lets +onlyGivenNames h2 at hr
  have e_h2 : h2 = high.l2 := rfl
  clear_value h2
  have b_h2 : h2 < 2^64 := by rw [e_h2]; exact hhigh.2.2.1
  -- h3: argument
  extract_lets +onlyGivenNames h3 at hr
  have e_h3 : h3 = high.l3 := rfl
  clear_value h3
  have b_h3 : h3 < 2^64 := by rw [e_h3]; exact hhigh.2.2.2
  -- p0: argument
  extract_lets +onlyGivenNames p0 at hr
  have e_p0 : p0 = modulus.l0 := rfl
  clear_value p0
  have b_p0 : p0 < 2^64 := by rw [e_p0]; exact hm.1
  -- p1: argument
  extract_lets +onlyGivenNames p1 at hr
  have e_p1 : p1 = modulus.l1 := rfl
  clear_value p1
  have b_p1 : p1 < 2^64 := by rw [e_p1]; exact hm.2.1
  -- p2: argument
  extract_lets +onlyGivenNames p2 at hr
  have e_p2 : p2 = modulus.l2 := rfl
  clear_value p2
  have b_p2 : p2 < 2^64 := by rw [e_p2]; exact hm.2.2.1
  -- p3: argument
  extract_lets +onlyGivenNames p3 at hr
  have e_p3 : p3 = modulus.l3 := rfl
  clear_value p3
  have b_p3 : p3 < 2^64 := by rw [e_p3]; exact hm.2.2.2
  -- inv': argument
  extract_lets +onlyGivenNames inv' at hr
  have e_inv' : inv' = inv := rfl
  clear_value inv'
  have b_inv' : inv' < 2^64 := by rw [e_inv']; exact hinv
  -- q: mul q,inv,r0
  extract_lets +onlyGivenNames q at hr
  have e_q : q = inv' * r0 % 2^64 := rfl
  clear_value q
  have b_q : q < 2^64 := by rw [e_q]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- t1: mul t1,p1,q
  extract_lets +onlyGivenNames t1 at hr
  have e_t1 : t1 = p1 * q % 2^64 := rfl
  clear_value t1
  have b_t1 : t1 < 2^64 := by rw [e_t1]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- t3: lsl t3,q,#62
  extract_lets +onlyGivenNames t3 at hr
  have e_t3 : t3 = q * 2^62 % 2^64 := rfl
  clear_value t3
  have b_t3 : t3 < 2^64 := by rw [e_t3]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- c: subs xzr,r0,#1
  extract_lets +onlyGivenNames c at hr
  have e_c : c = (r0 + 2^64 - 1 - (1 - 1)) / 2^64 := rfl
  clear_value c
  have b_c : c ≤ 1 := by rw [e_c]; exact subc_carry_le_one r0 1 1 b_r0
  have l_c : (c = 1 ∧ 1 + 1 ≤ r0 + 1) ∨ (c = 0 ∧ r0 + 1 < 1 + 1) :=
    subc_carry_cases r0 1 1 _ e_c b_r0 (by decide) (by decide)
  clear e_c
  -- t0: umulh t0,p0,q
  extract_lets +onlyGivenNames t0 at hr
  have e_t0 : t0 = p0 * q / 2^64 := rfl
  clear_value t0
  have p_t0 : p0 * q < 2^64 * 2^64 := Nat.mul_lt_mul'' b_p0 b_q
  have b_t0 : t0 < 2^64 := by rw [e_t0]; exact Nat.div_lt_of_lt_mul p_t0
  obtain ⟨lo_t0, b_lo_t0, d_t0⟩ :
      ∃ lo, lo < 2^64 ∧ lo + 2^64 * t0 = p0 * q :=
    ⟨p0 * q % 2^64, Nat.mod_lt _ (Nat.two_pow_pos _),
      by rw [e_t0]; exact Nat.mod_add_div _ _⟩
  clear e_t0
  -- r1_1: adcs r1,r1,t1
  extract_lets +onlyGivenNames s r1_1 c_1 at hr
  have e_r1_1 : r1_1 = (r1 + t1 + c) % 2^64 := rfl
  have e_c_1 : c_1 = (r1 + t1 + c) / 2^64 := rfl
  clear_value s r1_1 c_1
  have l_r1_1 : r1_1 + 2^64 * c_1 = r1 + t1 + c := by
    rw [e_r1_1, e_c_1]; exact Nat.mod_add_div _ _
  have b_r1_1 : r1_1 < 2^64 := by rw [e_r1_1]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_1 : c_1 ≤ 1 := by
    rw [e_c_1]; exact addc_carry_le_one r1 t1 c b_r1 b_t1 b_c
  clear e_r1_1 e_c_1
  -- t1_1: umulh t1,p1,q
  extract_lets +onlyGivenNames t1_1 at hr
  have e_t1_1 : t1_1 = p1 * q / 2^64 := rfl
  clear_value t1_1
  have p_t1_1 : p1 * q < 2^64 * 2^64 := Nat.mul_lt_mul'' b_p1 b_q
  have b_t1_1 : t1_1 < 2^64 := by rw [e_t1_1]; exact Nat.div_lt_of_lt_mul p_t1_1
  have d_t1_1 : t1 + 2^64 * t1_1 = p1 * q := by
    rw [e_t1, e_t1_1]; exact Nat.mod_add_div _ _
  clear e_t1 e_t1_1
  -- r2_1: adcs r2,r2,xzr
  extract_lets +onlyGivenNames s_1 r2_1 c_2 at hr
  have e_r2_1 : r2_1 = (r2 + 0 + c_1) % 2^64 := rfl
  have e_c_2 : c_2 = (r2 + 0 + c_1) / 2^64 := rfl
  clear_value s_1 r2_1 c_2
  have l_r2_1 : r2_1 + 2^64 * c_2 = r2 + 0 + c_1 := by
    rw [e_r2_1, e_c_2]; exact Nat.mod_add_div _ _
  have b_r2_1 : r2_1 < 2^64 := by rw [e_r2_1]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_2 : c_2 ≤ 1 := by
    rw [e_c_2]; exact addc_carry_le_one r2 0 c_1 b_r2 (by decide) b_c_1
  clear e_r2_1 e_c_2
  -- r3_1: adcs r3,r3,t3
  extract_lets +onlyGivenNames s_2 r3_1 c_3 at hr
  have e_r3_1 : r3_1 = (r3 + t3 + c_2) % 2^64 := rfl
  have e_c_3 : c_3 = (r3 + t3 + c_2) / 2^64 := rfl
  clear_value s_2 r3_1 c_3
  have l_r3_1 : r3_1 + 2^64 * c_3 = r3 + t3 + c_2 := by
    rw [e_r3_1, e_c_3]; exact Nat.mod_add_div _ _
  have b_r3_1 : r3_1 < 2^64 := by rw [e_r3_1]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_3 : c_3 ≤ 1 := by
    rw [e_c_3]; exact addc_carry_le_one r3 t3 c_2 b_r3 b_t3 b_c_2
  clear e_r3_1 e_c_3
  -- t3_1: lsr t3,q,#2
  extract_lets +onlyGivenNames t3_1 at hr
  have e_t3_1 : t3_1 = q / 2^2 := rfl
  clear_value t3_1
  have b_t3_1 : t3_1 < 2^62 := by
    rw [e_t3_1]; exact Nat.div_lt_of_lt_mul (lt_of_lt_of_eq b_q (by norm_num))
  have sh_t3_1 : t3 + 2^64 * t3_1 = q * 2^62 := by
    rw [e_t3, e_t3_1]; exact lsl62_lsr2_split _
  clear e_t3 e_t3_1
  -- r4: adc r4,xzr,xzr
  extract_lets +onlyGivenNames r4 at hr
  have e_r4 : r4 = (0 + 0 + c_3) % 2^64 := rfl
  clear_value r4
  have b_r4 : r4 < 2^64 := by rw [e_r4]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨k_r4, b_k_r4, l_r4⟩ :
      ∃ k, k ≤ 1 ∧ r4 + 2^64 * k = 0 + 0 + c_3 :=
    ⟨(0 + 0 + c_3) / 2^64, addc_carry_le_one 0 0 c_3 (by decide) (by decide) b_c_3,
      by rw [e_r4]; exact Nat.mod_add_div _ _⟩
  clear e_r4
  -- r0_1: adds r0,r1,t0
  extract_lets +onlyGivenNames s_3 r0_1 c_4 at hr
  have e_r0_1 : r0_1 = (r1_1 + t0 + 0) % 2^64 := rfl
  have e_c_4 : c_4 = (r1_1 + t0 + 0) / 2^64 := rfl
  clear_value s_3 r0_1 c_4
  have l_r0_1 : r0_1 + 2^64 * c_4 = r1_1 + t0 + 0 := by
    rw [e_r0_1, e_c_4]; exact Nat.mod_add_div _ _
  have b_r0_1 : r0_1 < 2^64 := by rw [e_r0_1]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_4 : c_4 ≤ 1 := by
    rw [e_c_4]; exact addc_carry_le_one r1_1 t0 0 b_r1_1 b_t0 (by decide)
  clear e_r0_1 e_c_4
  -- r1_2: adcs r1,r2,t1
  extract_lets +onlyGivenNames s_4 r1_2 c_5 at hr
  have e_r1_2 : r1_2 = (r2_1 + t1_1 + c_4) % 2^64 := rfl
  have e_c_5 : c_5 = (r2_1 + t1_1 + c_4) / 2^64 := rfl
  clear_value s_4 r1_2 c_5
  have l_r1_2 : r1_2 + 2^64 * c_5 = r2_1 + t1_1 + c_4 := by
    rw [e_r1_2, e_c_5]; exact Nat.mod_add_div _ _
  have b_r1_2 : r1_2 < 2^64 := by rw [e_r1_2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_5 : c_5 ≤ 1 := by
    rw [e_c_5]; exact addc_carry_le_one r2_1 t1_1 c_4 b_r2_1 b_t1_1 b_c_4
  clear e_r1_2 e_c_5
  -- r2_2: adcs r2,r3,xzr
  extract_lets +onlyGivenNames s_5 r2_2 c_6 at hr
  have e_r2_2 : r2_2 = (r3_1 + 0 + c_5) % 2^64 := rfl
  have e_c_6 : c_6 = (r3_1 + 0 + c_5) / 2^64 := rfl
  clear_value s_5 r2_2 c_6
  have l_r2_2 : r2_2 + 2^64 * c_6 = r3_1 + 0 + c_5 := by
    rw [e_r2_2, e_c_6]; exact Nat.mod_add_div _ _
  have b_r2_2 : r2_2 < 2^64 := by rw [e_r2_2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_6 : c_6 ≤ 1 := by
    rw [e_c_6]; exact addc_carry_le_one r3_1 0 c_5 b_r3_1 (by decide) b_c_5
  clear e_r2_2 e_c_6
  -- q_1: mul q,inv,r0
  extract_lets +onlyGivenNames q_1 at hr
  have e_q_1 : q_1 = inv' * r0_1 % 2^64 := rfl
  clear_value q_1
  have b_q_1 : q_1 < 2^64 := by rw [e_q_1]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- r3_2: adc r3,r4,t3
  extract_lets +onlyGivenNames r3_2 at hr
  have e_r3_2 : r3_2 = (r4 + t3_1 + c_6) % 2^64 := rfl
  clear_value r3_2
  have b_r3_2 : r3_2 < 2^64 := by rw [e_r3_2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨k_r3_2, b_k_r3_2, l_r3_2⟩ :
      ∃ k, k ≤ 1 ∧ r3_2 + 2^64 * k = r4 + t3_1 + c_6 :=
    ⟨(r4 + t3_1 + c_6) / 2^64, addc_carry_le_one r4 t3_1 c_6 b_r4 (lt_of_lt_of_le b_t3_1 (by norm_num)) b_c_6,
      by rw [e_r3_2]; exact Nat.mod_add_div _ _⟩
  clear e_r3_2
  -- t1_2: mul t1,p1,q
  extract_lets +onlyGivenNames t1_2 at hr
  have e_t1_2 : t1_2 = p1 * q_1 % 2^64 := rfl
  clear_value t1_2
  have b_t1_2 : t1_2 < 2^64 := by rw [e_t1_2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- t3_2: lsl t3,q,#62
  extract_lets +onlyGivenNames t3_2 at hr
  have e_t3_2 : t3_2 = q_1 * 2^62 % 2^64 := rfl
  clear_value t3_2
  have b_t3_2 : t3_2 < 2^64 := by rw [e_t3_2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- c_7: subs xzr,r0,#1
  extract_lets +onlyGivenNames c_7 at hr
  have e_c_7 : c_7 = (r0_1 + 2^64 - 1 - (1 - 1)) / 2^64 := rfl
  clear_value c_7
  have b_c_7 : c_7 ≤ 1 := by rw [e_c_7]; exact subc_carry_le_one r0_1 1 1 b_r0_1
  have l_c_7 : (c_7 = 1 ∧ 1 + 1 ≤ r0_1 + 1) ∨ (c_7 = 0 ∧ r0_1 + 1 < 1 + 1) :=
    subc_carry_cases r0_1 1 1 _ e_c_7 b_r0_1 (by decide) (by decide)
  clear e_c_7
  -- t0_1: umulh t0,p0,q
  extract_lets +onlyGivenNames t0_1 at hr
  have e_t0_1 : t0_1 = p0 * q_1 / 2^64 := rfl
  clear_value t0_1
  have p_t0_1 : p0 * q_1 < 2^64 * 2^64 := Nat.mul_lt_mul'' b_p0 b_q_1
  have b_t0_1 : t0_1 < 2^64 := by rw [e_t0_1]; exact Nat.div_lt_of_lt_mul p_t0_1
  obtain ⟨lo_t0_1, b_lo_t0_1, d_t0_1⟩ :
      ∃ lo, lo < 2^64 ∧ lo + 2^64 * t0_1 = p0 * q_1 :=
    ⟨p0 * q_1 % 2^64, Nat.mod_lt _ (Nat.two_pow_pos _),
      by rw [e_t0_1]; exact Nat.mod_add_div _ _⟩
  clear e_t0_1
  -- r1_3: adcs r1,r1,t1
  extract_lets +onlyGivenNames s_6 r1_3 c_8 at hr
  have e_r1_3 : r1_3 = (r1_2 + t1_2 + c_7) % 2^64 := rfl
  have e_c_8 : c_8 = (r1_2 + t1_2 + c_7) / 2^64 := rfl
  clear_value s_6 r1_3 c_8
  have l_r1_3 : r1_3 + 2^64 * c_8 = r1_2 + t1_2 + c_7 := by
    rw [e_r1_3, e_c_8]; exact Nat.mod_add_div _ _
  have b_r1_3 : r1_3 < 2^64 := by rw [e_r1_3]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_8 : c_8 ≤ 1 := by
    rw [e_c_8]; exact addc_carry_le_one r1_2 t1_2 c_7 b_r1_2 b_t1_2 b_c_7
  clear e_r1_3 e_c_8
  -- t1_3: umulh t1,p1,q
  extract_lets +onlyGivenNames t1_3 at hr
  have e_t1_3 : t1_3 = p1 * q_1 / 2^64 := rfl
  clear_value t1_3
  have p_t1_3 : p1 * q_1 < 2^64 * 2^64 := Nat.mul_lt_mul'' b_p1 b_q_1
  have b_t1_3 : t1_3 < 2^64 := by rw [e_t1_3]; exact Nat.div_lt_of_lt_mul p_t1_3
  have d_t1_3 : t1_2 + 2^64 * t1_3 = p1 * q_1 := by
    rw [e_t1_2, e_t1_3]; exact Nat.mod_add_div _ _
  clear e_t1_2 e_t1_3
  -- r2_3: adcs r2,r2,xzr
  extract_lets +onlyGivenNames s_7 r2_3 c_9 at hr
  have e_r2_3 : r2_3 = (r2_2 + 0 + c_8) % 2^64 := rfl
  have e_c_9 : c_9 = (r2_2 + 0 + c_8) / 2^64 := rfl
  clear_value s_7 r2_3 c_9
  have l_r2_3 : r2_3 + 2^64 * c_9 = r2_2 + 0 + c_8 := by
    rw [e_r2_3, e_c_9]; exact Nat.mod_add_div _ _
  have b_r2_3 : r2_3 < 2^64 := by rw [e_r2_3]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_9 : c_9 ≤ 1 := by
    rw [e_c_9]; exact addc_carry_le_one r2_2 0 c_8 b_r2_2 (by decide) b_c_8
  clear e_r2_3 e_c_9
  -- r3_3: adcs r3,r3,t3
  extract_lets +onlyGivenNames s_8 r3_3 c_10 at hr
  have e_r3_3 : r3_3 = (r3_2 + t3_2 + c_9) % 2^64 := rfl
  have e_c_10 : c_10 = (r3_2 + t3_2 + c_9) / 2^64 := rfl
  clear_value s_8 r3_3 c_10
  have l_r3_3 : r3_3 + 2^64 * c_10 = r3_2 + t3_2 + c_9 := by
    rw [e_r3_3, e_c_10]; exact Nat.mod_add_div _ _
  have b_r3_3 : r3_3 < 2^64 := by rw [e_r3_3]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_10 : c_10 ≤ 1 := by
    rw [e_c_10]; exact addc_carry_le_one r3_2 t3_2 c_9 b_r3_2 b_t3_2 b_c_9
  clear e_r3_3 e_c_10
  -- t3_3: lsr t3,q,#2
  extract_lets +onlyGivenNames t3_3 at hr
  have e_t3_3 : t3_3 = q_1 / 2^2 := rfl
  clear_value t3_3
  have b_t3_3 : t3_3 < 2^62 := by
    rw [e_t3_3]; exact Nat.div_lt_of_lt_mul (lt_of_lt_of_eq b_q_1 (by norm_num))
  have sh_t3_3 : t3_2 + 2^64 * t3_3 = q_1 * 2^62 := by
    rw [e_t3_2, e_t3_3]; exact lsl62_lsr2_split _
  clear e_t3_2 e_t3_3
  -- r4_1: adc r4,xzr,xzr
  extract_lets +onlyGivenNames r4_1 at hr
  have e_r4_1 : r4_1 = (0 + 0 + c_10) % 2^64 := rfl
  clear_value r4_1
  have b_r4_1 : r4_1 < 2^64 := by rw [e_r4_1]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨k_r4_1, b_k_r4_1, l_r4_1⟩ :
      ∃ k, k ≤ 1 ∧ r4_1 + 2^64 * k = 0 + 0 + c_10 :=
    ⟨(0 + 0 + c_10) / 2^64, addc_carry_le_one 0 0 c_10 (by decide) (by decide) b_c_10,
      by rw [e_r4_1]; exact Nat.mod_add_div _ _⟩
  clear e_r4_1
  -- r0_2: adds r0,r1,t0
  extract_lets +onlyGivenNames s_9 r0_2 c_11 at hr
  have e_r0_2 : r0_2 = (r1_3 + t0_1 + 0) % 2^64 := rfl
  have e_c_11 : c_11 = (r1_3 + t0_1 + 0) / 2^64 := rfl
  clear_value s_9 r0_2 c_11
  have l_r0_2 : r0_2 + 2^64 * c_11 = r1_3 + t0_1 + 0 := by
    rw [e_r0_2, e_c_11]; exact Nat.mod_add_div _ _
  have b_r0_2 : r0_2 < 2^64 := by rw [e_r0_2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_11 : c_11 ≤ 1 := by
    rw [e_c_11]; exact addc_carry_le_one r1_3 t0_1 0 b_r1_3 b_t0_1 (by decide)
  clear e_r0_2 e_c_11
  -- r1_4: adcs r1,r2,t1
  extract_lets +onlyGivenNames s_10 r1_4 c_12 at hr
  have e_r1_4 : r1_4 = (r2_3 + t1_3 + c_11) % 2^64 := rfl
  have e_c_12 : c_12 = (r2_3 + t1_3 + c_11) / 2^64 := rfl
  clear_value s_10 r1_4 c_12
  have l_r1_4 : r1_4 + 2^64 * c_12 = r2_3 + t1_3 + c_11 := by
    rw [e_r1_4, e_c_12]; exact Nat.mod_add_div _ _
  have b_r1_4 : r1_4 < 2^64 := by rw [e_r1_4]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_12 : c_12 ≤ 1 := by
    rw [e_c_12]; exact addc_carry_le_one r2_3 t1_3 c_11 b_r2_3 b_t1_3 b_c_11
  clear e_r1_4 e_c_12
  -- r2_4: adcs r2,r3,xzr
  extract_lets +onlyGivenNames s_11 r2_4 c_13 at hr
  have e_r2_4 : r2_4 = (r3_3 + 0 + c_12) % 2^64 := rfl
  have e_c_13 : c_13 = (r3_3 + 0 + c_12) / 2^64 := rfl
  clear_value s_11 r2_4 c_13
  have l_r2_4 : r2_4 + 2^64 * c_13 = r3_3 + 0 + c_12 := by
    rw [e_r2_4, e_c_13]; exact Nat.mod_add_div _ _
  have b_r2_4 : r2_4 < 2^64 := by rw [e_r2_4]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_13 : c_13 ≤ 1 := by
    rw [e_c_13]; exact addc_carry_le_one r3_3 0 c_12 b_r3_3 (by decide) b_c_12
  clear e_r2_4 e_c_13
  -- q_2: mul q,inv,r0
  extract_lets +onlyGivenNames q_2 at hr
  have e_q_2 : q_2 = inv' * r0_2 % 2^64 := rfl
  clear_value q_2
  have b_q_2 : q_2 < 2^64 := by rw [e_q_2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- r3_4: adc r3,r4,t3
  extract_lets +onlyGivenNames r3_4 at hr
  have e_r3_4 : r3_4 = (r4_1 + t3_3 + c_13) % 2^64 := rfl
  clear_value r3_4
  have b_r3_4 : r3_4 < 2^64 := by rw [e_r3_4]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨k_r3_4, b_k_r3_4, l_r3_4⟩ :
      ∃ k, k ≤ 1 ∧ r3_4 + 2^64 * k = r4_1 + t3_3 + c_13 :=
    ⟨(r4_1 + t3_3 + c_13) / 2^64, addc_carry_le_one r4_1 t3_3 c_13 b_r4_1 (lt_of_lt_of_le b_t3_3 (by norm_num)) b_c_13,
      by rw [e_r3_4]; exact Nat.mod_add_div _ _⟩
  clear e_r3_4
  -- t1_4: mul t1,p1,q
  extract_lets +onlyGivenNames t1_4 at hr
  have e_t1_4 : t1_4 = p1 * q_2 % 2^64 := rfl
  clear_value t1_4
  have b_t1_4 : t1_4 < 2^64 := by rw [e_t1_4]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- t3_4: lsl t3,q,#62
  extract_lets +onlyGivenNames t3_4 at hr
  have e_t3_4 : t3_4 = q_2 * 2^62 % 2^64 := rfl
  clear_value t3_4
  have b_t3_4 : t3_4 < 2^64 := by rw [e_t3_4]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- c_14: subs xzr,r0,#1
  extract_lets +onlyGivenNames c_14 at hr
  have e_c_14 : c_14 = (r0_2 + 2^64 - 1 - (1 - 1)) / 2^64 := rfl
  clear_value c_14
  have b_c_14 : c_14 ≤ 1 := by rw [e_c_14]; exact subc_carry_le_one r0_2 1 1 b_r0_2
  have l_c_14 : (c_14 = 1 ∧ 1 + 1 ≤ r0_2 + 1) ∨ (c_14 = 0 ∧ r0_2 + 1 < 1 + 1) :=
    subc_carry_cases r0_2 1 1 _ e_c_14 b_r0_2 (by decide) (by decide)
  clear e_c_14
  -- t0_2: umulh t0,p0,q
  extract_lets +onlyGivenNames t0_2 at hr
  have e_t0_2 : t0_2 = p0 * q_2 / 2^64 := rfl
  clear_value t0_2
  have p_t0_2 : p0 * q_2 < 2^64 * 2^64 := Nat.mul_lt_mul'' b_p0 b_q_2
  have b_t0_2 : t0_2 < 2^64 := by rw [e_t0_2]; exact Nat.div_lt_of_lt_mul p_t0_2
  obtain ⟨lo_t0_2, b_lo_t0_2, d_t0_2⟩ :
      ∃ lo, lo < 2^64 ∧ lo + 2^64 * t0_2 = p0 * q_2 :=
    ⟨p0 * q_2 % 2^64, Nat.mod_lt _ (Nat.two_pow_pos _),
      by rw [e_t0_2]; exact Nat.mod_add_div _ _⟩
  clear e_t0_2
  -- r1_5: adcs r1,r1,t1
  extract_lets +onlyGivenNames s_12 r1_5 c_15 at hr
  have e_r1_5 : r1_5 = (r1_4 + t1_4 + c_14) % 2^64 := rfl
  have e_c_15 : c_15 = (r1_4 + t1_4 + c_14) / 2^64 := rfl
  clear_value s_12 r1_5 c_15
  have l_r1_5 : r1_5 + 2^64 * c_15 = r1_4 + t1_4 + c_14 := by
    rw [e_r1_5, e_c_15]; exact Nat.mod_add_div _ _
  have b_r1_5 : r1_5 < 2^64 := by rw [e_r1_5]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_15 : c_15 ≤ 1 := by
    rw [e_c_15]; exact addc_carry_le_one r1_4 t1_4 c_14 b_r1_4 b_t1_4 b_c_14
  clear e_r1_5 e_c_15
  -- t1_5: umulh t1,p1,q
  extract_lets +onlyGivenNames t1_5 at hr
  have e_t1_5 : t1_5 = p1 * q_2 / 2^64 := rfl
  clear_value t1_5
  have p_t1_5 : p1 * q_2 < 2^64 * 2^64 := Nat.mul_lt_mul'' b_p1 b_q_2
  have b_t1_5 : t1_5 < 2^64 := by rw [e_t1_5]; exact Nat.div_lt_of_lt_mul p_t1_5
  have d_t1_5 : t1_4 + 2^64 * t1_5 = p1 * q_2 := by
    rw [e_t1_4, e_t1_5]; exact Nat.mod_add_div _ _
  clear e_t1_4 e_t1_5
  -- r2_5: adcs r2,r2,xzr
  extract_lets +onlyGivenNames s_13 r2_5 c_16 at hr
  have e_r2_5 : r2_5 = (r2_4 + 0 + c_15) % 2^64 := rfl
  have e_c_16 : c_16 = (r2_4 + 0 + c_15) / 2^64 := rfl
  clear_value s_13 r2_5 c_16
  have l_r2_5 : r2_5 + 2^64 * c_16 = r2_4 + 0 + c_15 := by
    rw [e_r2_5, e_c_16]; exact Nat.mod_add_div _ _
  have b_r2_5 : r2_5 < 2^64 := by rw [e_r2_5]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_16 : c_16 ≤ 1 := by
    rw [e_c_16]; exact addc_carry_le_one r2_4 0 c_15 b_r2_4 (by decide) b_c_15
  clear e_r2_5 e_c_16
  -- r3_5: adcs r3,r3,t3
  extract_lets +onlyGivenNames s_14 r3_5 c_17 at hr
  have e_r3_5 : r3_5 = (r3_4 + t3_4 + c_16) % 2^64 := rfl
  have e_c_17 : c_17 = (r3_4 + t3_4 + c_16) / 2^64 := rfl
  clear_value s_14 r3_5 c_17
  have l_r3_5 : r3_5 + 2^64 * c_17 = r3_4 + t3_4 + c_16 := by
    rw [e_r3_5, e_c_17]; exact Nat.mod_add_div _ _
  have b_r3_5 : r3_5 < 2^64 := by rw [e_r3_5]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_17 : c_17 ≤ 1 := by
    rw [e_c_17]; exact addc_carry_le_one r3_4 t3_4 c_16 b_r3_4 b_t3_4 b_c_16
  clear e_r3_5 e_c_17
  -- t3_5: lsr t3,q,#2
  extract_lets +onlyGivenNames t3_5 at hr
  have e_t3_5 : t3_5 = q_2 / 2^2 := rfl
  clear_value t3_5
  have b_t3_5 : t3_5 < 2^62 := by
    rw [e_t3_5]; exact Nat.div_lt_of_lt_mul (lt_of_lt_of_eq b_q_2 (by norm_num))
  have sh_t3_5 : t3_4 + 2^64 * t3_5 = q_2 * 2^62 := by
    rw [e_t3_4, e_t3_5]; exact lsl62_lsr2_split _
  clear e_t3_4 e_t3_5
  -- r4_2: adc r4,xzr,xzr
  extract_lets +onlyGivenNames r4_2 at hr
  have e_r4_2 : r4_2 = (0 + 0 + c_17) % 2^64 := rfl
  clear_value r4_2
  have b_r4_2 : r4_2 < 2^64 := by rw [e_r4_2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨k_r4_2, b_k_r4_2, l_r4_2⟩ :
      ∃ k, k ≤ 1 ∧ r4_2 + 2^64 * k = 0 + 0 + c_17 :=
    ⟨(0 + 0 + c_17) / 2^64, addc_carry_le_one 0 0 c_17 (by decide) (by decide) b_c_17,
      by rw [e_r4_2]; exact Nat.mod_add_div _ _⟩
  clear e_r4_2
  -- r0_3: adds r0,r1,t0
  extract_lets +onlyGivenNames s_15 r0_3 c_18 at hr
  have e_r0_3 : r0_3 = (r1_5 + t0_2 + 0) % 2^64 := rfl
  have e_c_18 : c_18 = (r1_5 + t0_2 + 0) / 2^64 := rfl
  clear_value s_15 r0_3 c_18
  have l_r0_3 : r0_3 + 2^64 * c_18 = r1_5 + t0_2 + 0 := by
    rw [e_r0_3, e_c_18]; exact Nat.mod_add_div _ _
  have b_r0_3 : r0_3 < 2^64 := by rw [e_r0_3]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_18 : c_18 ≤ 1 := by
    rw [e_c_18]; exact addc_carry_le_one r1_5 t0_2 0 b_r1_5 b_t0_2 (by decide)
  clear e_r0_3 e_c_18
  -- r1_6: adcs r1,r2,t1
  extract_lets +onlyGivenNames s_16 r1_6 c_19 at hr
  have e_r1_6 : r1_6 = (r2_5 + t1_5 + c_18) % 2^64 := rfl
  have e_c_19 : c_19 = (r2_5 + t1_5 + c_18) / 2^64 := rfl
  clear_value s_16 r1_6 c_19
  have l_r1_6 : r1_6 + 2^64 * c_19 = r2_5 + t1_5 + c_18 := by
    rw [e_r1_6, e_c_19]; exact Nat.mod_add_div _ _
  have b_r1_6 : r1_6 < 2^64 := by rw [e_r1_6]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_19 : c_19 ≤ 1 := by
    rw [e_c_19]; exact addc_carry_le_one r2_5 t1_5 c_18 b_r2_5 b_t1_5 b_c_18
  clear e_r1_6 e_c_19
  -- r2_6: adcs r2,r3,xzr
  extract_lets +onlyGivenNames s_17 r2_6 c_20 at hr
  have e_r2_6 : r2_6 = (r3_5 + 0 + c_19) % 2^64 := rfl
  have e_c_20 : c_20 = (r3_5 + 0 + c_19) / 2^64 := rfl
  clear_value s_17 r2_6 c_20
  have l_r2_6 : r2_6 + 2^64 * c_20 = r3_5 + 0 + c_19 := by
    rw [e_r2_6, e_c_20]; exact Nat.mod_add_div _ _
  have b_r2_6 : r2_6 < 2^64 := by rw [e_r2_6]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_20 : c_20 ≤ 1 := by
    rw [e_c_20]; exact addc_carry_le_one r3_5 0 c_19 b_r3_5 (by decide) b_c_19
  clear e_r2_6 e_c_20
  -- q_3: mul q,inv,r0
  extract_lets +onlyGivenNames q_3 at hr
  have e_q_3 : q_3 = inv' * r0_3 % 2^64 := rfl
  clear_value q_3
  have b_q_3 : q_3 < 2^64 := by rw [e_q_3]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- r3_6: adc r3,r4,t3
  extract_lets +onlyGivenNames r3_6 at hr
  have e_r3_6 : r3_6 = (r4_2 + t3_5 + c_20) % 2^64 := rfl
  clear_value r3_6
  have b_r3_6 : r3_6 < 2^64 := by rw [e_r3_6]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨k_r3_6, b_k_r3_6, l_r3_6⟩ :
      ∃ k, k ≤ 1 ∧ r3_6 + 2^64 * k = r4_2 + t3_5 + c_20 :=
    ⟨(r4_2 + t3_5 + c_20) / 2^64, addc_carry_le_one r4_2 t3_5 c_20 b_r4_2 (lt_of_lt_of_le b_t3_5 (by norm_num)) b_c_20,
      by rw [e_r3_6]; exact Nat.mod_add_div _ _⟩
  clear e_r3_6
  -- t1_6: mul t1,p1,q
  extract_lets +onlyGivenNames t1_6 at hr
  have e_t1_6 : t1_6 = p1 * q_3 % 2^64 := rfl
  clear_value t1_6
  have b_t1_6 : t1_6 < 2^64 := by rw [e_t1_6]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- t3_6: lsl t3,q,#62
  extract_lets +onlyGivenNames t3_6 at hr
  have e_t3_6 : t3_6 = q_3 * 2^62 % 2^64 := rfl
  clear_value t3_6
  have b_t3_6 : t3_6 < 2^64 := by rw [e_t3_6]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- c_21: subs xzr,r0,#1
  extract_lets +onlyGivenNames c_21 at hr
  have e_c_21 : c_21 = (r0_3 + 2^64 - 1 - (1 - 1)) / 2^64 := rfl
  clear_value c_21
  have b_c_21 : c_21 ≤ 1 := by rw [e_c_21]; exact subc_carry_le_one r0_3 1 1 b_r0_3
  have l_c_21 : (c_21 = 1 ∧ 1 + 1 ≤ r0_3 + 1) ∨ (c_21 = 0 ∧ r0_3 + 1 < 1 + 1) :=
    subc_carry_cases r0_3 1 1 _ e_c_21 b_r0_3 (by decide) (by decide)
  clear e_c_21
  -- t0_3: umulh t0,p0,q
  extract_lets +onlyGivenNames t0_3 at hr
  have e_t0_3 : t0_3 = p0 * q_3 / 2^64 := rfl
  clear_value t0_3
  have p_t0_3 : p0 * q_3 < 2^64 * 2^64 := Nat.mul_lt_mul'' b_p0 b_q_3
  have b_t0_3 : t0_3 < 2^64 := by rw [e_t0_3]; exact Nat.div_lt_of_lt_mul p_t0_3
  obtain ⟨lo_t0_3, b_lo_t0_3, d_t0_3⟩ :
      ∃ lo, lo < 2^64 ∧ lo + 2^64 * t0_3 = p0 * q_3 :=
    ⟨p0 * q_3 % 2^64, Nat.mod_lt _ (Nat.two_pow_pos _),
      by rw [e_t0_3]; exact Nat.mod_add_div _ _⟩
  clear e_t0_3
  -- r1_7: adcs r1,r1,t1
  extract_lets +onlyGivenNames s_18 r1_7 c_22 at hr
  have e_r1_7 : r1_7 = (r1_6 + t1_6 + c_21) % 2^64 := rfl
  have e_c_22 : c_22 = (r1_6 + t1_6 + c_21) / 2^64 := rfl
  clear_value s_18 r1_7 c_22
  have l_r1_7 : r1_7 + 2^64 * c_22 = r1_6 + t1_6 + c_21 := by
    rw [e_r1_7, e_c_22]; exact Nat.mod_add_div _ _
  have b_r1_7 : r1_7 < 2^64 := by rw [e_r1_7]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_22 : c_22 ≤ 1 := by
    rw [e_c_22]; exact addc_carry_le_one r1_6 t1_6 c_21 b_r1_6 b_t1_6 b_c_21
  clear e_r1_7 e_c_22
  -- t1_7: umulh t1,p1,q
  extract_lets +onlyGivenNames t1_7 at hr
  have e_t1_7 : t1_7 = p1 * q_3 / 2^64 := rfl
  clear_value t1_7
  have p_t1_7 : p1 * q_3 < 2^64 * 2^64 := Nat.mul_lt_mul'' b_p1 b_q_3
  have b_t1_7 : t1_7 < 2^64 := by rw [e_t1_7]; exact Nat.div_lt_of_lt_mul p_t1_7
  have d_t1_7 : t1_6 + 2^64 * t1_7 = p1 * q_3 := by
    rw [e_t1_6, e_t1_7]; exact Nat.mod_add_div _ _
  clear e_t1_6 e_t1_7
  -- r2_7: adcs r2,r2,xzr
  extract_lets +onlyGivenNames s_19 r2_7 c_23 at hr
  have e_r2_7 : r2_7 = (r2_6 + 0 + c_22) % 2^64 := rfl
  have e_c_23 : c_23 = (r2_6 + 0 + c_22) / 2^64 := rfl
  clear_value s_19 r2_7 c_23
  have l_r2_7 : r2_7 + 2^64 * c_23 = r2_6 + 0 + c_22 := by
    rw [e_r2_7, e_c_23]; exact Nat.mod_add_div _ _
  have b_r2_7 : r2_7 < 2^64 := by rw [e_r2_7]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_23 : c_23 ≤ 1 := by
    rw [e_c_23]; exact addc_carry_le_one r2_6 0 c_22 b_r2_6 (by decide) b_c_22
  clear e_r2_7 e_c_23
  -- r3_7: adcs r3,r3,t3
  extract_lets +onlyGivenNames s_20 r3_7 c_24 at hr
  have e_r3_7 : r3_7 = (r3_6 + t3_6 + c_23) % 2^64 := rfl
  have e_c_24 : c_24 = (r3_6 + t3_6 + c_23) / 2^64 := rfl
  clear_value s_20 r3_7 c_24
  have l_r3_7 : r3_7 + 2^64 * c_24 = r3_6 + t3_6 + c_23 := by
    rw [e_r3_7, e_c_24]; exact Nat.mod_add_div _ _
  have b_r3_7 : r3_7 < 2^64 := by rw [e_r3_7]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_24 : c_24 ≤ 1 := by
    rw [e_c_24]; exact addc_carry_le_one r3_6 t3_6 c_23 b_r3_6 b_t3_6 b_c_23
  clear e_r3_7 e_c_24
  -- t3_7: lsr t3,q,#2
  extract_lets +onlyGivenNames t3_7 at hr
  have e_t3_7 : t3_7 = q_3 / 2^2 := rfl
  clear_value t3_7
  have b_t3_7 : t3_7 < 2^62 := by
    rw [e_t3_7]; exact Nat.div_lt_of_lt_mul (lt_of_lt_of_eq b_q_3 (by norm_num))
  have sh_t3_7 : t3_6 + 2^64 * t3_7 = q_3 * 2^62 := by
    rw [e_t3_6, e_t3_7]; exact lsl62_lsr2_split _
  clear e_t3_6 e_t3_7
  -- r4_3: adc r4,xzr,xzr
  extract_lets +onlyGivenNames r4_3 at hr
  have e_r4_3 : r4_3 = (0 + 0 + c_24) % 2^64 := rfl
  clear_value r4_3
  have b_r4_3 : r4_3 < 2^64 := by rw [e_r4_3]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨k_r4_3, b_k_r4_3, l_r4_3⟩ :
      ∃ k, k ≤ 1 ∧ r4_3 + 2^64 * k = 0 + 0 + c_24 :=
    ⟨(0 + 0 + c_24) / 2^64, addc_carry_le_one 0 0 c_24 (by decide) (by decide) b_c_24,
      by rw [e_r4_3]; exact Nat.mod_add_div _ _⟩
  clear e_r4_3
  -- r0_4: adds r0,r1,t0
  extract_lets +onlyGivenNames s_21 r0_4 c_25 at hr
  have e_r0_4 : r0_4 = (r1_7 + t0_3 + 0) % 2^64 := rfl
  have e_c_25 : c_25 = (r1_7 + t0_3 + 0) / 2^64 := rfl
  clear_value s_21 r0_4 c_25
  have l_r0_4 : r0_4 + 2^64 * c_25 = r1_7 + t0_3 + 0 := by
    rw [e_r0_4, e_c_25]; exact Nat.mod_add_div _ _
  have b_r0_4 : r0_4 < 2^64 := by rw [e_r0_4]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_25 : c_25 ≤ 1 := by
    rw [e_c_25]; exact addc_carry_le_one r1_7 t0_3 0 b_r1_7 b_t0_3 (by decide)
  clear e_r0_4 e_c_25
  -- r1_8: adcs r1,r2,t1
  extract_lets +onlyGivenNames s_22 r1_8 c_26 at hr
  have e_r1_8 : r1_8 = (r2_7 + t1_7 + c_25) % 2^64 := rfl
  have e_c_26 : c_26 = (r2_7 + t1_7 + c_25) / 2^64 := rfl
  clear_value s_22 r1_8 c_26
  have l_r1_8 : r1_8 + 2^64 * c_26 = r2_7 + t1_7 + c_25 := by
    rw [e_r1_8, e_c_26]; exact Nat.mod_add_div _ _
  have b_r1_8 : r1_8 < 2^64 := by rw [e_r1_8]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_26 : c_26 ≤ 1 := by
    rw [e_c_26]; exact addc_carry_le_one r2_7 t1_7 c_25 b_r2_7 b_t1_7 b_c_25
  clear e_r1_8 e_c_26
  -- r2_8: adcs r2,r3,xzr
  extract_lets +onlyGivenNames s_23 r2_8 c_27 at hr
  have e_r2_8 : r2_8 = (r3_7 + 0 + c_26) % 2^64 := rfl
  have e_c_27 : c_27 = (r3_7 + 0 + c_26) / 2^64 := rfl
  clear_value s_23 r2_8 c_27
  have l_r2_8 : r2_8 + 2^64 * c_27 = r3_7 + 0 + c_26 := by
    rw [e_r2_8, e_c_27]; exact Nat.mod_add_div _ _
  have b_r2_8 : r2_8 < 2^64 := by rw [e_r2_8]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_27 : c_27 ≤ 1 := by
    rw [e_c_27]; exact addc_carry_le_one r3_7 0 c_26 b_r3_7 (by decide) b_c_26
  clear e_r2_8 e_c_27
  -- r3_8: adc r3,r4,t3
  extract_lets +onlyGivenNames r3_8 at hr
  have e_r3_8 : r3_8 = (r4_3 + t3_7 + c_27) % 2^64 := rfl
  clear_value r3_8
  have b_r3_8 : r3_8 < 2^64 := by rw [e_r3_8]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨k_r3_8, b_k_r3_8, l_r3_8⟩ :
      ∃ k, k ≤ 1 ∧ r3_8 + 2^64 * k = r4_3 + t3_7 + c_27 :=
    ⟨(r4_3 + t3_7 + c_27) / 2^64, addc_carry_le_one r4_3 t3_7 c_27 b_r4_3 (lt_of_lt_of_le b_t3_7 (by norm_num)) b_c_27,
      by rw [e_r3_8]; exact Nat.mod_add_div _ _⟩
  clear e_r3_8
  -- r0_5: adds r0,r0,h0
  extract_lets +onlyGivenNames s_24 r0_5 c_28 at hr
  have e_r0_5 : r0_5 = (r0_4 + h0 + 0) % 2^64 := rfl
  have e_c_28 : c_28 = (r0_4 + h0 + 0) / 2^64 := rfl
  clear_value s_24 r0_5 c_28
  have l_r0_5 : r0_5 + 2^64 * c_28 = r0_4 + h0 + 0 := by
    rw [e_r0_5, e_c_28]; exact Nat.mod_add_div _ _
  have b_r0_5 : r0_5 < 2^64 := by rw [e_r0_5]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_28 : c_28 ≤ 1 := by
    rw [e_c_28]; exact addc_carry_le_one r0_4 h0 0 b_r0_4 b_h0 (by decide)
  clear e_r0_5 e_c_28
  -- r1_9: adcs r1,r1,h1
  extract_lets +onlyGivenNames s_25 r1_9 c_29 at hr
  have e_r1_9 : r1_9 = (r1_8 + h1 + c_28) % 2^64 := rfl
  have e_c_29 : c_29 = (r1_8 + h1 + c_28) / 2^64 := rfl
  clear_value s_25 r1_9 c_29
  have l_r1_9 : r1_9 + 2^64 * c_29 = r1_8 + h1 + c_28 := by
    rw [e_r1_9, e_c_29]; exact Nat.mod_add_div _ _
  have b_r1_9 : r1_9 < 2^64 := by rw [e_r1_9]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_29 : c_29 ≤ 1 := by
    rw [e_c_29]; exact addc_carry_le_one r1_8 h1 c_28 b_r1_8 b_h1 b_c_28
  clear e_r1_9 e_c_29
  -- r2_9: adcs r2,r2,h2
  extract_lets +onlyGivenNames s_26 r2_9 c_30 at hr
  have e_r2_9 : r2_9 = (r2_8 + h2 + c_29) % 2^64 := rfl
  have e_c_30 : c_30 = (r2_8 + h2 + c_29) / 2^64 := rfl
  clear_value s_26 r2_9 c_30
  have l_r2_9 : r2_9 + 2^64 * c_30 = r2_8 + h2 + c_29 := by
    rw [e_r2_9, e_c_30]; exact Nat.mod_add_div _ _
  have b_r2_9 : r2_9 < 2^64 := by rw [e_r2_9]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_30 : c_30 ≤ 1 := by
    rw [e_c_30]; exact addc_carry_le_one r2_8 h2 c_29 b_r2_8 b_h2 b_c_29
  clear e_r2_9 e_c_30
  -- r3_9: adcs r3,r3,h3
  extract_lets +onlyGivenNames s_27 r3_9 c_31 at hr
  have e_r3_9 : r3_9 = (r3_8 + h3 + c_30) % 2^64 := rfl
  have e_c_31 : c_31 = (r3_8 + h3 + c_30) / 2^64 := rfl
  clear_value s_27 r3_9 c_31
  have l_r3_9 : r3_9 + 2^64 * c_31 = r3_8 + h3 + c_30 := by
    rw [e_r3_9, e_c_31]; exact Nat.mod_add_div _ _
  have b_r3_9 : r3_9 < 2^64 := by rw [e_r3_9]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_31 : c_31 ≤ 1 := by
    rw [e_c_31]; exact addc_carry_le_one r3_8 h3 c_30 b_r3_8 b_h3 b_c_30
  clear e_r3_9 e_c_31
  -- r4_4: adc r4,xzr,xzr
  extract_lets +onlyGivenNames r4_4 at hr
  have e_r4_4 : r4_4 = (0 + 0 + c_31) % 2^64 := rfl
  clear_value r4_4
  have b_r4_4 : r4_4 < 2^64 := by rw [e_r4_4]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨k_r4_4, b_k_r4_4, l_r4_4⟩ :
      ∃ k, k ≤ 1 ∧ r4_4 + 2^64 * k = 0 + 0 + c_31 :=
    ⟨(0 + 0 + c_31) / 2^64, addc_carry_le_one 0 0 c_31 (by decide) (by decide) b_c_31,
      by rw [e_r4_4]; exact Nat.mod_add_div _ _⟩
  clear e_r4_4
  -- t0_4: subs t0,r0,p0
  extract_lets +onlyGivenNames s_28 t0_4 c_32 at hr
  have e_t0_4 : t0_4 = (r0_5 + 2^64 - p0 - (1 - 1)) % 2^64 := rfl
  have e_c_32 : c_32 = (r0_5 + 2^64 - p0 - (1 - 1)) / 2^64 := rfl
  clear_value s_28 t0_4 c_32
  have l_t0_4 : t0_4 + 2^64 * c_32 + p0 + 1 = r0_5 + 2^64 + 1 := by
    rw [e_t0_4, e_c_32]; exact subc_lin r0_5 p0 1 b_p0 (by decide)
  have b_t0_4 : t0_4 < 2^64 := by rw [e_t0_4]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_32 : c_32 ≤ 1 := by
    rw [e_c_32]; exact subc_carry_le_one r0_5 p0 1 b_r0_5
  clear e_t0_4 e_c_32
  -- t1_8: sbcs t1,r1,p1
  extract_lets +onlyGivenNames s_29 t1_8 c_33 at hr
  have e_t1_8 : t1_8 = (r1_9 + 2^64 - p1 - (1 - c_32)) % 2^64 := rfl
  have e_c_33 : c_33 = (r1_9 + 2^64 - p1 - (1 - c_32)) / 2^64 := rfl
  clear_value s_29 t1_8 c_33
  have l_t1_8 : t1_8 + 2^64 * c_33 + p1 + 1 = r1_9 + 2^64 + c_32 := by
    rw [e_t1_8, e_c_33]; exact subc_lin r1_9 p1 c_32 b_p1 b_c_32
  have b_t1_8 : t1_8 < 2^64 := by rw [e_t1_8]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_33 : c_33 ≤ 1 := by
    rw [e_c_33]; exact subc_carry_le_one r1_9 p1 c_32 b_r1_9
  clear e_t1_8 e_c_33
  -- t2: sbcs t2,r2,p2
  extract_lets +onlyGivenNames s_30 t2 c_34 at hr
  have e_t2 : t2 = (r2_9 + 2^64 - p2 - (1 - c_33)) % 2^64 := rfl
  have e_c_34 : c_34 = (r2_9 + 2^64 - p2 - (1 - c_33)) / 2^64 := rfl
  clear_value s_30 t2 c_34
  have l_t2 : t2 + 2^64 * c_34 + p2 + 1 = r2_9 + 2^64 + c_33 := by
    rw [e_t2, e_c_34]; exact subc_lin r2_9 p2 c_33 b_p2 b_c_33
  have b_t2 : t2 < 2^64 := by rw [e_t2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_34 : c_34 ≤ 1 := by
    rw [e_c_34]; exact subc_carry_le_one r2_9 p2 c_33 b_r2_9
  clear e_t2 e_c_34
  -- t3_8: sbcs t3,r3,p3
  extract_lets +onlyGivenNames s_31 t3_8 c_35 at hr
  have e_t3_8 : t3_8 = (r3_9 + 2^64 - p3 - (1 - c_34)) % 2^64 := rfl
  have e_c_35 : c_35 = (r3_9 + 2^64 - p3 - (1 - c_34)) / 2^64 := rfl
  clear_value s_31 t3_8 c_35
  have l_t3_8 : t3_8 + 2^64 * c_35 + p3 + 1 = r3_9 + 2^64 + c_34 := by
    rw [e_t3_8, e_c_35]; exact subc_lin r3_9 p3 c_34 b_p3 b_c_34
  have b_t3_8 : t3_8 < 2^64 := by rw [e_t3_8]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c_35 : c_35 ≤ 1 := by
    rw [e_c_35]; exact subc_carry_le_one r3_9 p3 c_34 b_r3_9
  clear e_t3_8 e_c_35
  -- c_36: sbcs xzr,r4,xzr
  extract_lets +onlyGivenNames c_36 at hr
  have e_c_36 : c_36 = (r4_4 + 2^64 - 0 - (1 - c_35)) / 2^64 := rfl
  clear_value c_36
  have b_c_36 : c_36 ≤ 1 := by rw [e_c_36]; exact subc_carry_le_one r4_4 0 c_35 b_r4_4
  have l_c_36 : (c_36 = 1 ∧ 0 + 1 ≤ r4_4 + c_35) ∨ (c_36 = 0 ∧ r4_4 + c_35 < 0 + 1) :=
    subc_carry_cases r4_4 0 c_35 _ e_c_36 b_r4_4 (by decide) b_c_35
  clear e_c_36
  -- r0_6: csel r0,r0,t0,lo
  extract_lets +onlyGivenNames r0_6 at hr
  have e_r0_6 : r0_6 = (if c_36 = 0 then r0_5 else t0_4) := rfl
  clear_value r0_6
  have b_r0_6 : r0_6 < 2^64 := by
    rw [e_r0_6]; split <;> first | exact b_r0_5 | exact b_t0_4
  -- r1_10: csel r1,r1,t1,lo
  extract_lets +onlyGivenNames r1_10 at hr
  have e_r1_10 : r1_10 = (if c_36 = 0 then r1_9 else t1_8) := rfl
  clear_value r1_10
  have b_r1_10 : r1_10 < 2^64 := by
    rw [e_r1_10]; split <;> first | exact b_r1_9 | exact b_t1_8
  -- r2_10: csel r2,r2,t2,lo
  extract_lets +onlyGivenNames r2_10 at hr
  have e_r2_10 : r2_10 = (if c_36 = 0 then r2_9 else t2) := rfl
  clear_value r2_10
  have b_r2_10 : r2_10 < 2^64 := by
    rw [e_r2_10]; split <;> first | exact b_r2_9 | exact b_t2
  -- r3_10: csel r3,r3,t3,lo
  extract_lets +onlyGivenNames r3_10 at hr
  have e_r3_10 : r3_10 = (if c_36 = 0 then r3_9 else t3_8) := rfl
  clear_value r3_10
  have b_r3_10 : r3_10 < 2^64 := by
    rw [e_r3_10]; split <;> first | exact b_r3_9 | exact b_t3_8
  subst hr
  -- BEGIN redcMont conclusion
  sorry
  /-
  have hP : modulus.toNat = p0 + 2^64 * p1 + 2^254 := by
    rw [e_p0, e_p1]
    simp only [Limbs.toNat, hshape.1, hshape.2, Nat.mul_zero, Nat.add_zero]
  have hp : 0 < modulus.toNat := by rw [hP]; positivity
  have hpR : modulus.toNat < 2^256 := Limbs.toNat_lt modulus hm
  have hp255 : modulus.toNat < 2^255 := Limbs.toNat_lt_of_shape modulus hm hshape
  have hlo : low.toNat = r0 + 2^64 * r1 + 2^128 * r2 + 2^192 * r3 := by
    simp only [Limbs.toNat, e_r0, e_r1, e_r2, e_r3]
  have hhi : high.toNat = h0 + 2^64 * h1 + 2^128 * h2 + 2^192 * h3 := by
    simp only [Limbs.toNat, e_h0, e_h1, e_h2, e_h3]
  have hloR : low.toNat < 2^256 := Limbs.toNat_lt low hlow
  have hhiR : high.toNat < 2^256 := Limbs.toNat_lt high hhigh
  have hqp (q' : Nat) : q' * modulus.toNat =
      p0 * q' + 2^64 * (p1 * q') + 2^254 * q' := by
    rw [hP]
    ring
  have hqbound {q' : Nat} (hq' : q' < 2^64) : q' * modulus.toNat < 2^319 := by
    have h := Nat.mul_lt_mul'' hq' hp255
    norm_num at h ⊢
    exact h
  have hcancel0 : r0 + lo_t0 = 2^64 * c := by
    have h := cancel_low r0 inv' p0 (by rw [e_inv', e_p0]; exact hinv_spec)
    rw [← e_q, ← d_t0, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt b_lo_t0] at h
    clear * - h b_r0 b_lo_t0 l_c
    omega
  have hlimit0 :
      (r0 + 2^64 * r1 + 2^128 * r2 + 2^192 * r3) +
        q * modulus.toNat < 2^320 := by
    have hqb := hqbound b_q
    rw [← hlo]
    omega
  obtain ⟨hk4_0, hk3_0, hround0⟩ := redcMont_step hcancel0 d_t0 d_t1_1
    l_r1_1 l_r2_1 l_r3_1 sh_t3_1 l_r4 l_r0_1 l_r1_2 l_r2_2 l_r3_2
    (hqp q) hlimit0
  let y1 := r0_1 + 2^64 * r1_2 + 2^128 * r2_2 + 2^192 * r3_2
  have hy1R : y1 < 2^256 := by
    dsimp only [y1]
    clear * - b_r0_1 b_r1_2 b_r2_2 b_r3_2
    omega

  have hcancel1 : r0_1 + lo_t0_1 = 2^64 * c_7 := by
    have h := cancel_low r0_1 inv' p0 (by rw [e_inv', e_p0]; exact hinv_spec)
    rw [← e_q_1, ← d_t0_1, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt b_lo_t0_1] at h
    clear * - h b_r0_1 b_lo_t0_1 l_c_7
    omega
  have hlimit1 : y1 + q_1 * modulus.toNat < 2^320 := by
    have hqb := hqbound b_q_1
    omega
  obtain ⟨hk4_1, hk3_1, hround1⟩ := redcMont_step hcancel1 d_t0_1 d_t1_3
    l_r1_3 l_r2_3 l_r3_3 sh_t3_3 l_r4_1 l_r0_2 l_r1_4 l_r2_4 l_r3_4
    (hqp q_1) (by simpa only [y1] using hlimit1)
  let y2 := r0_2 + 2^64 * r1_4 + 2^128 * r2_4 + 2^192 * r3_4
  have hy2R : y2 < 2^256 := by
    dsimp only [y2]
    clear * - b_r0_2 b_r1_4 b_r2_4 b_r3_4
    omega

  have hcancel2 : r0_2 + lo_t0_2 = 2^64 * c_14 := by
    have h := cancel_low r0_2 inv' p0 (by rw [e_inv', e_p0]; exact hinv_spec)
    rw [← e_q_2, ← d_t0_2, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt b_lo_t0_2] at h
    clear * - h b_r0_2 b_lo_t0_2 l_c_14
    omega
  have hlimit2 : y2 + q_2 * modulus.toNat < 2^320 := by
    have hqb := hqbound b_q_2
    omega
  obtain ⟨hk4_2, hk3_2, hround2⟩ := redcMont_step hcancel2 d_t0_2 d_t1_5
    l_r1_5 l_r2_5 l_r3_5 sh_t3_5 l_r4_2 l_r0_3 l_r1_6 l_r2_6 l_r3_6
    (hqp q_2) (by simpa only [y2] using hlimit2)
  let y3 := r0_3 + 2^64 * r1_6 + 2^128 * r2_6 + 2^192 * r3_6
  have hy3R : y3 < 2^256 := by
    dsimp only [y3]
    clear * - b_r0_3 b_r1_6 b_r2_6 b_r3_6
    omega

  have hcancel3 : r0_3 + lo_t0_3 = 2^64 * c_21 := by
    have h := cancel_low r0_3 inv' p0 (by rw [e_inv', e_p0]; exact hinv_spec)
    rw [← e_q_3, ← d_t0_3, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt b_lo_t0_3] at h
    clear * - h b_r0_3 b_lo_t0_3 l_c_21
    omega
  have hlimit3 : y3 + q_3 * modulus.toNat < 2^320 := by
    have hqb := hqbound b_q_3
    omega
  obtain ⟨hk4_3, hk3_3, hround3⟩ := redcMont_step hcancel3 d_t0_3 d_t1_7
    l_r1_7 l_r2_7 l_r3_7 sh_t3_7 l_r4_3 l_r0_4 l_r1_8 l_r2_8 l_r3_8
    (hqp q_3) (by simpa only [y3] using hlimit3)
  let y := r0_4 + 2^64 * r1_8 + 2^128 * r2_8 + 2^192 * r3_8
  have hyR : y < 2^256 := by
    dsimp only [y]
    clear * - b_r0_4 b_r1_8 b_r2_8 b_r3_8
    omega
  have hround0' : 2^64 * y1 = low.toNat + q * modulus.toNat := by
    simpa only [y1, hlo] using hround0
  have hround1' : 2^64 * y2 = y1 + q_1 * modulus.toNat := by
    simpa only [y1, y2] using hround1
  have hround2' : 2^64 * y3 = y2 + q_2 * modulus.toNat := by
    simpa only [y2, y3] using hround2
  have hround3' : 2^64 * y = y3 + q_3 * modulus.toNat := by
    simpa only [y3, y] using hround3
  have hfour := redcMont_compose4 hround0' hround1' hround2' hround3'
  let m := q + 2^64 * q_1 + 2^128 * q_2 + 2^192 * q_3
  have hmR : m < 2^256 := by
    dsimp only [m]
    clear * - b_q b_q_1 b_q_2 b_q_3
    omega
  have hcancel : y * 2^256 = low.toNat + m * modulus.toNat := by
    rw [Nat.mul_comm]
    calc
      2^256 * y = low.toNat + q * modulus.toNat +
          2^64 * (q_1 * modulus.toNat) +
          2^128 * (q_2 * modulus.toNat) +
          2^192 * (q_3 * modulus.toNat) := hfour
      _ = low.toNat + m * modulus.toNat := by simp only [m]; ring
  have hyp : y ≤ modulus.toNat := redcMont_reduced_le hp hloR hmR hcancel

  let candidate := high.toNat + y
  have hT : low.toNat + 2^256 * high.toNat =
      low.toNat + 2^256 * high.toNat := rfl
  have hTlt : low.toNat + 2^256 * high.toNat < 2^256 * 2^256 := by
    omega
  have hspec := PastaAsm.REDC.full512_spec hp hpR hT hTlt hcancel hmR hyp
  have hcandlt : candidate < 2^256 + modulus.toNat := by
    exact PastaAsm.REDC.full512_candidate_lt hp hpR hT hTlt hyp

  have hkadd : k_r4_4 = 0 := by
    clear * - l_r4_4 b_c_31
    omega
  have hadd :
      r0_5 + 2^64 * r1_9 + 2^128 * r2_9 + 2^192 * r3_9 + 2^256 * r4_4 =
        candidate := by
    dsimp only [candidate, y]
    rw [hhi]
    clear * - l_r0_5 l_r1_9 l_r2_9 l_r3_9 l_r4_4 hkadd
    omega
  have htop : r4_4 ≤ 1 := by clear * - l_r4_4 hkadd b_c_31; omega
  have hlowFinal :
      r0_5 + 2^64 * r1_9 + 2^128 * r2_9 + 2^192 * r3_9 < 2^256 := by
    clear * - b_r0_5 b_r1_9 b_r2_9 b_r3_9
    omega
  have hdiffBound :
      t0_4 + 2^64 * t1_8 + 2^128 * t2 + 2^192 * t3_8 < 2^256 := by
    clear * - b_t0_4 b_t1_8 b_t2 b_t3_8
    omega
  have hdiff :
      (t0_4 + 2^64 * t1_8 + 2^128 * t2 + 2^192 * t3_8) + modulus.toNat +
          2^256 * c_35 =
        (r0_5 + 2^64 * r1_9 + 2^128 * r2_9 + 2^192 * r3_9) + 2^256 := by
    rw [hP]
    clear * - l_t0_4 l_t1_8 l_t2 l_t3_8 e_p2 e_p3 hshape
    subst p2
    subst p3
    omega
  let outNat := r0_6 + 2^64 * r1_10 + 2^128 * r2_10 + 2^192 * r3_10
  have houtSelect : outNat = if c_36 = 0 then
      (r0_5 + 2^64 * r1_9 + 2^128 * r2_9 + 2^192 * r3_9)
    else (t0_4 + 2^64 * t1_8 + 2^128 * t2 + 2^192 * t3_8) := by
    dsimp only [outNat]
    by_cases hc : c_36 = 0
    · rw [if_pos hc] at e_r0_6 e_r1_10 e_r2_10 e_r3_10 ⊢
      omega
    · rw [if_neg hc] at e_r0_6 e_r1_10 e_r2_10 e_r3_10 ⊢
      omega
  have houtCorrect : outNat = PastaAsm.REDC.carryCorrect candidate modulus.toNat :=
    redcMont_tail hpR hcandlt hadd hlowFinal htop hdiff b_c_35 hdiffBound
      l_c_36 houtSelect
  refine ⟨⟨b_r0_6, b_r1_10, b_r2_10, b_r3_10⟩, ?_⟩
  change 2^256 * outNat ≡ low.toNat + 2^256 * high.toNat [MOD modulus.toNat]
  rw [houtCorrect]
  exact hspec.2
  -/
  -- END redcMont conclusion

end PastaAsm.AArch64
