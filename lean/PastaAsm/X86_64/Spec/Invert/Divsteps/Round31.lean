/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.X86_64.Spec.Invert.Divsteps.Lemmas

/-!
# Correctness of one x86-64 packed approximation round

The generated instruction trace implements one shared approximation step.  The two coefficient
rows remain packed as biased 32-bit lanes in `a1` and `a2`.
-/

namespace PastaAsm.X86_64

open InversionSpec InversionConvergence

-- BEGIN divsteps31Round_spec statement
/-- One packed inner-loop iteration follows `approxStep` and preserves the two biased row words. -/
theorem divsteps31Round_spec (s : Divsteps31State) (abstract : ApproxState)
    (hs : s.Bounded) (hstate : s.a0 = abstract.a ∧ s.b0 = abstract.b)
    (hrows : PackedRowRep s.a1 abstract.matrix.row0 ∧
      PackedRowRep s.a2 abstract.matrix.row1)
    (hbias : s.a3 = packedRowBias) (hodd : Odd abstract.b) :
    ∀ s', s' = divsteps31Round s →
      s'.Bounded ∧ s'.a0 = (approxStep abstract).a ∧
        s'.b0 = (approxStep abstract).b ∧
        PackedRowRep s'.a1 (approxStep abstract).matrix.row0 ∧
        PackedRowRep s'.a2 (approxStep abstract).matrix.row1 ∧
        s'.a3 = packedRowBias ∧ Odd (approxStep abstract).b := by
  intro s' hr
-- END divsteps31Round_spec statement
  -- generated skeleton for `divsteps31Round`: do not edit between the annotations
  unfold divsteps31Round at hr
  lift_lets at hr
  -- a0: input a0
  extract_lets +onlyGivenNames a0 at hr
  have e_a0 : a0 = s.a0 := rfl
  clear_value a0
  have b_a0 : a0 < 2^64 := by rw [e_a0]; exact hs.1
  -- a1: input a1
  extract_lets +onlyGivenNames a1 at hr
  have e_a1 : a1 = s.a1 := rfl
  clear_value a1
  have b_a1 : a1 < 2^64 := by rw [e_a1]; exact hs.2.1
  -- a2: input a2
  extract_lets +onlyGivenNames a2 at hr
  have e_a2 : a2 = s.a2 := rfl
  clear_value a2
  have b_a2 : a2 < 2^64 := by rw [e_a2]; exact hs.2.2.1
  -- a3: input a3
  extract_lets +onlyGivenNames a3 at hr
  have e_a3 : a3 = s.a3 := rfl
  clear_value a3
  have b_a3 : a3 < 2^64 := by rw [e_a3]; exact hs.2.2.2.1
  -- b0: input b0
  extract_lets +onlyGivenNames b0 at hr
  have e_b0 : b0 = s.b0 := rfl
  clear_value b0
  have b_b0 : b0 < 2^64 := by rw [e_b0]; exact hs.2.2.2.2.1
  -- b1: input b1
  extract_lets +onlyGivenNames b1 at hr
  have e_b1 : b1 = s.b1 := rfl
  clear_value b1
  have b_b1 : b1 < 2^64 := by rw [e_b1]; exact hs.2.2.2.2.2.1
  -- b2: input b2
  extract_lets +onlyGivenNames b2 at hr
  have e_b2 : b2 = s.b2 := rfl
  clear_value b2
  have b_b2 : b2 < 2^64 := by rw [e_b2]; exact hs.2.2.2.2.2.2.1
  -- b3: input b3
  extract_lets +onlyGivenNames b3 at hr
  have e_b3 : b3 = s.b3 := rfl
  clear_value b3
  have b_b3 : b3 < 2^64 := by rw [e_b3]; exact hs.2.2.2.2.2.2.2.1
  -- cf: cmp {a0}, {b0}
  extract_lets +onlyGivenNames cf at hr
  have e_cf : cf = (sbb a0 b0 0).2 := rfl
  clear_value cf
  have b_cf : cf ≤ 1 := by rw [e_cf]; exact sbb_borrow_le_one a0 b0 0
  -- b1_1: mov {b1}, {a0}
  extract_lets +onlyGivenNames b1_1 at hr
  have e_b1_1 : b1_1 = a0 := rfl
  clear_value b1_1
  have b_b1_1 : b1_1 < 2^64 := by rw [e_b1_1]; exact b_a0
  -- b2_1: mov {b2}, {b0}
  extract_lets +onlyGivenNames b2_1 at hr
  have e_b2_1 : b2_1 = b0 := rfl
  clear_value b2_1
  have b_b2_1 : b2_1 < 2^64 := by rw [e_b2_1]; exact b_b0
  -- b3_1: mov {b3}, {a1}
  extract_lets +onlyGivenNames b3_1 at hr
  have e_b3_1 : b3_1 = a1 := rfl
  clear_value b3_1
  have b_b3_1 : b3_1 < 2^64 := by rw [e_b3_1]; exact b_a1
  -- t: mov {t}, {a2}
  extract_lets +onlyGivenNames t at hr
  have e_t : t = a2 := rfl
  clear_value t
  have b_t : t < 2^64 := by rw [e_t]; exact b_a2
  -- a0_1: cmovb {a0}, {b0}
  extract_lets +onlyGivenNames a0_1 at hr
  have e_a0_1 : a0_1 = (if cf = 0 then a0 else b0) := rfl
  clear_value a0_1
  have b_a0_1 : a0_1 < 2^64 := by
    rw [e_a0_1]; split <;> first | exact b_a0 | exact b_b0
  -- b0_1: cmovb {b0}, {b1}
  extract_lets +onlyGivenNames b0_1 at hr
  have e_b0_1 : b0_1 = (if cf = 0 then b0 else b1_1) := rfl
  clear_value b0_1
  have b_b0_1 : b0_1 < 2^64 := by
    rw [e_b0_1]; split <;> first | exact b_b0 | exact b_b1_1
  -- a1_1: cmovb {a1}, {a2}
  extract_lets +onlyGivenNames a1_1 at hr
  have e_a1_1 : a1_1 = (if cf = 0 then a1 else a2) := rfl
  clear_value a1_1
  have b_a1_1 : a1_1 < 2^64 := by
    rw [e_a1_1]; split <;> first | exact b_a1 | exact b_a2
  -- a2_1: cmovb {a2}, {b3}
  extract_lets +onlyGivenNames a2_1 at hr
  have e_a2_1 : a2_1 = (if cf = 0 then a2 else b3_1) := rfl
  clear_value a2_1
  have b_a2_1 : a2_1 < 2^64 := by
    rw [e_a2_1]; split <;> first | exact b_a2 | exact b_b3_1
  -- a0_2: sub {a0}, {b0}
  extract_lets +onlyGivenNames s a0_2 cf_1 at hr
  have e_a0_2 : a0_2 = (sbb a0_1 b0_1 0).1 := rfl
  have e_cf_1 : cf_1 = (sbb a0_1 b0_1 0).2 := rfl
  clear_value s a0_2 cf_1
  have l_a0_2 : a0_2 + b0_1 + 0 = a0_1 + 2^64 * cf_1 := by
    rw [e_a0_2, e_cf_1]; exact sbb_lin a0_1 b0_1 0 b_a0_1 b_b0_1 (by decide)
  have b_a0_2 : a0_2 < 2^64 := by rw [e_a0_2]; exact sbb_value_lt a0_1 b0_1 0
  have b_cf_1 : cf_1 ≤ 1 := by rw [e_cf_1]; exact sbb_borrow_le_one a0_1 b0_1 0
  clear e_a0_2 e_cf_1
  -- a1_2: sub {a1}, {a2}
  extract_lets +onlyGivenNames s_1 a1_2 cf_2 at hr
  have e_a1_2 : a1_2 = (sbb a1_1 a2_1 0).1 := rfl
  have e_cf_2 : cf_2 = (sbb a1_1 a2_1 0).2 := rfl
  clear_value s_1 a1_2 cf_2
  have l_a1_2 : a1_2 + a2_1 + 0 = a1_1 + 2^64 * cf_2 := by
    rw [e_a1_2, e_cf_2]; exact sbb_lin a1_1 a2_1 0 b_a1_1 b_a2_1 (by decide)
  have b_a1_2 : a1_2 < 2^64 := by rw [e_a1_2]; exact sbb_value_lt a1_1 a2_1 0
  have b_cf_2 : cf_2 ≤ 1 := by rw [e_cf_2]; exact sbb_borrow_le_one a1_1 a2_1 0
  clear e_a1_2 e_cf_2
  -- a1_3: add {a1}, {a3}
  extract_lets +onlyGivenNames s_2 a1_3 cf_3 at hr
  have e_a1_3 : a1_3 = (addc a1_2 a3 0).1 := rfl
  have e_cf_3 : cf_3 = (addc a1_2 a3 0).2 := rfl
  clear_value s_2 a1_3 cf_3
  have l_a1_3 : a1_3 + 2^64 * cf_3 = a1_2 + a3 + 0 := by
    rw [e_a1_3, e_cf_3]; exact addc_lin a1_2 a3 0
  have b_a1_3 : a1_3 < 2^64 := by rw [e_a1_3]; exact addc_value_lt a1_2 a3 0
  have b_cf_3 : cf_3 ≤ 1 := by rw [e_cf_3]; exact addc_carry_le_one a1_2 a3 0 b_a1_2 b_a3 (by decide)
  clear e_a1_3 e_cf_3
  -- test: test {b1}, 1
  extract_lets +onlyGivenNames test cf_4 zf at hr
  have e_test : test = bitAnd b1_1 1 := rfl
  have e_cf_4 : cf_4 = 0 := rfl
  have e_zf : zf = zeroFlag test := rfl
  clear_value test cf_4 zf
  have b_test : test < 2^64 := by rw [e_test]; exact bitAnd_lt _ _
  have b_cf_4 : cf_4 ≤ 1 := by rw [e_cf_4]; decide
  have b_zf : zf ≤ 1 := by rw [e_zf]; exact zeroFlag_le_one _
  -- a0_3: cmovz {a0}, {b1}
  extract_lets +onlyGivenNames a0_3 at hr
  have e_a0_3 : a0_3 = (if zf = 0 then a0_2 else b1_1) := rfl
  clear_value a0_3
  have b_a0_3 : a0_3 < 2^64 := by
    rw [e_a0_3]; split <;> first | exact b_a0_2 | exact b_b1_1
  -- b0_2: cmovz {b0}, {b2}
  extract_lets +onlyGivenNames b0_2 at hr
  have e_b0_2 : b0_2 = (if zf = 0 then b0_1 else b2_1) := rfl
  clear_value b0_2
  have b_b0_2 : b0_2 < 2^64 := by
    rw [e_b0_2]; split <;> first | exact b_b0_1 | exact b_b2_1
  -- a1_4: cmovz {a1}, {b3}
  extract_lets +onlyGivenNames a1_4 at hr
  have e_a1_4 : a1_4 = (if zf = 0 then a1_3 else b3_1) := rfl
  clear_value a1_4
  have b_a1_4 : a1_4 < 2^64 := by
    rw [e_a1_4]; split <;> first | exact b_a1_3 | exact b_b3_1
  -- a2_2: cmovz {a2}, {t}
  extract_lets +onlyGivenNames a2_2 at hr
  have e_a2_2 : a2_2 = (if zf = 0 then a2_1 else t) := rfl
  clear_value a2_2
  have b_a2_2 : a2_2 < 2^64 := by
    rw [e_a2_2]; split <;> first | exact b_a2_1 | exact b_t
  -- a0_4: shr {a0}, 1
  extract_lets +onlyGivenNames a0_4 at hr
  have e_a0_4 : a0_4 = a0_3 / 2^1 := rfl
  clear_value a0_4
  have b_a0_4 : a0_4 < 2^63 := by
    rw [e_a0_4]; exact Nat.div_lt_of_lt_mul (lt_of_lt_of_eq b_a0_3 (by norm_num))
  -- a2_3: add {a2}, {a2}
  extract_lets +onlyGivenNames s_3 a2_3 cf_5 at hr
  have e_a2_3 : a2_3 = (addc a2_2 a2_2 0).1 := rfl
  have e_cf_5 : cf_5 = (addc a2_2 a2_2 0).2 := rfl
  clear_value s_3 a2_3 cf_5
  have l_a2_3 : a2_3 + 2^64 * cf_5 = a2_2 + a2_2 + 0 := by
    rw [e_a2_3, e_cf_5]; exact addc_lin a2_2 a2_2 0
  have b_a2_3 : a2_3 < 2^64 := by rw [e_a2_3]; exact addc_value_lt a2_2 a2_2 0
  have b_cf_5 : cf_5 ≤ 1 := by rw [e_cf_5]; exact addc_carry_le_one a2_2 a2_2 0 b_a2_2 b_a2_2 (by decide)
  clear e_a2_3 e_cf_5
  -- a2_4: sub {a2}, {a3}
  extract_lets +onlyGivenNames s_4 a2_4 cf_6 at hr
  have e_a2_4 : a2_4 = (sbb a2_3 a3 0).1 := rfl
  have e_cf_6 : cf_6 = (sbb a2_3 a3 0).2 := rfl
  clear_value s_4 a2_4 cf_6
  have l_a2_4 : a2_4 + a3 + 0 = a2_3 + 2^64 * cf_6 := by
    rw [e_a2_4, e_cf_6]; exact sbb_lin a2_3 a3 0 b_a2_3 b_a3 (by decide)
  have b_a2_4 : a2_4 < 2^64 := by rw [e_a2_4]; exact sbb_value_lt a2_3 a3 0
  have b_cf_6 : cf_6 ≤ 1 := by rw [e_cf_6]; exact sbb_borrow_le_one a2_3 a3 0
  clear e_a2_4 e_cf_6
  subst hr
  -- BEGIN divsteps31Round conclusion
  rcases hstate with ⟨hsa, hsb⟩
  rcases hrows with ⟨hrow0, hrow1⟩
  have ha : a0 = abstract.a := e_a0.trans hsa
  have hb : b0 = abstract.b := e_b0.trans hsb
  have hrow0' : PackedRowRep a1 abstract.matrix.row0 := by simpa [e_a1] using hrow0
  have hrow1' : PackedRowRep a2 abstract.matrix.row1 := by simpa [e_a2] using hrow1
  have hbias' : a3 = packedRowBias := e_a3.trans hbias
  have hbiasRep : SignedWordRep a3 packedRowBias := by
    refine ⟨b_a3, ?_⟩
    rw [hbias']
    simp
  have hbounded : (⟨a0_4, a1_4, a2_4, a3, b0_2, b1_1, b2_1, b3_1, t⟩ :
      Divsteps31State).Bounded :=
    ⟨b_a0_4.trans (by norm_num), b_a1_4, b_a2_4, b_a3, b_b0_2,
      b_b1_1, b_b2_1, b_b3_1, b_t⟩
  have hcf : cf = 1 ↔ a0 < b0 := by
    rw [e_cf]
    simpa using sbb_borrow_iff a0 b0 0 b_a0 b_b0 (by decide)
  unfold approxStep
  split_ifs with heven hle
  · have hzf : zf = 1 := by
      rw [e_zf, e_test, e_b1_1]
      exact (zeroFlag_bitAnd_one_eq_one_iff b_a0).2 (by simpa [ha] using heven)
    have ha03 : a0_3 = a0 := by simp [e_a0_3, hzf, e_b1_1]
    have hb02 : b0_2 = b0 := by simp [e_b0_2, hzf, e_b2_1]
    have ha14 : a1_4 = a1 := by simp [e_a1_4, hzf, e_b3_1]
    have ha22 : a2_2 = a2 := by simp [e_a2_2, hzf, e_t]
    have hdoubleLin : a2_3 + 2^64 * cf_5 = a2 + a2 := by simpa [ha22] using l_a2_3
    have hdoubled : SignedWordRep a2_3
        (2 * ((packedRowBias : Int) + abstract.matrix.row1.left +
          (2^32 : Int) * abstract.matrix.row1.right)) :=
      signedWordRep_double b_a2_3 hdoubleLin hrow1'
    refine ⟨hbounded, ?_, ?_, ?_, ?_, hbias', hodd⟩
    · simp [e_a0_4, ha03, ha]
    · simp [hb02, hb]
    · simpa [ha14] using hrow0'
    · exact packedRowRep_double hdoubled hbiasRep b_a2_4 (by omega)
  · have hnotEven : ¬ Even a0 := by simpa [ha] using heven
    have hzf : zf = 0 := by
      rw [e_zf, e_test, e_b1_1]
      exact (zeroFlag_bitAnd_one_eq_zero_iff b_a0).2 hnotEven
    have hge : b0 ≤ a0 := by simpa [ha, hb] using hle
    have hcf0 : cf = 0 := by
      by_contra hn
      have : cf = 1 := by omega
      exact (Nat.not_lt_of_ge hge) (hcf.mp this)
    have ha01 : a0_1 = a0 := by simp [e_a0_1, hcf0]
    have hb01 : b0_1 = b0 := by simp [e_b0_1, hcf0]
    have ha11 : a1_1 = a1 := by simp [e_a1_1, hcf0]
    have ha21 : a2_1 = a2 := by simp [e_a2_1, hcf0]
    have ha02 : a0_2 = a0 - b0 := by omega
    have ha03 : a0_3 = a0 - b0 := by simp [e_a0_3, hzf, ha02]
    have hb02 : b0_2 = b0 := by simp [e_b0_2, hzf, hb01]
    have hsubLin : a1_2 + a2 = a1 + 2^64 * cf_2 := by
      simpa [ha11, ha21] using l_a1_2
    have hdiffBiased : SignedWordRep a1_2
        (((packedRowBias : Int) + abstract.matrix.row0.left +
          (2^32 : Int) * abstract.matrix.row0.right) -
         ((packedRowBias : Int) + abstract.matrix.row1.left +
          (2^32 : Int) * abstract.matrix.row1.right)) :=
      signedWordRep_sub b_a1_2 hsubLin hrow0' hrow1'
    have hdiff : SignedWordRep a1_2
        (abstract.matrix.row0.left - abstract.matrix.row1.left +
          (2^32 : Int) * (abstract.matrix.row0.right - abstract.matrix.row1.right)) := by
      convert hdiffBiased using 1
      all_goals ring
    have ha13 : SignedWordRep a1_3
        ((packedRowBias : Int) + (abstract.matrix.row0.left - abstract.matrix.row1.left) +
          (2^32 : Int) * (abstract.matrix.row0.right - abstract.matrix.row1.right)) := by
      have h := signedWordRep_add b_a1_3 (by omega) hdiff hbiasRep
      convert h using 1
      all_goals ring
    have ha14 : a1_4 = a1_3 := by simp [e_a1_4, hzf]
    have ha22 : a2_2 = a2 := by simp [e_a2_2, hzf, ha21]
    have hdoubleLin : a2_3 + 2^64 * cf_5 = a2 + a2 := by simpa [ha22] using l_a2_3
    have hdoubled : SignedWordRep a2_3
        (2 * ((packedRowBias : Int) + abstract.matrix.row1.left +
          (2^32 : Int) * abstract.matrix.row1.right)) :=
      signedWordRep_double b_a2_3 hdoubleLin hrow1'
    refine ⟨hbounded, ?_, ?_, ?_, ?_, hbias', hodd⟩
    · simp [e_a0_4, ha03, ha, hb]
    · simp [hb02, hb]
    · rw [ha14]
      simpa only [PackedRowRep, SignedRow.sub] using ha13
    · exact packedRowRep_double hdoubled hbiasRep b_a2_4 (by omega)
  · have hnotEven : ¬ Even a0 := by simpa [ha] using heven
    have hzf : zf = 0 := by
      rw [e_zf, e_test, e_b1_1]
      exact (zeroFlag_bitAnd_one_eq_zero_iff b_a0).2 hnotEven
    have hlt : a0 < b0 := by simpa [ha, hb] using Nat.lt_of_not_ge hle
    have hcf1 : cf = 1 := hcf.mpr hlt
    have ha01 : a0_1 = b0 := by simp [e_a0_1, hcf1]
    have hb01 : b0_1 = a0 := by simp [e_b0_1, hcf1, e_b1_1]
    have ha11 : a1_1 = a2 := by simp [e_a1_1, hcf1]
    have ha21 : a2_1 = a1 := by simp [e_a2_1, hcf1, e_b3_1]
    have ha02 : a0_2 = b0 - a0 := by omega
    have ha03 : a0_3 = b0 - a0 := by simp [e_a0_3, hzf, ha02]
    have hb02 : b0_2 = a0 := by simp [e_b0_2, hzf, hb01]
    have hsubLin : a1_2 + a1 = a2 + 2^64 * cf_2 := by
      simpa [ha11, ha21] using l_a1_2
    have hdiffBiased : SignedWordRep a1_2
        (((packedRowBias : Int) + abstract.matrix.row1.left +
          (2^32 : Int) * abstract.matrix.row1.right) -
         ((packedRowBias : Int) + abstract.matrix.row0.left +
          (2^32 : Int) * abstract.matrix.row0.right)) :=
      signedWordRep_sub b_a1_2 hsubLin hrow1' hrow0'
    have hdiff : SignedWordRep a1_2
        (abstract.matrix.row1.left - abstract.matrix.row0.left +
          (2^32 : Int) * (abstract.matrix.row1.right - abstract.matrix.row0.right)) := by
      convert hdiffBiased using 1
      all_goals ring
    have ha13 : SignedWordRep a1_3
        ((packedRowBias : Int) + (abstract.matrix.row1.left - abstract.matrix.row0.left) +
          (2^32 : Int) * (abstract.matrix.row1.right - abstract.matrix.row0.right)) := by
      have h := signedWordRep_add b_a1_3 (by omega) hdiff hbiasRep
      convert h using 1
      all_goals ring
    have ha14 : a1_4 = a1_3 := by simp [e_a1_4, hzf]
    have ha22 : a2_2 = a1 := by simp [e_a2_2, hzf, ha21]
    have hdoubleLin : a2_3 + 2^64 * cf_5 = a1 + a1 := by simpa [ha22] using l_a2_3
    have hdoubled : SignedWordRep a2_3
        (2 * ((packedRowBias : Int) + abstract.matrix.row0.left +
          (2^32 : Int) * abstract.matrix.row0.right)) :=
      signedWordRep_double b_a2_3 hdoubleLin hrow0'
    refine ⟨hbounded, ?_, ?_, ?_, ?_, hbias', ?_⟩
    · simp [e_a0_4, ha03, ha, hb]
    · simp [hb02, ha]
    · rw [ha14]
      simpa only [PackedRowRep, SignedRow.sub] using ha13
    · exact packedRowRep_double hdoubled hbiasRep b_a2_4 (by omega)
    · exact Nat.not_even_iff_odd.mp (by simpa [ha] using hnotEven)
  -- END divsteps31Round conclusion

end PastaAsm.X86_64
