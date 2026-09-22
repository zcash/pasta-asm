/-
Copyright Supranational LLC (the routines, transcribed from Semolina v0.1.4).
Copyright (c) 2026 the pasta-asm contributors (the transcription and the proofs).
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.AArch64.Spec.Invert.Divsteps.Round47

namespace PastaAsm.AArch64

open Spec.Invert Spec.Invert.Convergence

/-- The per-lane bias used by the packed AArch64 approximation coefficients. -/
def packedLaneBias : Nat := 2^31 - 1

/-- Two copies of `packedLaneBias`, one in each 32-bit lane. -/
def packedRowBias : Nat := packedLaneBias + 2^32 * packedLaneBias

/-- The signed row encoded by one biased pair of 32-bit lanes. -/
def packedRowValue (r : SignedRow) : Int :=
  (packedRowBias : Int) + r.left + (2^32 : Int) * r.right

/-- A packed AArch64 coefficient word represents a shared signed row. -/
def PackedRowRep (w : Nat) (r : SignedRow) : Prop := WordRep w (packedRowValue r)

lemma packedRowValue_double (r : SignedRow) :
    2 * packedRowValue r - packedRowBias = packedRowValue r.double := by
  simp only [packedRowValue, SignedRow.double]
  ring

lemma packedRowValue_sub (r s : SignedRow) :
    packedRowValue r - packedRowValue s + packedRowBias = packedRowValue (r.sub s) := by
  simp only [packedRowValue, SignedRow.sub]
  ring

namespace Divsteps31State

/-- All carried values are valid AArch64 register contents. -/
def Bounded (s : Divsteps31State) : Prop :=
  s.a3 < 2^64 ∧ s.cnt < 2^64 ∧ s.b3 < 2^64 ∧ s.fg1 < 2^64 ∧ s.fg0 < 2^64

/-- One concrete packed loop state matches one shared approximation state. -/
def Matches (s : Divsteps31State) (abstract : ApproxState) : Prop :=
  s.Bounded ∧ s.a3 = abstract.a ∧ s.b3 = abstract.b ∧
    PackedRowRep s.fg0 abstract.matrix.row0 ∧
    PackedRowRep s.fg1 abstract.matrix.row1 ∧ Odd s.b3

end Divsteps31State

-- BEGIN divsteps31Round_spec statement
/-- One mechanically factored packed iteration performs one actual approximation-controlled
operation and the same signed row recurrence in the two biased 32-bit lanes. -/
theorem divsteps31Round_spec (bias : Nat) (acc : Divsteps31State) (abstract : ApproxState)
    (hbias : bias < 2^64) (hbiaseq : bias = packedRowBias)
    (hacc : acc.Bounded) (hstate : acc.a3 = abstract.a ∧ acc.b3 = abstract.b)
    (hrows : PackedRowRep acc.fg0 abstract.matrix.row0 ∧
      PackedRowRep acc.fg1 abstract.matrix.row1) (hodd : Odd acc.b3) :
    ∀ out, out = divsteps31Round bias acc →
      out.Bounded ∧ out.a3 = (approxStep abstract).a ∧
        out.b3 = (approxStep abstract).b ∧
        PackedRowRep out.fg0 (approxStep abstract).matrix.row0 ∧
        PackedRowRep out.fg1 (approxStep abstract).matrix.row1 ∧ Odd out.b3 := by
  intro out hr
-- END divsteps31Round_spec statement
  -- generated skeleton for `divsteps31Round`: do not edit between the annotations
  unfold divsteps31Round at hr
  lift_lets -merge at hr
  -- bias': invariant argument
  extract_lets -merge +onlyGivenNames bias' at hr
  have e_bias' : bias' = bias := rfl
  clear_value bias'
  have b_bias' : bias' < 2^64 := by rw [e_bias']; exact hbias
  -- a3: loop state argument
  extract_lets -merge +onlyGivenNames a3 at hr
  have e_a3 : a3 = acc.a3 := rfl
  clear_value a3
  have b_a3 : a3 < 2^64 := by rw [e_a3]; exact hacc.1
  -- cnt: loop state argument
  extract_lets -merge +onlyGivenNames cnt at hr
  have e_cnt : cnt = acc.cnt := rfl
  clear_value cnt
  have b_cnt : cnt < 2^64 := by rw [e_cnt]; exact hacc.2.1
  -- b3: loop state argument
  extract_lets -merge +onlyGivenNames b3 at hr
  have e_b3 : b3 = acc.b3 := rfl
  clear_value b3
  have b_b3 : b3 < 2^64 := by rw [e_b3]; exact hacc.2.2.1
  -- fg1: loop state argument
  extract_lets -merge +onlyGivenNames fg1 at hr
  have e_fg1 : fg1 = acc.fg1 := rfl
  clear_value fg1
  have b_fg1 : fg1 < 2^64 := by rw [e_fg1]; exact hacc.2.2.2.1
  -- fg0: loop state argument
  extract_lets -merge +onlyGivenNames fg0 at hr
  have e_fg0 : fg0 = acc.fg0 := rfl
  clear_value fg0
  have b_fg0 : fg0 < 2^64 := by rw [e_fg0]; exact hacc.2.2.2.2
  -- t3: sbfx t3,a3,#0,#1
  extract_lets -merge +onlyGivenNames t3 at hr
  have e_t3 : t3 = sbfx a3 0 1 := rfl
  clear_value t3
  have b_t3 : t3 < 2^64 := by rw [e_t3]; exact sbfx_lt _ _ _
  -- cnt_1: sub cnt,cnt,#1
  extract_lets -merge +onlyGivenNames cnt_1 at hr
  have e_cnt_1 : cnt_1 = sub cnt 1 := rfl
  clear_value cnt_1
  have b_cnt_1 : cnt_1 < 2^64 := by rw [e_cnt_1]; exact sub_lt _ _
  -- t0: and t0,b3,t3
  extract_lets -merge +onlyGivenNames t0 at hr
  have e_t0 : t0 = bitAnd b3 t3 := rfl
  clear_value t0
  have b_t0 : t0 < 2^64 := by rw [e_t0]; exact bitAnd_lt _ _
  -- t1: sub t1,b3,a3
  extract_lets -merge +onlyGivenNames t1 at hr
  have e_t1 : t1 = sub b3 a3 := rfl
  clear_value t1
  have b_t1 : t1 < 2^64 := by rw [e_t1]; exact sub_lt _ _
  -- t2: subs t2,a3,t0
  extract_lets -merge +onlyGivenNames s t2 c at hr
  have e_t2 : t2 = (a3 + 2^64 - t0 - (1 - 1)) % 2^64 := rfl
  have e_c : c = (a3 + 2^64 - t0 - (1 - 1)) / 2^64 := rfl
  clear_value s t2 c
  have l_t2 : t2 + 2^64 * c + t0 + 1 = a3 + 2^64 + 1 := by
    rw [e_t2, e_c]; exact subc_lin a3 t0 1 b_t0 (by decide)
  have b_t2 : t2 < 2^64 := by rw [e_t2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c : c ≤ 1 := by
    rw [e_c]; exact subc_carry_le_one a3 t0 1 b_a3
  clear e_t2 e_c
  -- t0_1: mov t0,fg1
  extract_lets -merge +onlyGivenNames t0_1 at hr
  have e_t0_1 : t0_1 = fg1 := rfl
  clear_value t0_1
  have b_t0_1 : t0_1 < 2^64 := by rw [e_t0_1]; exact b_fg1
  -- b3_1: csel b3,b3,a3,hs
  extract_lets -merge +onlyGivenNames b3_1 at hr
  have e_b3_1 : b3_1 = (if c = 0 then a3 else b3) := rfl
  clear_value b3_1
  have b_b3_1 : b3_1 < 2^64 := by
    rw [e_b3_1]; split <;> first | exact b_a3 | exact b_b3
  -- a3_1: csel a3,t2,t1,hs
  extract_lets -merge +onlyGivenNames a3_1 at hr
  have e_a3_1 : a3_1 = (if c = 0 then t1 else t2) := rfl
  clear_value a3_1
  have b_a3_1 : a3_1 < 2^64 := by
    rw [e_a3_1]; split <;> first | exact b_t1 | exact b_t2
  -- fg1_1: csel fg1,fg1,fg0,hs
  extract_lets -merge +onlyGivenNames fg1_1 at hr
  have e_fg1_1 : fg1_1 = (if c = 0 then fg0 else fg1) := rfl
  clear_value fg1_1
  have b_fg1_1 : fg1_1 < 2^64 := by
    rw [e_fg1_1]; split <;> first | exact b_fg0 | exact b_fg1
  -- fg0_1: csel fg0,fg0,t0,hs
  extract_lets -merge +onlyGivenNames fg0_1 at hr
  have e_fg0_1 : fg0_1 = (if c = 0 then t0_1 else fg0) := rfl
  clear_value fg0_1
  have b_fg0_1 : fg0_1 < 2^64 := by
    rw [e_fg0_1]; split <;> first | exact b_t0_1 | exact b_fg0
  -- a3_2: lsr a3,a3,#1
  extract_lets -merge +onlyGivenNames a3_2 at hr
  have e_a3_2 : a3_2 = lsr a3_1 1 := rfl
  clear_value a3_2
  have b_a3_2 : a3_2 < 2^64 := by rw [e_a3_2]; exact lt_of_le_of_lt (Nat.div_le_self _ _) b_a3_1
  -- t0_2: and t0,fg1,t3
  extract_lets -merge +onlyGivenNames t0_2 at hr
  have e_t0_2 : t0_2 = bitAnd fg1_1 t3 := rfl
  clear_value t0_2
  have b_t0_2 : t0_2 < 2^64 := by rw [e_t0_2]; exact bitAnd_lt _ _
  -- t1_1: and t1,bias,t3
  extract_lets -merge +onlyGivenNames t1_1 at hr
  have e_t1_1 : t1_1 = bitAnd bias' t3 := rfl
  clear_value t1_1
  have b_t1_1 : t1_1 < 2^64 := by rw [e_t1_1]; exact bitAnd_lt _ _
  -- fg0_2: sub fg0,fg0,t0
  extract_lets -merge +onlyGivenNames fg0_2 at hr
  have e_fg0_2 : fg0_2 = sub fg0_1 t0_2 := rfl
  clear_value fg0_2
  have b_fg0_2 : fg0_2 < 2^64 := by rw [e_fg0_2]; exact sub_lt _ _
  -- fg1_2: add fg1,fg1,fg1
  extract_lets -merge +onlyGivenNames fg1_2 at hr
  have e_fg1_2 : fg1_2 = add fg1_1 fg1_1 := rfl
  clear_value fg1_2
  have b_fg1_2 : fg1_2 < 2^64 := by rw [e_fg1_2]; exact add_lt _ _
  -- fg0_3: add fg0,fg0,t1
  extract_lets -merge +onlyGivenNames fg0_3 at hr
  have e_fg0_3 : fg0_3 = add fg0_2 t1_1 := rfl
  clear_value fg0_3
  have b_fg0_3 : fg0_3 < 2^64 := by rw [e_fg0_3]; exact add_lt _ _
  -- fg1_3: sub fg1,fg1,bias
  extract_lets -merge +onlyGivenNames fg1_3 at hr
  have e_fg1_3 : fg1_3 = sub fg1_2 bias' := rfl
  clear_value fg1_3
  have b_fg1_3 : fg1_3 < 2^64 := by rw [e_fg1_3]; exact sub_lt _ _
  subst hr
  -- BEGIN divsteps31Round conclusion
  rcases hstate with ⟨hstateA, hstateB⟩
  rcases hrows with ⟨hrow0, hrow1⟩
  have ha : a3 = abstract.a := e_a3.trans hstateA
  have hb : b3 = abstract.b := e_b3.trans hstateB
  have wrow0 : WordRep fg0 (packedRowValue abstract.matrix.row0) := by
    simpa [PackedRowRep, e_fg0] using hrow0
  have wrow1 : WordRep fg1 (packedRowValue abstract.matrix.row1) := by
    simpa [PackedRowRep, e_fg1] using hrow1
  have wbias : WordRep bias' (packedRowBias : Int) := by
    simp [WordRep, e_bias', hbiaseq]
  have hparity : t3 = if Even a3 then 0 else 2^64 - 1 := by rw [e_t3, sbfx_bit]
  unfold approxStep
  split_ifs with hea hab
  · have ht3 : t3 = 0 := by rw [hparity, if_pos (by simpa [ha] using hea)]
    have ht0 : t0 = 0 := by rw [e_t0, ht3, and_zero]
    have hc : c = 1 := by omega
    have ha1 : a3_1 = a3 := by simp [e_a3_1, hc]; omega
    have hb1 : b3_1 = b3 := by simp [e_b3_1, hc]
    have hfg11 : fg1_1 = fg1 := by simp [e_fg1_1, hc]
    have hfg01 : fg0_1 = fg0 := by simp [e_fg0_1, hc]
    have ht02 : t0_2 = 0 := by simp [e_t0_2, ht3]
    have ht11 : t1_1 = 0 := by simp [e_t1_1, ht3]
    have wfg02 : WordRep fg0_2 (packedRowValue abstract.matrix.row0) := by
      simpa [e_fg0_2, hfg01, ht02] using
        wordRep_sub b_fg0 (by decide : 0 < 2^64) wrow0 wordRep_zero
    have wfg03 : WordRep fg0_3 (packedRowValue abstract.matrix.row0) := by
      simpa [e_fg0_3, ht11] using wordRep_add wfg02 wordRep_zero
    have wfg12 : WordRep fg1_2 (2 * packedRowValue abstract.matrix.row1) := by
      simpa [e_fg1_2, hfg11] using wordRep_double wrow1
    have wfg13 : WordRep fg1_3 (packedRowValue abstract.matrix.row1.double) := by
      have h := wordRep_sub b_fg1_2 b_bias' wfg12 wbias
      rw [e_fg1_3]
      simpa only [packedRowValue_double] using h
    refine ⟨⟨b_a3_2, b_cnt_1, b_b3_1, b_fg1_3, b_fg0_3⟩, ?_, ?_, ?_, ?_, ?_⟩
    · simp [e_a3_2, ha1, lsr, ha]
    · simp [hb1, hb]
    · simpa [PackedRowRep] using wfg03
    · simpa [PackedRowRep] using wfg13
    · simpa [hb1, e_b3] using hodd
  · have ht3 : t3 = 2^64 - 1 := by rw [hparity, if_neg (by simpa [ha] using hea)]
    have ht0 : t0 = b3 := by rw [e_t0, ht3, and_allOnes b3 b_b3]
    have hba : b3 ≤ a3 := by simpa [ha, hb] using hab
    have hc : c = 1 := by omega
    have ha1 : a3_1 = t2 := by simp [e_a3_1, hc]
    have hb1 : b3_1 = b3 := by simp [e_b3_1, hc]
    have ht2eq : t2 = a3 - b3 := by omega
    have hfg11 : fg1_1 = fg1 := by simp [e_fg1_1, hc]
    have hfg01 : fg0_1 = fg0 := by simp [e_fg0_1, hc]
    have ht02 : t0_2 = fg1 := by rw [e_t0_2, hfg11, ht3, and_allOnes fg1 b_fg1]
    have ht11 : t1_1 = bias' := by rw [e_t1_1, ht3, and_allOnes bias' b_bias']
    have wfg02 : WordRep fg0_2
        (packedRowValue abstract.matrix.row0 - packedRowValue abstract.matrix.row1) := by
      simpa [e_fg0_2, hfg01, ht02] using wordRep_sub b_fg0 b_fg1 wrow0 wrow1
    have wfg03 : WordRep fg0_3
        (packedRowValue (abstract.matrix.row0.sub abstract.matrix.row1)) := by
      have h := wordRep_add wfg02 wbias
      rw [e_fg0_3, ht11]
      simpa only [packedRowValue_sub] using h
    have wfg12 : WordRep fg1_2 (2 * packedRowValue abstract.matrix.row1) := by
      simpa [e_fg1_2, hfg11] using wordRep_double wrow1
    have wfg13 : WordRep fg1_3 (packedRowValue abstract.matrix.row1.double) := by
      have h := wordRep_sub b_fg1_2 b_bias' wfg12 wbias
      rw [e_fg1_3]
      simpa only [packedRowValue_double] using h
    refine ⟨⟨b_a3_2, b_cnt_1, b_b3_1, b_fg1_3, b_fg0_3⟩, ?_, ?_, ?_, ?_, ?_⟩
    · simp [e_a3_2, ha1, ht2eq, lsr, ha, hb]
    · simp [hb1, hb]
    · simpa [PackedRowRep] using wfg03
    · simpa [PackedRowRep] using wfg13
    · simpa [hb1, e_b3] using hodd
  · have ht3 : t3 = 2^64 - 1 := by rw [hparity, if_neg (by simpa [ha] using hea)]
    have ht0 : t0 = b3 := by rw [e_t0, ht3, and_allOnes b3 b_b3]
    have hba : ¬ b3 ≤ a3 := by simpa [ha, hb] using hab
    have hc : c = 0 := by omega
    have ha1 : a3_1 = t1 := by simp [e_a3_1, hc]
    have hb1 : b3_1 = a3 := by simp [e_b3_1, hc]
    have ht1eq : t1 = b3 - a3 := by
      rw [e_t1, sub, subc]
      simp only [regMod]
      have harg : b3 + 2^64 - a3 - (1 - 1) = b3 + 2^64 - a3 := by omega
      rw [harg]
      have hge : 2^64 ≤ b3 + 2^64 - a3 := by omega
      rw [Nat.mod_eq_sub_mod hge]
      have hdiff : b3 + 2^64 - a3 - 2^64 = b3 - a3 := by omega
      rw [hdiff, Nat.mod_eq_of_lt (by omega : b3 - a3 < 2^64)]
    have hfg11 : fg1_1 = fg0 := by simp [e_fg1_1, hc]
    have hfg01 : fg0_1 = fg1 := by simp [e_fg0_1, hc, e_t0_1]
    have ht02 : t0_2 = fg0 := by rw [e_t0_2, hfg11, ht3, and_allOnes fg0 b_fg0]
    have ht11 : t1_1 = bias' := by rw [e_t1_1, ht3, and_allOnes bias' b_bias']
    have wfg02 : WordRep fg0_2
        (packedRowValue abstract.matrix.row1 - packedRowValue abstract.matrix.row0) := by
      simpa [e_fg0_2, hfg01, ht02] using wordRep_sub b_fg1 b_fg0 wrow1 wrow0
    have wfg03 : WordRep fg0_3
        (packedRowValue (abstract.matrix.row1.sub abstract.matrix.row0)) := by
      have h := wordRep_add wfg02 wbias
      rw [e_fg0_3, ht11]
      simpa only [packedRowValue_sub] using h
    have wfg12 : WordRep fg1_2 (2 * packedRowValue abstract.matrix.row0) := by
      simpa [e_fg1_2, hfg11] using wordRep_double wrow0
    have wfg13 : WordRep fg1_3 (packedRowValue abstract.matrix.row0.double) := by
      have h := wordRep_sub b_fg1_2 b_bias' wfg12 wbias
      rw [e_fg1_3]
      simpa only [packedRowValue_double] using h
    refine ⟨⟨b_a3_2, b_cnt_1, b_b3_1, b_fg1_3, b_fg0_3⟩, ?_, ?_, ?_, ?_, ?_⟩
    · simp [e_a3_2, ha1, ht1eq, lsr, ha, hb]
    · simp [hb1, ha]
    · simpa [PackedRowRep] using wfg03
    · simpa [PackedRowRep] using wfg13
    · simpa [hb1, ha] using (Nat.not_even_iff_odd.mp (by simpa [ha] using hea))
  -- END divsteps31Round conclusion

lemma Divsteps31State.Matches.next {s : Divsteps31State} {abstract : ApproxState}
    (h : s.Matches abstract) :
    (divsteps31Round packedRowBias s).Matches (approxStep abstract) := by
  rcases h with ⟨hs, ha, hb, hrow0, hrow1, hodd⟩
  have hbias : packedRowBias < 2^64 := by decide
  rcases divsteps31Round_spec packedRowBias s abstract hbias rfl hs ⟨ha, hb⟩
      ⟨hrow0, hrow1⟩ hodd _ rfl with
    ⟨hs', ha', hb', hrow0', hrow1', hodd'⟩
  exact ⟨hs', ha', hb', hrow0', hrow1', hodd'⟩

end PastaAsm.AArch64
