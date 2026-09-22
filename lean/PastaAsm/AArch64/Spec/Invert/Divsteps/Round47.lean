/-
Copyright Supranational LLC (the routines, transcribed from Semolina v0.1.4).
Copyright (c) 2026 the pasta-asm contributors (the transcription and the proofs).
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.AArch64.Spec.Invert.Divsteps.Core
import PastaAsm.Spec.Invert.Convergence

namespace PastaAsm.AArch64

open Spec.Invert Spec.Invert.Convergence

-- BEGIN divsteps47Round_spec statement
/-- One mechanically factored final-loop operation is the shared exact short-loop operation.
The state values are exact naturals; the coefficient words represent the resulting signed rows
modulo `2^64`, and every output remains a bounded AArch64 register value. -/
theorem divsteps47Round_spec (acc : Divsteps47State) (m : SignedMatrix)
    (hacc : acc.Bounded) (hrep : acc.Represents m) (hodd : Odd acc.b) :
    ∀ out, out = divsteps47Round acc →
      let next := approxStep ⟨acc.a, acc.b, m⟩
      out.Bounded ∧ out.a = next.a ∧ out.b = next.b ∧
        out.Represents next.matrix ∧ Odd out.b ∧ CoeffStep m next.matrix := by
  intro out hr
-- END divsteps47Round_spec statement
  -- generated skeleton for `divsteps47Round`: do not edit between the annotations
  unfold divsteps47Round at hr
  lift_lets -merge at hr
  -- a: loop state argument
  extract_lets -merge +onlyGivenNames a at hr
  have e_a : a = acc.a := rfl
  clear_value a
  have b_a : a < 2^64 := by rw [e_a]; exact hacc.1
  -- cnt: loop state argument
  extract_lets -merge +onlyGivenNames cnt at hr
  have e_cnt : cnt = acc.cnt := rfl
  clear_value cnt
  have b_cnt : cnt < 2^64 := by rw [e_cnt]; exact hacc.2.1
  -- b: loop state argument
  extract_lets -merge +onlyGivenNames b at hr
  have e_b : b = acc.b := rfl
  clear_value b
  have b_b : b < 2^64 := by rw [e_b]; exact hacc.2.2.1
  -- f0: loop state argument
  extract_lets -merge +onlyGivenNames f0 at hr
  have e_f0 : f0 = acc.f0 := rfl
  clear_value f0
  have b_f0 : f0 < 2^64 := by rw [e_f0]; exact hacc.2.2.2.1
  -- g0: loop state argument
  extract_lets -merge +onlyGivenNames g0 at hr
  have e_g0 : g0 = acc.g0 := rfl
  clear_value g0
  have b_g0 : g0 < 2^64 := by rw [e_g0]; exact hacc.2.2.2.2.1
  -- f1: loop state argument
  extract_lets -merge +onlyGivenNames f1 at hr
  have e_f1 : f1 = acc.f1 := rfl
  clear_value f1
  have b_f1 : f1 < 2^64 := by rw [e_f1]; exact hacc.2.2.2.2.2.1
  -- g1: loop state argument
  extract_lets -merge +onlyGivenNames g1 at hr
  have e_g1 : g1 = acc.g1 := rfl
  clear_value g1
  have b_g1 : g1 < 2^64 := by rw [e_g1]; exact hacc.2.2.2.2.2.2
  -- odd: sbfx odd,a,#0,#1
  extract_lets -merge +onlyGivenNames odd at hr
  have e_odd : odd = sbfx a 0 1 := rfl
  clear_value odd
  have b_odd : odd < 2^64 := by rw [e_odd]; exact sbfx_lt _ _ _
  -- cnt_1: sub cnt,cnt,#1
  extract_lets -merge +onlyGivenNames cnt_1 at hr
  have e_cnt_1 : cnt_1 = sub cnt 1 := rfl
  clear_value cnt_1
  have b_cnt_1 : cnt_1 < 2^64 := by rw [e_cnt_1]; exact sub_lt _ _
  -- t0: and t0,b,odd
  extract_lets -merge +onlyGivenNames t0 at hr
  have e_t0 : t0 = bitAnd b odd := rfl
  clear_value t0
  have b_t0 : t0 < 2^64 := by rw [e_t0]; exact bitAnd_lt _ _
  -- t1: sub t1,b,a
  extract_lets -merge +onlyGivenNames t1 at hr
  have e_t1 : t1 = sub b a := rfl
  clear_value t1
  have b_t1 : t1 < 2^64 := by rw [e_t1]; exact sub_lt _ _
  -- t2: subs t2,a,t0
  extract_lets -merge +onlyGivenNames s t2 c at hr
  have e_t2 : t2 = (a + 2^64 - t0 - (1 - 1)) % 2^64 := rfl
  have e_c : c = (a + 2^64 - t0 - (1 - 1)) / 2^64 := rfl
  clear_value s t2 c
  have l_t2 : t2 + 2^64 * c + t0 + 1 = a + 2^64 + 1 := by
    rw [e_t2, e_c]; exact subc_lin a t0 1 b_t0 (by decide)
  have b_t2 : t2 < 2^64 := by rw [e_t2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have b_c : c ≤ 1 := by
    rw [e_c]; exact subc_carry_le_one a t0 1 b_a
  clear e_t2 e_c
  -- t0_1: mov t0,f0
  extract_lets -merge +onlyGivenNames t0_1 at hr
  have e_t0_1 : t0_1 = f0 := rfl
  clear_value t0_1
  have b_t0_1 : t0_1 < 2^64 := by rw [e_t0_1]; exact b_f0
  -- b_1: csel b,b,a,hs
  extract_lets -merge +onlyGivenNames b_1 at hr
  have e_b_1 : b_1 = (if c = 0 then a else b) := rfl
  clear_value b_1
  have b_b_1 : b_1 < 2^64 := by
    rw [e_b_1]; split <;> first | exact b_a | exact b_b
  -- a_1: csel a,t2,t1,hs
  extract_lets -merge +onlyGivenNames a_1 at hr
  have e_a_1 : a_1 = (if c = 0 then t1 else t2) := rfl
  clear_value a_1
  have b_a_1 : a_1 < 2^64 := by
    rw [e_a_1]; split <;> first | exact b_t1 | exact b_t2
  -- t1_1: mov t1,g0
  extract_lets -merge +onlyGivenNames t1_1 at hr
  have e_t1_1 : t1_1 = g0 := rfl
  clear_value t1_1
  have b_t1_1 : t1_1 < 2^64 := by rw [e_t1_1]; exact b_g0
  -- f0_1: csel f0,f0,f1,hs
  extract_lets -merge +onlyGivenNames f0_1 at hr
  have e_f0_1 : f0_1 = (if c = 0 then f1 else f0) := rfl
  clear_value f0_1
  have b_f0_1 : f0_1 < 2^64 := by
    rw [e_f0_1]; split <;> first | exact b_f1 | exact b_f0
  -- f1_1: csel f1,f1,t0,hs
  extract_lets -merge +onlyGivenNames f1_1 at hr
  have e_f1_1 : f1_1 = (if c = 0 then t0_1 else f1) := rfl
  clear_value f1_1
  have b_f1_1 : f1_1 < 2^64 := by
    rw [e_f1_1]; split <;> first | exact b_t0_1 | exact b_f1
  -- g0_1: csel g0,g0,g1,hs
  extract_lets -merge +onlyGivenNames g0_1 at hr
  have e_g0_1 : g0_1 = (if c = 0 then g1 else g0) := rfl
  clear_value g0_1
  have b_g0_1 : g0_1 < 2^64 := by
    rw [e_g0_1]; split <;> first | exact b_g1 | exact b_g0
  -- g1_1: csel g1,g1,t1,hs
  extract_lets -merge +onlyGivenNames g1_1 at hr
  have e_g1_1 : g1_1 = (if c = 0 then t1_1 else g1) := rfl
  clear_value g1_1
  have b_g1_1 : g1_1 < 2^64 := by
    rw [e_g1_1]; split <;> first | exact b_t1_1 | exact b_g1
  -- a_2: lsr a,a,#1
  extract_lets -merge +onlyGivenNames a_2 at hr
  have e_a_2 : a_2 = lsr a_1 1 := rfl
  clear_value a_2
  have b_a_2 : a_2 < 2^64 := by rw [e_a_2]; exact lt_of_le_of_lt (Nat.div_le_self _ _) b_a_1
  -- t0_2: and t0,f1,odd
  extract_lets -merge +onlyGivenNames t0_2 at hr
  have e_t0_2 : t0_2 = bitAnd f1_1 odd := rfl
  clear_value t0_2
  have b_t0_2 : t0_2 < 2^64 := by rw [e_t0_2]; exact bitAnd_lt _ _
  -- t1_2: and t1,g1,odd
  extract_lets -merge +onlyGivenNames t1_2 at hr
  have e_t1_2 : t1_2 = bitAnd g1_1 odd := rfl
  clear_value t1_2
  have b_t1_2 : t1_2 < 2^64 := by rw [e_t1_2]; exact bitAnd_lt _ _
  -- f1_2: add f1,f1,f1
  extract_lets -merge +onlyGivenNames f1_2 at hr
  have e_f1_2 : f1_2 = add f1_1 f1_1 := rfl
  clear_value f1_2
  have b_f1_2 : f1_2 < 2^64 := by rw [e_f1_2]; exact add_lt _ _
  -- g1_2: add g1,g1,g1
  extract_lets -merge +onlyGivenNames g1_2 at hr
  have e_g1_2 : g1_2 = add g1_1 g1_1 := rfl
  clear_value g1_2
  have b_g1_2 : g1_2 < 2^64 := by rw [e_g1_2]; exact add_lt _ _
  -- f0_2: sub f0,f0,t0
  extract_lets -merge +onlyGivenNames f0_2 at hr
  have e_f0_2 : f0_2 = sub f0_1 t0_2 := rfl
  clear_value f0_2
  have b_f0_2 : f0_2 < 2^64 := by rw [e_f0_2]; exact sub_lt _ _
  -- g0_2: sub g0,g0,t1
  extract_lets -merge +onlyGivenNames g0_2 at hr
  have e_g0_2 : g0_2 = sub g0_1 t1_2 := rfl
  clear_value g0_2
  have b_g0_2 : g0_2 < 2^64 := by rw [e_g0_2]; exact sub_lt _ _
  subst hr
  -- BEGIN conclusion
  let state : ApproxState := ⟨acc.a, acc.b, m⟩
  have hparity : odd = if Even a then 0 else 2^64 - 1 := by rw [e_odd, sbfx_bit]
  rcases hrep with ⟨hf0, hg0, hf1, hg1⟩
  have wf0 : WordRep f0 m.row0.left := by simpa [e_f0] using hf0
  have wg0 : WordRep g0 m.row0.right := by simpa [e_g0] using hg0
  have wf1 : WordRep f1 m.row1.left := by simpa [e_f1] using hf1
  have wg1 : WordRep g1 m.row1.right := by simpa [e_g1] using hg1
  unfold approxStep
  split_ifs with hea hab
  · have hodd0 : odd = 0 := by rw [hparity, if_pos (by simpa [e_a] using hea)]
    have ht0 : t0 = 0 := by rw [e_t0, hodd0, and_zero]
    have hc : c = 1 := by omega
    have ha1 : a_1 = a := by simp [e_a_1, hc]; omega
    have hb1 : b_1 = b := by simp [e_b_1, hc]
    have hf01 : f0_1 = f0 := by simp [e_f0_1, hc]
    have hg01 : g0_1 = g0 := by simp [e_g0_1, hc]
    have hf11 : f1_1 = f1 := by simp [e_f1_1, hc]
    have hg11 : g1_1 = g1 := by simp [e_g1_1, hc]
    have ht02 : t0_2 = 0 := by simp [e_t0_2, hodd0]
    have ht12 : t1_2 = 0 := by simp [e_t1_2, hodd0]
    refine ⟨⟨b_a_2, b_cnt_1, b_b_1, b_f0_2, b_g0_2, b_f1_2, b_g1_2⟩,
      ?_, ?_, ?_, ?_, CoeffStep.even _ _⟩
    · simp [e_a_2, ha1, lsr, e_a]
    · simp [hb1, e_b]
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [e_f0_2, hf01, ht02] using wordRep_sub b_f0 (by decide : 0 < 2^64) wf0 wordRep_zero
      · simpa [e_g0_2, hg01, ht12] using wordRep_sub b_g0 (by decide : 0 < 2^64) wg0 wordRep_zero
      · simpa [e_f1_2, hf11, SignedRow.double] using wordRep_double wf1
      · simpa [e_g1_2, hg11, SignedRow.double] using wordRep_double wg1
    · simpa [hb1, e_b] using hodd
  · have hodd1 : odd = 2^64 - 1 := by rw [hparity, if_neg (by simpa [e_a] using hea)]
    have ht0 : t0 = b := by rw [e_t0, hodd1, and_allOnes b b_b]
    have hba : b ≤ a := by simpa [state, e_a, e_b] using hab
    have hc1 : c = 1 := by omega
    have ha1 : a_1 = t2 := by simp [e_a_1, hc1]
    have hb1 : b_1 = b := by simp [e_b_1, hc1]
    have ht2eq : t2 = a - b := by omega
    have hf01 : f0_1 = f0 := by simp [e_f0_1, hc1]
    have hg01 : g0_1 = g0 := by simp [e_g0_1, hc1]
    have hf11 : f1_1 = f1 := by simp [e_f1_1, hc1]
    have hg11 : g1_1 = g1 := by simp [e_g1_1, hc1]
    have ht02 : t0_2 = f1 := by rw [e_t0_2, hf11, hodd1, and_allOnes f1 b_f1]
    have ht12 : t1_2 = g1 := by rw [e_t1_2, hg11, hodd1, and_allOnes g1 b_g1]
    refine ⟨⟨b_a_2, b_cnt_1, b_b_1, b_f0_2, b_g0_2, b_f1_2, b_g1_2⟩,
      ?_, ?_, ?_, ?_, CoeffStep.subtract _ _⟩
    · simp [e_a_2, ha1, ht2eq, lsr, e_a, e_b]
    · simp [hb1, e_b]
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [e_f0_2, hf01, ht02, SignedRow.sub] using wordRep_sub b_f0 b_f1 wf0 wf1
      · simpa [e_g0_2, hg01, ht12, SignedRow.sub] using wordRep_sub b_g0 b_g1 wg0 wg1
      · simpa [e_f1_2, hf11, SignedRow.double] using wordRep_double wf1
      · simpa [e_g1_2, hg11, SignedRow.double] using wordRep_double wg1
    · simpa [hb1, e_b] using hodd
  · have hodd1 : odd = 2^64 - 1 := by rw [hparity, if_neg (by simpa [e_a] using hea)]
    have ht0 : t0 = b := by rw [e_t0, hodd1, and_allOnes b b_b]
    have hba : ¬b ≤ a := by simpa [state, e_a, e_b] using hab
    have hc0 : c = 0 := by omega
    have ha1 : a_1 = t1 := by simp [e_a_1, hc0]
    have hb1 : b_1 = a := by simp [e_b_1, hc0]
    have ht1eq : t1 = b - a := by
      rw [e_t1, sub, subc]
      simp only [regMod]
      have harg : b + 2^64 - a - (1 - 1) = b + 2^64 - a := by omega
      rw [harg]
      have hge : 2^64 ≤ b + 2^64 - a := by omega
      rw [Nat.mod_eq_sub_mod hge]
      have hdiff : b + 2^64 - a - 2^64 = b - a := by omega
      rw [hdiff, Nat.mod_eq_of_lt (by omega : b - a < 2^64)]
    have hf01 : f0_1 = f1 := by simp [e_f0_1, hc0]
    have hg01 : g0_1 = g1 := by simp [e_g0_1, hc0]
    have hf11 : f1_1 = f0 := by simp [e_f1_1, hc0, e_t0_1]
    have hg11 : g1_1 = g0 := by simp [e_g1_1, hc0, e_t1_1]
    have ht02 : t0_2 = f0 := by rw [e_t0_2, hf11, hodd1, and_allOnes f0 b_f0]
    have ht12 : t1_2 = g0 := by rw [e_t1_2, hg11, hodd1, and_allOnes g0 b_g0]
    refine ⟨⟨b_a_2, b_cnt_1, b_b_1, b_f0_2, b_g0_2, b_f1_2, b_g1_2⟩,
      ?_, ?_, ?_, ?_, CoeffStep.swapSubtract _ _⟩
    · simp [e_a_2, ha1, ht1eq, lsr, e_a, e_b]
    · simp [hb1, e_a]
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [e_f0_2, hf01, ht02, SignedRow.sub] using wordRep_sub b_f1 b_f0 wf1 wf0
      · simpa [e_g0_2, hg01, ht12, SignedRow.sub] using wordRep_sub b_g1 b_g0 wg1 wg0
      · simpa [e_f1_2, hf11, SignedRow.double] using wordRep_double wf0
      · simpa [e_g1_2, hg11, SignedRow.double] using wordRep_double wg0
    · simpa [hb1, e_a] using (Nat.not_even_iff_odd.mp (by simpa [state] using hea))
  -- END conclusion

/-- Conventional forward iteration, convenient for the unrolled AArch64 wrapper. -/
def forwardSteps : Nat → ApproxState → ApproxState
  | 0, s => s
  | n + 1, s => approxStep (forwardSteps n s)

lemma approxSteps_succ_right (n : Nat) (s : ApproxState) :
    approxSteps (n + 1) s = approxStep (approxSteps n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [approxSteps, ih]
      rfl

lemma forwardSteps_eq_approxSteps (n : Nat) (s : ApproxState) :
    forwardSteps n s = approxSteps n s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [forwardSteps, ih, approxSteps_succ_right]

lemma approxStep_pair (s : ApproxState) :
    ((approxStep s).a, (approxStep s).b) = exactStep s.a s.b := by
  unfold approxStep exactStep
  split_ifs <;> rfl

lemma approxSteps_pair (n : Nat) (s : ApproxState) :
    ((approxSteps n s).a, (approxSteps n s).b) = exactSteps n (s.a, s.b) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [approxSteps, exactSteps]
      simpa only [approxStep_pair] using ih (approxStep s)

namespace Divsteps47State

/-- Concrete register state matched to one shared mathematical state. -/
def Matches (s : Divsteps47State) (abstract : ApproxState) : Prop :=
  s.Bounded ∧ s.a = abstract.a ∧ s.b = abstract.b ∧
    s.Represents abstract.matrix ∧ Odd s.b

lemma Matches.next {s : Divsteps47State} {abstract : ApproxState}
    (h : s.Matches abstract) : (divsteps47Round s).Matches (approxStep abstract) := by
  rcases h with ⟨hs, ha, hb, hm, hodd⟩
  rcases divsteps47Round_spec s abstract.matrix hs hm hodd (divsteps47Round s) rfl with
    ⟨hs', ha', hb', hm', hodd', _⟩
  exact ⟨hs', by simpa [ha, hb] using ha', by simpa [ha, hb] using hb',
    by simpa [ha, hb] using hm', hodd'⟩

end Divsteps47State

end PastaAsm.AArch64
