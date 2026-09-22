/-
Copyright Supranational LLC (the routines, transcribed from Semolina v0.1.4).
Copyright (c) 2026 the pasta-asm contributors (the transcription and the proofs).
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.AArch64.Spec.Invert.Divsteps.Round47

namespace PastaAsm.AArch64

open Spec.Invert Spec.Invert.Convergence

-- BEGIN divsteps47 conclusion helper
private theorem finishDivsteps47
    (outF outG : Nat) (terminal : Divsteps47State) (final : ApproxState)
    (hterminal : terminal.Matches final)
    (eF : outF = terminal.f1) (eG : outG = terminal.g1)
    (hbounded : final.matrix.Bounded (2^47))
    (hcoeff : CoeffSteps 47 identityMatrix final.matrix) :
    WordRep outF final.matrix.row1.left ∧ WordRep outG final.matrix.row1.right ∧
      Odd final.b ∧ final.matrix.Bounded (2^47) ∧
      CoeffSteps 47 identityMatrix final.matrix := by
  rcases hterminal with ⟨_, _, hb, ⟨_, _, hf, hg⟩, hodd⟩
  have houtF : WordRep outF final.matrix.row1.left := by simpa only [eF] using hf
  have houtG : WordRep outG final.matrix.row1.right := by simpa only [eG] using hg
  have hfinalOdd : Odd final.b := by simpa only [hb] using hodd
  exact ⟨houtF, houtG, hfinalOdd, hbounded, hcoeff⟩
-- END divsteps47 conclusion helper

-- BEGIN divsteps47_spec statement
/-- The generated fixed wrapper performs all 47 exact final divsteps and returns the second
signed transition row modulo `2^64`, together with the shared row recurrence and bound. -/
theorem divsteps47_spec (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) (hodd : Odd b) :
    ∀ out, out = divsteps47 a b →
      let final := approxSteps 47 (ApproxState.initial a b)
      WordRep out.f1 final.matrix.row1.left ∧ WordRep out.g1 final.matrix.row1.right ∧
        Odd final.b ∧ final.matrix.Bounded (2^47) ∧
        CoeffSteps 47 identityMatrix final.matrix := by
  intro out hr
-- END divsteps47_spec statement
  -- generated skeleton for `divsteps47`: do not edit between the annotations
  unfold divsteps47 at hr
  lift_lets -merge at hr
  -- a': argument
  extract_lets -merge +onlyGivenNames a' at hr
  have e_a' : a' = a := rfl
  clear_value a'
  have b_a' : a' < 2^64 := by rw [e_a']; exact ha
  -- b': argument
  extract_lets -merge +onlyGivenNames b' at hr
  have e_b' : b' = b := rfl
  clear_value b'
  have b_b' : b' < 2^64 := by rw [e_b']; exact hb
  -- cnt: argument
  extract_lets -merge +onlyGivenNames cnt at hr
  have e_cnt : cnt = 47 := rfl
  clear_value cnt
  have b_cnt : cnt < 2^64 := by rw [e_cnt]; decide
  -- f0: argument
  extract_lets -merge +onlyGivenNames f0 at hr
  have e_f0 : f0 = 1 := rfl
  clear_value f0
  have b_f0 : f0 < 2^64 := by rw [e_f0]; decide
  -- g0: argument
  extract_lets -merge +onlyGivenNames g0 at hr
  have e_g0 : g0 = 0 := rfl
  clear_value g0
  have b_g0 : g0 < 2^64 := by rw [e_g0]; decide
  -- f1: argument
  extract_lets -merge +onlyGivenNames f1 at hr
  have e_f1 : f1 = 0 := rfl
  clear_value f1
  have b_f1 : f1 < 2^64 := by rw [e_f1]; decide
  -- g1: argument
  extract_lets -merge +onlyGivenNames g1 at hr
  have e_g1 : g1 = 1 := rfl
  clear_value g1
  have b_g1 : g1 < 2^64 := by rw [e_g1]; decide
  -- BEGIN initial invariant
  have hmatch0 : (⟨a', cnt, b', f0, g0, f1, g1⟩ : Divsteps47State).Matches
      (ApproxState.initial a b) := by
    refine ⟨⟨b_a', b_cnt, b_b', b_f0, b_g0, b_f1, b_g1⟩, ?_, ?_, ?_, ?_⟩
    · simp [ApproxState.initial, e_a']
    · simp [ApproxState.initial, e_b']
    · exact ⟨by simpa [e_f0, identityMatrix] using wordRep_one,
        by simpa [e_g0, identityMatrix] using wordRep_zero,
        by simpa [e_f1, identityMatrix] using wordRep_zero,
        by simpa [e_g1, identityMatrix] using wordRep_one⟩
    · simpa [e_b'] using hodd
  -- END initial invariant
  -- round1: loop iteration 1
  extract_lets -merge +onlyGivenNames round1 at hr
  have e_round1 : round1 = divsteps47Round ⟨a', cnt, b', f0, g0, f1, g1⟩ := rfl
  clear_value round1
  -- a_1: loop iteration 1 output
  extract_lets -merge +onlyGivenNames a_1 at hr
  have e_a_1 : a_1 = round1.a := rfl
  clear_value a_1
  -- cnt_1: loop iteration 1 output
  extract_lets -merge +onlyGivenNames cnt_1 at hr
  have e_cnt_1 : cnt_1 = round1.cnt := rfl
  clear_value cnt_1
  -- b_1: loop iteration 1 output
  extract_lets -merge +onlyGivenNames b_1 at hr
  have e_b_1 : b_1 = round1.b := rfl
  clear_value b_1
  -- f0_1: loop iteration 1 output
  extract_lets -merge +onlyGivenNames f0_1 at hr
  have e_f0_1 : f0_1 = round1.f0 := rfl
  clear_value f0_1
  -- g0_1: loop iteration 1 output
  extract_lets -merge +onlyGivenNames g0_1 at hr
  have e_g0_1 : g0_1 = round1.g0 := rfl
  clear_value g0_1
  -- f1_1: loop iteration 1 output
  extract_lets -merge +onlyGivenNames f1_1 at hr
  have e_f1_1 : f1_1 = round1.f1 := rfl
  clear_value f1_1
  -- g1_1: loop iteration 1 output
  extract_lets -merge +onlyGivenNames g1_1 at hr
  have e_g1_1 : g1_1 = round1.g1 := rfl
  clear_value g1_1
  -- round2: loop iteration 2
  extract_lets -merge +onlyGivenNames round2 at hr
  have e_round2 : round2 = divsteps47Round ⟨a_1, cnt_1, b_1, f0_1, g0_1, f1_1, g1_1⟩ := rfl
  clear_value round2
  -- a_2: loop iteration 2 output
  extract_lets -merge +onlyGivenNames a_2 at hr
  have e_a_2 : a_2 = round2.a := rfl
  clear_value a_2
  -- cnt_2: loop iteration 2 output
  extract_lets -merge +onlyGivenNames cnt_2 at hr
  have e_cnt_2 : cnt_2 = round2.cnt := rfl
  clear_value cnt_2
  -- b_2: loop iteration 2 output
  extract_lets -merge +onlyGivenNames b_2 at hr
  have e_b_2 : b_2 = round2.b := rfl
  clear_value b_2
  -- f0_2: loop iteration 2 output
  extract_lets -merge +onlyGivenNames f0_2 at hr
  have e_f0_2 : f0_2 = round2.f0 := rfl
  clear_value f0_2
  -- g0_2: loop iteration 2 output
  extract_lets -merge +onlyGivenNames g0_2 at hr
  have e_g0_2 : g0_2 = round2.g0 := rfl
  clear_value g0_2
  -- f1_2: loop iteration 2 output
  extract_lets -merge +onlyGivenNames f1_2 at hr
  have e_f1_2 : f1_2 = round2.f1 := rfl
  clear_value f1_2
  -- g1_2: loop iteration 2 output
  extract_lets -merge +onlyGivenNames g1_2 at hr
  have e_g1_2 : g1_2 = round2.g1 := rfl
  clear_value g1_2
  -- round3: loop iteration 3
  extract_lets -merge +onlyGivenNames round3 at hr
  have e_round3 : round3 = divsteps47Round ⟨a_2, cnt_2, b_2, f0_2, g0_2, f1_2, g1_2⟩ := rfl
  clear_value round3
  -- a_3: loop iteration 3 output
  extract_lets -merge +onlyGivenNames a_3 at hr
  have e_a_3 : a_3 = round3.a := rfl
  clear_value a_3
  -- cnt_3: loop iteration 3 output
  extract_lets -merge +onlyGivenNames cnt_3 at hr
  have e_cnt_3 : cnt_3 = round3.cnt := rfl
  clear_value cnt_3
  -- b_3: loop iteration 3 output
  extract_lets -merge +onlyGivenNames b_3 at hr
  have e_b_3 : b_3 = round3.b := rfl
  clear_value b_3
  -- f0_3: loop iteration 3 output
  extract_lets -merge +onlyGivenNames f0_3 at hr
  have e_f0_3 : f0_3 = round3.f0 := rfl
  clear_value f0_3
  -- g0_3: loop iteration 3 output
  extract_lets -merge +onlyGivenNames g0_3 at hr
  have e_g0_3 : g0_3 = round3.g0 := rfl
  clear_value g0_3
  -- f1_3: loop iteration 3 output
  extract_lets -merge +onlyGivenNames f1_3 at hr
  have e_f1_3 : f1_3 = round3.f1 := rfl
  clear_value f1_3
  -- g1_3: loop iteration 3 output
  extract_lets -merge +onlyGivenNames g1_3 at hr
  have e_g1_3 : g1_3 = round3.g1 := rfl
  clear_value g1_3
  -- round4: loop iteration 4
  extract_lets -merge +onlyGivenNames round4 at hr
  have e_round4 : round4 = divsteps47Round ⟨a_3, cnt_3, b_3, f0_3, g0_3, f1_3, g1_3⟩ := rfl
  clear_value round4
  -- a_4: loop iteration 4 output
  extract_lets -merge +onlyGivenNames a_4 at hr
  have e_a_4 : a_4 = round4.a := rfl
  clear_value a_4
  -- cnt_4: loop iteration 4 output
  extract_lets -merge +onlyGivenNames cnt_4 at hr
  have e_cnt_4 : cnt_4 = round4.cnt := rfl
  clear_value cnt_4
  -- b_4: loop iteration 4 output
  extract_lets -merge +onlyGivenNames b_4 at hr
  have e_b_4 : b_4 = round4.b := rfl
  clear_value b_4
  -- f0_4: loop iteration 4 output
  extract_lets -merge +onlyGivenNames f0_4 at hr
  have e_f0_4 : f0_4 = round4.f0 := rfl
  clear_value f0_4
  -- g0_4: loop iteration 4 output
  extract_lets -merge +onlyGivenNames g0_4 at hr
  have e_g0_4 : g0_4 = round4.g0 := rfl
  clear_value g0_4
  -- f1_4: loop iteration 4 output
  extract_lets -merge +onlyGivenNames f1_4 at hr
  have e_f1_4 : f1_4 = round4.f1 := rfl
  clear_value f1_4
  -- g1_4: loop iteration 4 output
  extract_lets -merge +onlyGivenNames g1_4 at hr
  have e_g1_4 : g1_4 = round4.g1 := rfl
  clear_value g1_4
  -- round5: loop iteration 5
  extract_lets -merge +onlyGivenNames round5 at hr
  have e_round5 : round5 = divsteps47Round ⟨a_4, cnt_4, b_4, f0_4, g0_4, f1_4, g1_4⟩ := rfl
  clear_value round5
  -- a_5: loop iteration 5 output
  extract_lets -merge +onlyGivenNames a_5 at hr
  have e_a_5 : a_5 = round5.a := rfl
  clear_value a_5
  -- cnt_5: loop iteration 5 output
  extract_lets -merge +onlyGivenNames cnt_5 at hr
  have e_cnt_5 : cnt_5 = round5.cnt := rfl
  clear_value cnt_5
  -- b_5: loop iteration 5 output
  extract_lets -merge +onlyGivenNames b_5 at hr
  have e_b_5 : b_5 = round5.b := rfl
  clear_value b_5
  -- f0_5: loop iteration 5 output
  extract_lets -merge +onlyGivenNames f0_5 at hr
  have e_f0_5 : f0_5 = round5.f0 := rfl
  clear_value f0_5
  -- g0_5: loop iteration 5 output
  extract_lets -merge +onlyGivenNames g0_5 at hr
  have e_g0_5 : g0_5 = round5.g0 := rfl
  clear_value g0_5
  -- f1_5: loop iteration 5 output
  extract_lets -merge +onlyGivenNames f1_5 at hr
  have e_f1_5 : f1_5 = round5.f1 := rfl
  clear_value f1_5
  -- g1_5: loop iteration 5 output
  extract_lets -merge +onlyGivenNames g1_5 at hr
  have e_g1_5 : g1_5 = round5.g1 := rfl
  clear_value g1_5
  -- round6: loop iteration 6
  extract_lets -merge +onlyGivenNames round6 at hr
  have e_round6 : round6 = divsteps47Round ⟨a_5, cnt_5, b_5, f0_5, g0_5, f1_5, g1_5⟩ := rfl
  clear_value round6
  -- a_6: loop iteration 6 output
  extract_lets -merge +onlyGivenNames a_6 at hr
  have e_a_6 : a_6 = round6.a := rfl
  clear_value a_6
  -- cnt_6: loop iteration 6 output
  extract_lets -merge +onlyGivenNames cnt_6 at hr
  have e_cnt_6 : cnt_6 = round6.cnt := rfl
  clear_value cnt_6
  -- b_6: loop iteration 6 output
  extract_lets -merge +onlyGivenNames b_6 at hr
  have e_b_6 : b_6 = round6.b := rfl
  clear_value b_6
  -- f0_6: loop iteration 6 output
  extract_lets -merge +onlyGivenNames f0_6 at hr
  have e_f0_6 : f0_6 = round6.f0 := rfl
  clear_value f0_6
  -- g0_6: loop iteration 6 output
  extract_lets -merge +onlyGivenNames g0_6 at hr
  have e_g0_6 : g0_6 = round6.g0 := rfl
  clear_value g0_6
  -- f1_6: loop iteration 6 output
  extract_lets -merge +onlyGivenNames f1_6 at hr
  have e_f1_6 : f1_6 = round6.f1 := rfl
  clear_value f1_6
  -- g1_6: loop iteration 6 output
  extract_lets -merge +onlyGivenNames g1_6 at hr
  have e_g1_6 : g1_6 = round6.g1 := rfl
  clear_value g1_6
  -- round7: loop iteration 7
  extract_lets -merge +onlyGivenNames round7 at hr
  have e_round7 : round7 = divsteps47Round ⟨a_6, cnt_6, b_6, f0_6, g0_6, f1_6, g1_6⟩ := rfl
  clear_value round7
  -- a_7: loop iteration 7 output
  extract_lets -merge +onlyGivenNames a_7 at hr
  have e_a_7 : a_7 = round7.a := rfl
  clear_value a_7
  -- cnt_7: loop iteration 7 output
  extract_lets -merge +onlyGivenNames cnt_7 at hr
  have e_cnt_7 : cnt_7 = round7.cnt := rfl
  clear_value cnt_7
  -- b_7: loop iteration 7 output
  extract_lets -merge +onlyGivenNames b_7 at hr
  have e_b_7 : b_7 = round7.b := rfl
  clear_value b_7
  -- f0_7: loop iteration 7 output
  extract_lets -merge +onlyGivenNames f0_7 at hr
  have e_f0_7 : f0_7 = round7.f0 := rfl
  clear_value f0_7
  -- g0_7: loop iteration 7 output
  extract_lets -merge +onlyGivenNames g0_7 at hr
  have e_g0_7 : g0_7 = round7.g0 := rfl
  clear_value g0_7
  -- f1_7: loop iteration 7 output
  extract_lets -merge +onlyGivenNames f1_7 at hr
  have e_f1_7 : f1_7 = round7.f1 := rfl
  clear_value f1_7
  -- g1_7: loop iteration 7 output
  extract_lets -merge +onlyGivenNames g1_7 at hr
  have e_g1_7 : g1_7 = round7.g1 := rfl
  clear_value g1_7
  -- round8: loop iteration 8
  extract_lets -merge +onlyGivenNames round8 at hr
  have e_round8 : round8 = divsteps47Round ⟨a_7, cnt_7, b_7, f0_7, g0_7, f1_7, g1_7⟩ := rfl
  clear_value round8
  -- a_8: loop iteration 8 output
  extract_lets -merge +onlyGivenNames a_8 at hr
  have e_a_8 : a_8 = round8.a := rfl
  clear_value a_8
  -- cnt_8: loop iteration 8 output
  extract_lets -merge +onlyGivenNames cnt_8 at hr
  have e_cnt_8 : cnt_8 = round8.cnt := rfl
  clear_value cnt_8
  -- b_8: loop iteration 8 output
  extract_lets -merge +onlyGivenNames b_8 at hr
  have e_b_8 : b_8 = round8.b := rfl
  clear_value b_8
  -- f0_8: loop iteration 8 output
  extract_lets -merge +onlyGivenNames f0_8 at hr
  have e_f0_8 : f0_8 = round8.f0 := rfl
  clear_value f0_8
  -- g0_8: loop iteration 8 output
  extract_lets -merge +onlyGivenNames g0_8 at hr
  have e_g0_8 : g0_8 = round8.g0 := rfl
  clear_value g0_8
  -- f1_8: loop iteration 8 output
  extract_lets -merge +onlyGivenNames f1_8 at hr
  have e_f1_8 : f1_8 = round8.f1 := rfl
  clear_value f1_8
  -- g1_8: loop iteration 8 output
  extract_lets -merge +onlyGivenNames g1_8 at hr
  have e_g1_8 : g1_8 = round8.g1 := rfl
  clear_value g1_8
  -- round9: loop iteration 9
  extract_lets -merge +onlyGivenNames round9 at hr
  have e_round9 : round9 = divsteps47Round ⟨a_8, cnt_8, b_8, f0_8, g0_8, f1_8, g1_8⟩ := rfl
  clear_value round9
  -- a_9: loop iteration 9 output
  extract_lets -merge +onlyGivenNames a_9 at hr
  have e_a_9 : a_9 = round9.a := rfl
  clear_value a_9
  -- cnt_9: loop iteration 9 output
  extract_lets -merge +onlyGivenNames cnt_9 at hr
  have e_cnt_9 : cnt_9 = round9.cnt := rfl
  clear_value cnt_9
  -- b_9: loop iteration 9 output
  extract_lets -merge +onlyGivenNames b_9 at hr
  have e_b_9 : b_9 = round9.b := rfl
  clear_value b_9
  -- f0_9: loop iteration 9 output
  extract_lets -merge +onlyGivenNames f0_9 at hr
  have e_f0_9 : f0_9 = round9.f0 := rfl
  clear_value f0_9
  -- g0_9: loop iteration 9 output
  extract_lets -merge +onlyGivenNames g0_9 at hr
  have e_g0_9 : g0_9 = round9.g0 := rfl
  clear_value g0_9
  -- f1_9: loop iteration 9 output
  extract_lets -merge +onlyGivenNames f1_9 at hr
  have e_f1_9 : f1_9 = round9.f1 := rfl
  clear_value f1_9
  -- g1_9: loop iteration 9 output
  extract_lets -merge +onlyGivenNames g1_9 at hr
  have e_g1_9 : g1_9 = round9.g1 := rfl
  clear_value g1_9
  -- round10: loop iteration 10
  extract_lets -merge +onlyGivenNames round10 at hr
  have e_round10 : round10 = divsteps47Round ⟨a_9, cnt_9, b_9, f0_9, g0_9, f1_9, g1_9⟩ := rfl
  clear_value round10
  -- a_10: loop iteration 10 output
  extract_lets -merge +onlyGivenNames a_10 at hr
  have e_a_10 : a_10 = round10.a := rfl
  clear_value a_10
  -- cnt_10: loop iteration 10 output
  extract_lets -merge +onlyGivenNames cnt_10 at hr
  have e_cnt_10 : cnt_10 = round10.cnt := rfl
  clear_value cnt_10
  -- b_10: loop iteration 10 output
  extract_lets -merge +onlyGivenNames b_10 at hr
  have e_b_10 : b_10 = round10.b := rfl
  clear_value b_10
  -- f0_10: loop iteration 10 output
  extract_lets -merge +onlyGivenNames f0_10 at hr
  have e_f0_10 : f0_10 = round10.f0 := rfl
  clear_value f0_10
  -- g0_10: loop iteration 10 output
  extract_lets -merge +onlyGivenNames g0_10 at hr
  have e_g0_10 : g0_10 = round10.g0 := rfl
  clear_value g0_10
  -- f1_10: loop iteration 10 output
  extract_lets -merge +onlyGivenNames f1_10 at hr
  have e_f1_10 : f1_10 = round10.f1 := rfl
  clear_value f1_10
  -- g1_10: loop iteration 10 output
  extract_lets -merge +onlyGivenNames g1_10 at hr
  have e_g1_10 : g1_10 = round10.g1 := rfl
  clear_value g1_10
  -- round11: loop iteration 11
  extract_lets -merge +onlyGivenNames round11 at hr
  have e_round11 : round11 = divsteps47Round ⟨a_10, cnt_10, b_10, f0_10, g0_10, f1_10, g1_10⟩ := rfl
  clear_value round11
  -- a_11: loop iteration 11 output
  extract_lets -merge +onlyGivenNames a_11 at hr
  have e_a_11 : a_11 = round11.a := rfl
  clear_value a_11
  -- cnt_11: loop iteration 11 output
  extract_lets -merge +onlyGivenNames cnt_11 at hr
  have e_cnt_11 : cnt_11 = round11.cnt := rfl
  clear_value cnt_11
  -- b_11: loop iteration 11 output
  extract_lets -merge +onlyGivenNames b_11 at hr
  have e_b_11 : b_11 = round11.b := rfl
  clear_value b_11
  -- f0_11: loop iteration 11 output
  extract_lets -merge +onlyGivenNames f0_11 at hr
  have e_f0_11 : f0_11 = round11.f0 := rfl
  clear_value f0_11
  -- g0_11: loop iteration 11 output
  extract_lets -merge +onlyGivenNames g0_11 at hr
  have e_g0_11 : g0_11 = round11.g0 := rfl
  clear_value g0_11
  -- f1_11: loop iteration 11 output
  extract_lets -merge +onlyGivenNames f1_11 at hr
  have e_f1_11 : f1_11 = round11.f1 := rfl
  clear_value f1_11
  -- g1_11: loop iteration 11 output
  extract_lets -merge +onlyGivenNames g1_11 at hr
  have e_g1_11 : g1_11 = round11.g1 := rfl
  clear_value g1_11
  -- round12: loop iteration 12
  extract_lets -merge +onlyGivenNames round12 at hr
  have e_round12 : round12 = divsteps47Round ⟨a_11, cnt_11, b_11, f0_11, g0_11, f1_11, g1_11⟩ := rfl
  clear_value round12
  -- a_12: loop iteration 12 output
  extract_lets -merge +onlyGivenNames a_12 at hr
  have e_a_12 : a_12 = round12.a := rfl
  clear_value a_12
  -- cnt_12: loop iteration 12 output
  extract_lets -merge +onlyGivenNames cnt_12 at hr
  have e_cnt_12 : cnt_12 = round12.cnt := rfl
  clear_value cnt_12
  -- b_12: loop iteration 12 output
  extract_lets -merge +onlyGivenNames b_12 at hr
  have e_b_12 : b_12 = round12.b := rfl
  clear_value b_12
  -- f0_12: loop iteration 12 output
  extract_lets -merge +onlyGivenNames f0_12 at hr
  have e_f0_12 : f0_12 = round12.f0 := rfl
  clear_value f0_12
  -- g0_12: loop iteration 12 output
  extract_lets -merge +onlyGivenNames g0_12 at hr
  have e_g0_12 : g0_12 = round12.g0 := rfl
  clear_value g0_12
  -- f1_12: loop iteration 12 output
  extract_lets -merge +onlyGivenNames f1_12 at hr
  have e_f1_12 : f1_12 = round12.f1 := rfl
  clear_value f1_12
  -- g1_12: loop iteration 12 output
  extract_lets -merge +onlyGivenNames g1_12 at hr
  have e_g1_12 : g1_12 = round12.g1 := rfl
  clear_value g1_12
  -- round13: loop iteration 13
  extract_lets -merge +onlyGivenNames round13 at hr
  have e_round13 : round13 = divsteps47Round ⟨a_12, cnt_12, b_12, f0_12, g0_12, f1_12, g1_12⟩ := rfl
  clear_value round13
  -- a_13: loop iteration 13 output
  extract_lets -merge +onlyGivenNames a_13 at hr
  have e_a_13 : a_13 = round13.a := rfl
  clear_value a_13
  -- cnt_13: loop iteration 13 output
  extract_lets -merge +onlyGivenNames cnt_13 at hr
  have e_cnt_13 : cnt_13 = round13.cnt := rfl
  clear_value cnt_13
  -- b_13: loop iteration 13 output
  extract_lets -merge +onlyGivenNames b_13 at hr
  have e_b_13 : b_13 = round13.b := rfl
  clear_value b_13
  -- f0_13: loop iteration 13 output
  extract_lets -merge +onlyGivenNames f0_13 at hr
  have e_f0_13 : f0_13 = round13.f0 := rfl
  clear_value f0_13
  -- g0_13: loop iteration 13 output
  extract_lets -merge +onlyGivenNames g0_13 at hr
  have e_g0_13 : g0_13 = round13.g0 := rfl
  clear_value g0_13
  -- f1_13: loop iteration 13 output
  extract_lets -merge +onlyGivenNames f1_13 at hr
  have e_f1_13 : f1_13 = round13.f1 := rfl
  clear_value f1_13
  -- g1_13: loop iteration 13 output
  extract_lets -merge +onlyGivenNames g1_13 at hr
  have e_g1_13 : g1_13 = round13.g1 := rfl
  clear_value g1_13
  -- round14: loop iteration 14
  extract_lets -merge +onlyGivenNames round14 at hr
  have e_round14 : round14 = divsteps47Round ⟨a_13, cnt_13, b_13, f0_13, g0_13, f1_13, g1_13⟩ := rfl
  clear_value round14
  -- a_14: loop iteration 14 output
  extract_lets -merge +onlyGivenNames a_14 at hr
  have e_a_14 : a_14 = round14.a := rfl
  clear_value a_14
  -- cnt_14: loop iteration 14 output
  extract_lets -merge +onlyGivenNames cnt_14 at hr
  have e_cnt_14 : cnt_14 = round14.cnt := rfl
  clear_value cnt_14
  -- b_14: loop iteration 14 output
  extract_lets -merge +onlyGivenNames b_14 at hr
  have e_b_14 : b_14 = round14.b := rfl
  clear_value b_14
  -- f0_14: loop iteration 14 output
  extract_lets -merge +onlyGivenNames f0_14 at hr
  have e_f0_14 : f0_14 = round14.f0 := rfl
  clear_value f0_14
  -- g0_14: loop iteration 14 output
  extract_lets -merge +onlyGivenNames g0_14 at hr
  have e_g0_14 : g0_14 = round14.g0 := rfl
  clear_value g0_14
  -- f1_14: loop iteration 14 output
  extract_lets -merge +onlyGivenNames f1_14 at hr
  have e_f1_14 : f1_14 = round14.f1 := rfl
  clear_value f1_14
  -- g1_14: loop iteration 14 output
  extract_lets -merge +onlyGivenNames g1_14 at hr
  have e_g1_14 : g1_14 = round14.g1 := rfl
  clear_value g1_14
  -- round15: loop iteration 15
  extract_lets -merge +onlyGivenNames round15 at hr
  have e_round15 : round15 = divsteps47Round ⟨a_14, cnt_14, b_14, f0_14, g0_14, f1_14, g1_14⟩ := rfl
  clear_value round15
  -- a_15: loop iteration 15 output
  extract_lets -merge +onlyGivenNames a_15 at hr
  have e_a_15 : a_15 = round15.a := rfl
  clear_value a_15
  -- cnt_15: loop iteration 15 output
  extract_lets -merge +onlyGivenNames cnt_15 at hr
  have e_cnt_15 : cnt_15 = round15.cnt := rfl
  clear_value cnt_15
  -- b_15: loop iteration 15 output
  extract_lets -merge +onlyGivenNames b_15 at hr
  have e_b_15 : b_15 = round15.b := rfl
  clear_value b_15
  -- f0_15: loop iteration 15 output
  extract_lets -merge +onlyGivenNames f0_15 at hr
  have e_f0_15 : f0_15 = round15.f0 := rfl
  clear_value f0_15
  -- g0_15: loop iteration 15 output
  extract_lets -merge +onlyGivenNames g0_15 at hr
  have e_g0_15 : g0_15 = round15.g0 := rfl
  clear_value g0_15
  -- f1_15: loop iteration 15 output
  extract_lets -merge +onlyGivenNames f1_15 at hr
  have e_f1_15 : f1_15 = round15.f1 := rfl
  clear_value f1_15
  -- g1_15: loop iteration 15 output
  extract_lets -merge +onlyGivenNames g1_15 at hr
  have e_g1_15 : g1_15 = round15.g1 := rfl
  clear_value g1_15
  -- round16: loop iteration 16
  extract_lets -merge +onlyGivenNames round16 at hr
  have e_round16 : round16 = divsteps47Round ⟨a_15, cnt_15, b_15, f0_15, g0_15, f1_15, g1_15⟩ := rfl
  clear_value round16
  -- a_16: loop iteration 16 output
  extract_lets -merge +onlyGivenNames a_16 at hr
  have e_a_16 : a_16 = round16.a := rfl
  clear_value a_16
  -- cnt_16: loop iteration 16 output
  extract_lets -merge +onlyGivenNames cnt_16 at hr
  have e_cnt_16 : cnt_16 = round16.cnt := rfl
  clear_value cnt_16
  -- b_16: loop iteration 16 output
  extract_lets -merge +onlyGivenNames b_16 at hr
  have e_b_16 : b_16 = round16.b := rfl
  clear_value b_16
  -- f0_16: loop iteration 16 output
  extract_lets -merge +onlyGivenNames f0_16 at hr
  have e_f0_16 : f0_16 = round16.f0 := rfl
  clear_value f0_16
  -- g0_16: loop iteration 16 output
  extract_lets -merge +onlyGivenNames g0_16 at hr
  have e_g0_16 : g0_16 = round16.g0 := rfl
  clear_value g0_16
  -- f1_16: loop iteration 16 output
  extract_lets -merge +onlyGivenNames f1_16 at hr
  have e_f1_16 : f1_16 = round16.f1 := rfl
  clear_value f1_16
  -- g1_16: loop iteration 16 output
  extract_lets -merge +onlyGivenNames g1_16 at hr
  have e_g1_16 : g1_16 = round16.g1 := rfl
  clear_value g1_16
  -- round17: loop iteration 17
  extract_lets -merge +onlyGivenNames round17 at hr
  have e_round17 : round17 = divsteps47Round ⟨a_16, cnt_16, b_16, f0_16, g0_16, f1_16, g1_16⟩ := rfl
  clear_value round17
  -- a_17: loop iteration 17 output
  extract_lets -merge +onlyGivenNames a_17 at hr
  have e_a_17 : a_17 = round17.a := rfl
  clear_value a_17
  -- cnt_17: loop iteration 17 output
  extract_lets -merge +onlyGivenNames cnt_17 at hr
  have e_cnt_17 : cnt_17 = round17.cnt := rfl
  clear_value cnt_17
  -- b_17: loop iteration 17 output
  extract_lets -merge +onlyGivenNames b_17 at hr
  have e_b_17 : b_17 = round17.b := rfl
  clear_value b_17
  -- f0_17: loop iteration 17 output
  extract_lets -merge +onlyGivenNames f0_17 at hr
  have e_f0_17 : f0_17 = round17.f0 := rfl
  clear_value f0_17
  -- g0_17: loop iteration 17 output
  extract_lets -merge +onlyGivenNames g0_17 at hr
  have e_g0_17 : g0_17 = round17.g0 := rfl
  clear_value g0_17
  -- f1_17: loop iteration 17 output
  extract_lets -merge +onlyGivenNames f1_17 at hr
  have e_f1_17 : f1_17 = round17.f1 := rfl
  clear_value f1_17
  -- g1_17: loop iteration 17 output
  extract_lets -merge +onlyGivenNames g1_17 at hr
  have e_g1_17 : g1_17 = round17.g1 := rfl
  clear_value g1_17
  -- round18: loop iteration 18
  extract_lets -merge +onlyGivenNames round18 at hr
  have e_round18 : round18 = divsteps47Round ⟨a_17, cnt_17, b_17, f0_17, g0_17, f1_17, g1_17⟩ := rfl
  clear_value round18
  -- a_18: loop iteration 18 output
  extract_lets -merge +onlyGivenNames a_18 at hr
  have e_a_18 : a_18 = round18.a := rfl
  clear_value a_18
  -- cnt_18: loop iteration 18 output
  extract_lets -merge +onlyGivenNames cnt_18 at hr
  have e_cnt_18 : cnt_18 = round18.cnt := rfl
  clear_value cnt_18
  -- b_18: loop iteration 18 output
  extract_lets -merge +onlyGivenNames b_18 at hr
  have e_b_18 : b_18 = round18.b := rfl
  clear_value b_18
  -- f0_18: loop iteration 18 output
  extract_lets -merge +onlyGivenNames f0_18 at hr
  have e_f0_18 : f0_18 = round18.f0 := rfl
  clear_value f0_18
  -- g0_18: loop iteration 18 output
  extract_lets -merge +onlyGivenNames g0_18 at hr
  have e_g0_18 : g0_18 = round18.g0 := rfl
  clear_value g0_18
  -- f1_18: loop iteration 18 output
  extract_lets -merge +onlyGivenNames f1_18 at hr
  have e_f1_18 : f1_18 = round18.f1 := rfl
  clear_value f1_18
  -- g1_18: loop iteration 18 output
  extract_lets -merge +onlyGivenNames g1_18 at hr
  have e_g1_18 : g1_18 = round18.g1 := rfl
  clear_value g1_18
  -- round19: loop iteration 19
  extract_lets -merge +onlyGivenNames round19 at hr
  have e_round19 : round19 = divsteps47Round ⟨a_18, cnt_18, b_18, f0_18, g0_18, f1_18, g1_18⟩ := rfl
  clear_value round19
  -- a_19: loop iteration 19 output
  extract_lets -merge +onlyGivenNames a_19 at hr
  have e_a_19 : a_19 = round19.a := rfl
  clear_value a_19
  -- cnt_19: loop iteration 19 output
  extract_lets -merge +onlyGivenNames cnt_19 at hr
  have e_cnt_19 : cnt_19 = round19.cnt := rfl
  clear_value cnt_19
  -- b_19: loop iteration 19 output
  extract_lets -merge +onlyGivenNames b_19 at hr
  have e_b_19 : b_19 = round19.b := rfl
  clear_value b_19
  -- f0_19: loop iteration 19 output
  extract_lets -merge +onlyGivenNames f0_19 at hr
  have e_f0_19 : f0_19 = round19.f0 := rfl
  clear_value f0_19
  -- g0_19: loop iteration 19 output
  extract_lets -merge +onlyGivenNames g0_19 at hr
  have e_g0_19 : g0_19 = round19.g0 := rfl
  clear_value g0_19
  -- f1_19: loop iteration 19 output
  extract_lets -merge +onlyGivenNames f1_19 at hr
  have e_f1_19 : f1_19 = round19.f1 := rfl
  clear_value f1_19
  -- g1_19: loop iteration 19 output
  extract_lets -merge +onlyGivenNames g1_19 at hr
  have e_g1_19 : g1_19 = round19.g1 := rfl
  clear_value g1_19
  -- round20: loop iteration 20
  extract_lets -merge +onlyGivenNames round20 at hr
  have e_round20 : round20 = divsteps47Round ⟨a_19, cnt_19, b_19, f0_19, g0_19, f1_19, g1_19⟩ := rfl
  clear_value round20
  -- a_20: loop iteration 20 output
  extract_lets -merge +onlyGivenNames a_20 at hr
  have e_a_20 : a_20 = round20.a := rfl
  clear_value a_20
  -- cnt_20: loop iteration 20 output
  extract_lets -merge +onlyGivenNames cnt_20 at hr
  have e_cnt_20 : cnt_20 = round20.cnt := rfl
  clear_value cnt_20
  -- b_20: loop iteration 20 output
  extract_lets -merge +onlyGivenNames b_20 at hr
  have e_b_20 : b_20 = round20.b := rfl
  clear_value b_20
  -- f0_20: loop iteration 20 output
  extract_lets -merge +onlyGivenNames f0_20 at hr
  have e_f0_20 : f0_20 = round20.f0 := rfl
  clear_value f0_20
  -- g0_20: loop iteration 20 output
  extract_lets -merge +onlyGivenNames g0_20 at hr
  have e_g0_20 : g0_20 = round20.g0 := rfl
  clear_value g0_20
  -- f1_20: loop iteration 20 output
  extract_lets -merge +onlyGivenNames f1_20 at hr
  have e_f1_20 : f1_20 = round20.f1 := rfl
  clear_value f1_20
  -- g1_20: loop iteration 20 output
  extract_lets -merge +onlyGivenNames g1_20 at hr
  have e_g1_20 : g1_20 = round20.g1 := rfl
  clear_value g1_20
  -- round21: loop iteration 21
  extract_lets -merge +onlyGivenNames round21 at hr
  have e_round21 : round21 = divsteps47Round ⟨a_20, cnt_20, b_20, f0_20, g0_20, f1_20, g1_20⟩ := rfl
  clear_value round21
  -- a_21: loop iteration 21 output
  extract_lets -merge +onlyGivenNames a_21 at hr
  have e_a_21 : a_21 = round21.a := rfl
  clear_value a_21
  -- cnt_21: loop iteration 21 output
  extract_lets -merge +onlyGivenNames cnt_21 at hr
  have e_cnt_21 : cnt_21 = round21.cnt := rfl
  clear_value cnt_21
  -- b_21: loop iteration 21 output
  extract_lets -merge +onlyGivenNames b_21 at hr
  have e_b_21 : b_21 = round21.b := rfl
  clear_value b_21
  -- f0_21: loop iteration 21 output
  extract_lets -merge +onlyGivenNames f0_21 at hr
  have e_f0_21 : f0_21 = round21.f0 := rfl
  clear_value f0_21
  -- g0_21: loop iteration 21 output
  extract_lets -merge +onlyGivenNames g0_21 at hr
  have e_g0_21 : g0_21 = round21.g0 := rfl
  clear_value g0_21
  -- f1_21: loop iteration 21 output
  extract_lets -merge +onlyGivenNames f1_21 at hr
  have e_f1_21 : f1_21 = round21.f1 := rfl
  clear_value f1_21
  -- g1_21: loop iteration 21 output
  extract_lets -merge +onlyGivenNames g1_21 at hr
  have e_g1_21 : g1_21 = round21.g1 := rfl
  clear_value g1_21
  -- round22: loop iteration 22
  extract_lets -merge +onlyGivenNames round22 at hr
  have e_round22 : round22 = divsteps47Round ⟨a_21, cnt_21, b_21, f0_21, g0_21, f1_21, g1_21⟩ := rfl
  clear_value round22
  -- a_22: loop iteration 22 output
  extract_lets -merge +onlyGivenNames a_22 at hr
  have e_a_22 : a_22 = round22.a := rfl
  clear_value a_22
  -- cnt_22: loop iteration 22 output
  extract_lets -merge +onlyGivenNames cnt_22 at hr
  have e_cnt_22 : cnt_22 = round22.cnt := rfl
  clear_value cnt_22
  -- b_22: loop iteration 22 output
  extract_lets -merge +onlyGivenNames b_22 at hr
  have e_b_22 : b_22 = round22.b := rfl
  clear_value b_22
  -- f0_22: loop iteration 22 output
  extract_lets -merge +onlyGivenNames f0_22 at hr
  have e_f0_22 : f0_22 = round22.f0 := rfl
  clear_value f0_22
  -- g0_22: loop iteration 22 output
  extract_lets -merge +onlyGivenNames g0_22 at hr
  have e_g0_22 : g0_22 = round22.g0 := rfl
  clear_value g0_22
  -- f1_22: loop iteration 22 output
  extract_lets -merge +onlyGivenNames f1_22 at hr
  have e_f1_22 : f1_22 = round22.f1 := rfl
  clear_value f1_22
  -- g1_22: loop iteration 22 output
  extract_lets -merge +onlyGivenNames g1_22 at hr
  have e_g1_22 : g1_22 = round22.g1 := rfl
  clear_value g1_22
  -- round23: loop iteration 23
  extract_lets -merge +onlyGivenNames round23 at hr
  have e_round23 : round23 = divsteps47Round ⟨a_22, cnt_22, b_22, f0_22, g0_22, f1_22, g1_22⟩ := rfl
  clear_value round23
  -- a_23: loop iteration 23 output
  extract_lets -merge +onlyGivenNames a_23 at hr
  have e_a_23 : a_23 = round23.a := rfl
  clear_value a_23
  -- cnt_23: loop iteration 23 output
  extract_lets -merge +onlyGivenNames cnt_23 at hr
  have e_cnt_23 : cnt_23 = round23.cnt := rfl
  clear_value cnt_23
  -- b_23: loop iteration 23 output
  extract_lets -merge +onlyGivenNames b_23 at hr
  have e_b_23 : b_23 = round23.b := rfl
  clear_value b_23
  -- f0_23: loop iteration 23 output
  extract_lets -merge +onlyGivenNames f0_23 at hr
  have e_f0_23 : f0_23 = round23.f0 := rfl
  clear_value f0_23
  -- g0_23: loop iteration 23 output
  extract_lets -merge +onlyGivenNames g0_23 at hr
  have e_g0_23 : g0_23 = round23.g0 := rfl
  clear_value g0_23
  -- f1_23: loop iteration 23 output
  extract_lets -merge +onlyGivenNames f1_23 at hr
  have e_f1_23 : f1_23 = round23.f1 := rfl
  clear_value f1_23
  -- g1_23: loop iteration 23 output
  extract_lets -merge +onlyGivenNames g1_23 at hr
  have e_g1_23 : g1_23 = round23.g1 := rfl
  clear_value g1_23
  -- round24: loop iteration 24
  extract_lets -merge +onlyGivenNames round24 at hr
  have e_round24 : round24 = divsteps47Round ⟨a_23, cnt_23, b_23, f0_23, g0_23, f1_23, g1_23⟩ := rfl
  clear_value round24
  -- a_24: loop iteration 24 output
  extract_lets -merge +onlyGivenNames a_24 at hr
  have e_a_24 : a_24 = round24.a := rfl
  clear_value a_24
  -- cnt_24: loop iteration 24 output
  extract_lets -merge +onlyGivenNames cnt_24 at hr
  have e_cnt_24 : cnt_24 = round24.cnt := rfl
  clear_value cnt_24
  -- b_24: loop iteration 24 output
  extract_lets -merge +onlyGivenNames b_24 at hr
  have e_b_24 : b_24 = round24.b := rfl
  clear_value b_24
  -- f0_24: loop iteration 24 output
  extract_lets -merge +onlyGivenNames f0_24 at hr
  have e_f0_24 : f0_24 = round24.f0 := rfl
  clear_value f0_24
  -- g0_24: loop iteration 24 output
  extract_lets -merge +onlyGivenNames g0_24 at hr
  have e_g0_24 : g0_24 = round24.g0 := rfl
  clear_value g0_24
  -- f1_24: loop iteration 24 output
  extract_lets -merge +onlyGivenNames f1_24 at hr
  have e_f1_24 : f1_24 = round24.f1 := rfl
  clear_value f1_24
  -- g1_24: loop iteration 24 output
  extract_lets -merge +onlyGivenNames g1_24 at hr
  have e_g1_24 : g1_24 = round24.g1 := rfl
  clear_value g1_24
  -- round25: loop iteration 25
  extract_lets -merge +onlyGivenNames round25 at hr
  have e_round25 : round25 = divsteps47Round ⟨a_24, cnt_24, b_24, f0_24, g0_24, f1_24, g1_24⟩ := rfl
  clear_value round25
  -- a_25: loop iteration 25 output
  extract_lets -merge +onlyGivenNames a_25 at hr
  have e_a_25 : a_25 = round25.a := rfl
  clear_value a_25
  -- cnt_25: loop iteration 25 output
  extract_lets -merge +onlyGivenNames cnt_25 at hr
  have e_cnt_25 : cnt_25 = round25.cnt := rfl
  clear_value cnt_25
  -- b_25: loop iteration 25 output
  extract_lets -merge +onlyGivenNames b_25 at hr
  have e_b_25 : b_25 = round25.b := rfl
  clear_value b_25
  -- f0_25: loop iteration 25 output
  extract_lets -merge +onlyGivenNames f0_25 at hr
  have e_f0_25 : f0_25 = round25.f0 := rfl
  clear_value f0_25
  -- g0_25: loop iteration 25 output
  extract_lets -merge +onlyGivenNames g0_25 at hr
  have e_g0_25 : g0_25 = round25.g0 := rfl
  clear_value g0_25
  -- f1_25: loop iteration 25 output
  extract_lets -merge +onlyGivenNames f1_25 at hr
  have e_f1_25 : f1_25 = round25.f1 := rfl
  clear_value f1_25
  -- g1_25: loop iteration 25 output
  extract_lets -merge +onlyGivenNames g1_25 at hr
  have e_g1_25 : g1_25 = round25.g1 := rfl
  clear_value g1_25
  -- round26: loop iteration 26
  extract_lets -merge +onlyGivenNames round26 at hr
  have e_round26 : round26 = divsteps47Round ⟨a_25, cnt_25, b_25, f0_25, g0_25, f1_25, g1_25⟩ := rfl
  clear_value round26
  -- a_26: loop iteration 26 output
  extract_lets -merge +onlyGivenNames a_26 at hr
  have e_a_26 : a_26 = round26.a := rfl
  clear_value a_26
  -- cnt_26: loop iteration 26 output
  extract_lets -merge +onlyGivenNames cnt_26 at hr
  have e_cnt_26 : cnt_26 = round26.cnt := rfl
  clear_value cnt_26
  -- b_26: loop iteration 26 output
  extract_lets -merge +onlyGivenNames b_26 at hr
  have e_b_26 : b_26 = round26.b := rfl
  clear_value b_26
  -- f0_26: loop iteration 26 output
  extract_lets -merge +onlyGivenNames f0_26 at hr
  have e_f0_26 : f0_26 = round26.f0 := rfl
  clear_value f0_26
  -- g0_26: loop iteration 26 output
  extract_lets -merge +onlyGivenNames g0_26 at hr
  have e_g0_26 : g0_26 = round26.g0 := rfl
  clear_value g0_26
  -- f1_26: loop iteration 26 output
  extract_lets -merge +onlyGivenNames f1_26 at hr
  have e_f1_26 : f1_26 = round26.f1 := rfl
  clear_value f1_26
  -- g1_26: loop iteration 26 output
  extract_lets -merge +onlyGivenNames g1_26 at hr
  have e_g1_26 : g1_26 = round26.g1 := rfl
  clear_value g1_26
  -- round27: loop iteration 27
  extract_lets -merge +onlyGivenNames round27 at hr
  have e_round27 : round27 = divsteps47Round ⟨a_26, cnt_26, b_26, f0_26, g0_26, f1_26, g1_26⟩ := rfl
  clear_value round27
  -- a_27: loop iteration 27 output
  extract_lets -merge +onlyGivenNames a_27 at hr
  have e_a_27 : a_27 = round27.a := rfl
  clear_value a_27
  -- cnt_27: loop iteration 27 output
  extract_lets -merge +onlyGivenNames cnt_27 at hr
  have e_cnt_27 : cnt_27 = round27.cnt := rfl
  clear_value cnt_27
  -- b_27: loop iteration 27 output
  extract_lets -merge +onlyGivenNames b_27 at hr
  have e_b_27 : b_27 = round27.b := rfl
  clear_value b_27
  -- f0_27: loop iteration 27 output
  extract_lets -merge +onlyGivenNames f0_27 at hr
  have e_f0_27 : f0_27 = round27.f0 := rfl
  clear_value f0_27
  -- g0_27: loop iteration 27 output
  extract_lets -merge +onlyGivenNames g0_27 at hr
  have e_g0_27 : g0_27 = round27.g0 := rfl
  clear_value g0_27
  -- f1_27: loop iteration 27 output
  extract_lets -merge +onlyGivenNames f1_27 at hr
  have e_f1_27 : f1_27 = round27.f1 := rfl
  clear_value f1_27
  -- g1_27: loop iteration 27 output
  extract_lets -merge +onlyGivenNames g1_27 at hr
  have e_g1_27 : g1_27 = round27.g1 := rfl
  clear_value g1_27
  -- round28: loop iteration 28
  extract_lets -merge +onlyGivenNames round28 at hr
  have e_round28 : round28 = divsteps47Round ⟨a_27, cnt_27, b_27, f0_27, g0_27, f1_27, g1_27⟩ := rfl
  clear_value round28
  -- a_28: loop iteration 28 output
  extract_lets -merge +onlyGivenNames a_28 at hr
  have e_a_28 : a_28 = round28.a := rfl
  clear_value a_28
  -- cnt_28: loop iteration 28 output
  extract_lets -merge +onlyGivenNames cnt_28 at hr
  have e_cnt_28 : cnt_28 = round28.cnt := rfl
  clear_value cnt_28
  -- b_28: loop iteration 28 output
  extract_lets -merge +onlyGivenNames b_28 at hr
  have e_b_28 : b_28 = round28.b := rfl
  clear_value b_28
  -- f0_28: loop iteration 28 output
  extract_lets -merge +onlyGivenNames f0_28 at hr
  have e_f0_28 : f0_28 = round28.f0 := rfl
  clear_value f0_28
  -- g0_28: loop iteration 28 output
  extract_lets -merge +onlyGivenNames g0_28 at hr
  have e_g0_28 : g0_28 = round28.g0 := rfl
  clear_value g0_28
  -- f1_28: loop iteration 28 output
  extract_lets -merge +onlyGivenNames f1_28 at hr
  have e_f1_28 : f1_28 = round28.f1 := rfl
  clear_value f1_28
  -- g1_28: loop iteration 28 output
  extract_lets -merge +onlyGivenNames g1_28 at hr
  have e_g1_28 : g1_28 = round28.g1 := rfl
  clear_value g1_28
  -- round29: loop iteration 29
  extract_lets -merge +onlyGivenNames round29 at hr
  have e_round29 : round29 = divsteps47Round ⟨a_28, cnt_28, b_28, f0_28, g0_28, f1_28, g1_28⟩ := rfl
  clear_value round29
  -- a_29: loop iteration 29 output
  extract_lets -merge +onlyGivenNames a_29 at hr
  have e_a_29 : a_29 = round29.a := rfl
  clear_value a_29
  -- cnt_29: loop iteration 29 output
  extract_lets -merge +onlyGivenNames cnt_29 at hr
  have e_cnt_29 : cnt_29 = round29.cnt := rfl
  clear_value cnt_29
  -- b_29: loop iteration 29 output
  extract_lets -merge +onlyGivenNames b_29 at hr
  have e_b_29 : b_29 = round29.b := rfl
  clear_value b_29
  -- f0_29: loop iteration 29 output
  extract_lets -merge +onlyGivenNames f0_29 at hr
  have e_f0_29 : f0_29 = round29.f0 := rfl
  clear_value f0_29
  -- g0_29: loop iteration 29 output
  extract_lets -merge +onlyGivenNames g0_29 at hr
  have e_g0_29 : g0_29 = round29.g0 := rfl
  clear_value g0_29
  -- f1_29: loop iteration 29 output
  extract_lets -merge +onlyGivenNames f1_29 at hr
  have e_f1_29 : f1_29 = round29.f1 := rfl
  clear_value f1_29
  -- g1_29: loop iteration 29 output
  extract_lets -merge +onlyGivenNames g1_29 at hr
  have e_g1_29 : g1_29 = round29.g1 := rfl
  clear_value g1_29
  -- round30: loop iteration 30
  extract_lets -merge +onlyGivenNames round30 at hr
  have e_round30 : round30 = divsteps47Round ⟨a_29, cnt_29, b_29, f0_29, g0_29, f1_29, g1_29⟩ := rfl
  clear_value round30
  -- a_30: loop iteration 30 output
  extract_lets -merge +onlyGivenNames a_30 at hr
  have e_a_30 : a_30 = round30.a := rfl
  clear_value a_30
  -- cnt_30: loop iteration 30 output
  extract_lets -merge +onlyGivenNames cnt_30 at hr
  have e_cnt_30 : cnt_30 = round30.cnt := rfl
  clear_value cnt_30
  -- b_30: loop iteration 30 output
  extract_lets -merge +onlyGivenNames b_30 at hr
  have e_b_30 : b_30 = round30.b := rfl
  clear_value b_30
  -- f0_30: loop iteration 30 output
  extract_lets -merge +onlyGivenNames f0_30 at hr
  have e_f0_30 : f0_30 = round30.f0 := rfl
  clear_value f0_30
  -- g0_30: loop iteration 30 output
  extract_lets -merge +onlyGivenNames g0_30 at hr
  have e_g0_30 : g0_30 = round30.g0 := rfl
  clear_value g0_30
  -- f1_30: loop iteration 30 output
  extract_lets -merge +onlyGivenNames f1_30 at hr
  have e_f1_30 : f1_30 = round30.f1 := rfl
  clear_value f1_30
  -- g1_30: loop iteration 30 output
  extract_lets -merge +onlyGivenNames g1_30 at hr
  have e_g1_30 : g1_30 = round30.g1 := rfl
  clear_value g1_30
  -- round31: loop iteration 31
  extract_lets -merge +onlyGivenNames round31 at hr
  have e_round31 : round31 = divsteps47Round ⟨a_30, cnt_30, b_30, f0_30, g0_30, f1_30, g1_30⟩ := rfl
  clear_value round31
  -- a_31: loop iteration 31 output
  extract_lets -merge +onlyGivenNames a_31 at hr
  have e_a_31 : a_31 = round31.a := rfl
  clear_value a_31
  -- cnt_31: loop iteration 31 output
  extract_lets -merge +onlyGivenNames cnt_31 at hr
  have e_cnt_31 : cnt_31 = round31.cnt := rfl
  clear_value cnt_31
  -- b_31: loop iteration 31 output
  extract_lets -merge +onlyGivenNames b_31 at hr
  have e_b_31 : b_31 = round31.b := rfl
  clear_value b_31
  -- f0_31: loop iteration 31 output
  extract_lets -merge +onlyGivenNames f0_31 at hr
  have e_f0_31 : f0_31 = round31.f0 := rfl
  clear_value f0_31
  -- g0_31: loop iteration 31 output
  extract_lets -merge +onlyGivenNames g0_31 at hr
  have e_g0_31 : g0_31 = round31.g0 := rfl
  clear_value g0_31
  -- f1_31: loop iteration 31 output
  extract_lets -merge +onlyGivenNames f1_31 at hr
  have e_f1_31 : f1_31 = round31.f1 := rfl
  clear_value f1_31
  -- g1_31: loop iteration 31 output
  extract_lets -merge +onlyGivenNames g1_31 at hr
  have e_g1_31 : g1_31 = round31.g1 := rfl
  clear_value g1_31
  -- round32: loop iteration 32
  extract_lets -merge +onlyGivenNames round32 at hr
  have e_round32 : round32 = divsteps47Round ⟨a_31, cnt_31, b_31, f0_31, g0_31, f1_31, g1_31⟩ := rfl
  clear_value round32
  -- a_32: loop iteration 32 output
  extract_lets -merge +onlyGivenNames a_32 at hr
  have e_a_32 : a_32 = round32.a := rfl
  clear_value a_32
  -- cnt_32: loop iteration 32 output
  extract_lets -merge +onlyGivenNames cnt_32 at hr
  have e_cnt_32 : cnt_32 = round32.cnt := rfl
  clear_value cnt_32
  -- b_32: loop iteration 32 output
  extract_lets -merge +onlyGivenNames b_32 at hr
  have e_b_32 : b_32 = round32.b := rfl
  clear_value b_32
  -- f0_32: loop iteration 32 output
  extract_lets -merge +onlyGivenNames f0_32 at hr
  have e_f0_32 : f0_32 = round32.f0 := rfl
  clear_value f0_32
  -- g0_32: loop iteration 32 output
  extract_lets -merge +onlyGivenNames g0_32 at hr
  have e_g0_32 : g0_32 = round32.g0 := rfl
  clear_value g0_32
  -- f1_32: loop iteration 32 output
  extract_lets -merge +onlyGivenNames f1_32 at hr
  have e_f1_32 : f1_32 = round32.f1 := rfl
  clear_value f1_32
  -- g1_32: loop iteration 32 output
  extract_lets -merge +onlyGivenNames g1_32 at hr
  have e_g1_32 : g1_32 = round32.g1 := rfl
  clear_value g1_32
  -- round33: loop iteration 33
  extract_lets -merge +onlyGivenNames round33 at hr
  have e_round33 : round33 = divsteps47Round ⟨a_32, cnt_32, b_32, f0_32, g0_32, f1_32, g1_32⟩ := rfl
  clear_value round33
  -- a_33: loop iteration 33 output
  extract_lets -merge +onlyGivenNames a_33 at hr
  have e_a_33 : a_33 = round33.a := rfl
  clear_value a_33
  -- cnt_33: loop iteration 33 output
  extract_lets -merge +onlyGivenNames cnt_33 at hr
  have e_cnt_33 : cnt_33 = round33.cnt := rfl
  clear_value cnt_33
  -- b_33: loop iteration 33 output
  extract_lets -merge +onlyGivenNames b_33 at hr
  have e_b_33 : b_33 = round33.b := rfl
  clear_value b_33
  -- f0_33: loop iteration 33 output
  extract_lets -merge +onlyGivenNames f0_33 at hr
  have e_f0_33 : f0_33 = round33.f0 := rfl
  clear_value f0_33
  -- g0_33: loop iteration 33 output
  extract_lets -merge +onlyGivenNames g0_33 at hr
  have e_g0_33 : g0_33 = round33.g0 := rfl
  clear_value g0_33
  -- f1_33: loop iteration 33 output
  extract_lets -merge +onlyGivenNames f1_33 at hr
  have e_f1_33 : f1_33 = round33.f1 := rfl
  clear_value f1_33
  -- g1_33: loop iteration 33 output
  extract_lets -merge +onlyGivenNames g1_33 at hr
  have e_g1_33 : g1_33 = round33.g1 := rfl
  clear_value g1_33
  -- round34: loop iteration 34
  extract_lets -merge +onlyGivenNames round34 at hr
  have e_round34 : round34 = divsteps47Round ⟨a_33, cnt_33, b_33, f0_33, g0_33, f1_33, g1_33⟩ := rfl
  clear_value round34
  -- a_34: loop iteration 34 output
  extract_lets -merge +onlyGivenNames a_34 at hr
  have e_a_34 : a_34 = round34.a := rfl
  clear_value a_34
  -- cnt_34: loop iteration 34 output
  extract_lets -merge +onlyGivenNames cnt_34 at hr
  have e_cnt_34 : cnt_34 = round34.cnt := rfl
  clear_value cnt_34
  -- b_34: loop iteration 34 output
  extract_lets -merge +onlyGivenNames b_34 at hr
  have e_b_34 : b_34 = round34.b := rfl
  clear_value b_34
  -- f0_34: loop iteration 34 output
  extract_lets -merge +onlyGivenNames f0_34 at hr
  have e_f0_34 : f0_34 = round34.f0 := rfl
  clear_value f0_34
  -- g0_34: loop iteration 34 output
  extract_lets -merge +onlyGivenNames g0_34 at hr
  have e_g0_34 : g0_34 = round34.g0 := rfl
  clear_value g0_34
  -- f1_34: loop iteration 34 output
  extract_lets -merge +onlyGivenNames f1_34 at hr
  have e_f1_34 : f1_34 = round34.f1 := rfl
  clear_value f1_34
  -- g1_34: loop iteration 34 output
  extract_lets -merge +onlyGivenNames g1_34 at hr
  have e_g1_34 : g1_34 = round34.g1 := rfl
  clear_value g1_34
  -- round35: loop iteration 35
  extract_lets -merge +onlyGivenNames round35 at hr
  have e_round35 : round35 = divsteps47Round ⟨a_34, cnt_34, b_34, f0_34, g0_34, f1_34, g1_34⟩ := rfl
  clear_value round35
  -- a_35: loop iteration 35 output
  extract_lets -merge +onlyGivenNames a_35 at hr
  have e_a_35 : a_35 = round35.a := rfl
  clear_value a_35
  -- cnt_35: loop iteration 35 output
  extract_lets -merge +onlyGivenNames cnt_35 at hr
  have e_cnt_35 : cnt_35 = round35.cnt := rfl
  clear_value cnt_35
  -- b_35: loop iteration 35 output
  extract_lets -merge +onlyGivenNames b_35 at hr
  have e_b_35 : b_35 = round35.b := rfl
  clear_value b_35
  -- f0_35: loop iteration 35 output
  extract_lets -merge +onlyGivenNames f0_35 at hr
  have e_f0_35 : f0_35 = round35.f0 := rfl
  clear_value f0_35
  -- g0_35: loop iteration 35 output
  extract_lets -merge +onlyGivenNames g0_35 at hr
  have e_g0_35 : g0_35 = round35.g0 := rfl
  clear_value g0_35
  -- f1_35: loop iteration 35 output
  extract_lets -merge +onlyGivenNames f1_35 at hr
  have e_f1_35 : f1_35 = round35.f1 := rfl
  clear_value f1_35
  -- g1_35: loop iteration 35 output
  extract_lets -merge +onlyGivenNames g1_35 at hr
  have e_g1_35 : g1_35 = round35.g1 := rfl
  clear_value g1_35
  -- round36: loop iteration 36
  extract_lets -merge +onlyGivenNames round36 at hr
  have e_round36 : round36 = divsteps47Round ⟨a_35, cnt_35, b_35, f0_35, g0_35, f1_35, g1_35⟩ := rfl
  clear_value round36
  -- a_36: loop iteration 36 output
  extract_lets -merge +onlyGivenNames a_36 at hr
  have e_a_36 : a_36 = round36.a := rfl
  clear_value a_36
  -- cnt_36: loop iteration 36 output
  extract_lets -merge +onlyGivenNames cnt_36 at hr
  have e_cnt_36 : cnt_36 = round36.cnt := rfl
  clear_value cnt_36
  -- b_36: loop iteration 36 output
  extract_lets -merge +onlyGivenNames b_36 at hr
  have e_b_36 : b_36 = round36.b := rfl
  clear_value b_36
  -- f0_36: loop iteration 36 output
  extract_lets -merge +onlyGivenNames f0_36 at hr
  have e_f0_36 : f0_36 = round36.f0 := rfl
  clear_value f0_36
  -- g0_36: loop iteration 36 output
  extract_lets -merge +onlyGivenNames g0_36 at hr
  have e_g0_36 : g0_36 = round36.g0 := rfl
  clear_value g0_36
  -- f1_36: loop iteration 36 output
  extract_lets -merge +onlyGivenNames f1_36 at hr
  have e_f1_36 : f1_36 = round36.f1 := rfl
  clear_value f1_36
  -- g1_36: loop iteration 36 output
  extract_lets -merge +onlyGivenNames g1_36 at hr
  have e_g1_36 : g1_36 = round36.g1 := rfl
  clear_value g1_36
  -- round37: loop iteration 37
  extract_lets -merge +onlyGivenNames round37 at hr
  have e_round37 : round37 = divsteps47Round ⟨a_36, cnt_36, b_36, f0_36, g0_36, f1_36, g1_36⟩ := rfl
  clear_value round37
  -- a_37: loop iteration 37 output
  extract_lets -merge +onlyGivenNames a_37 at hr
  have e_a_37 : a_37 = round37.a := rfl
  clear_value a_37
  -- cnt_37: loop iteration 37 output
  extract_lets -merge +onlyGivenNames cnt_37 at hr
  have e_cnt_37 : cnt_37 = round37.cnt := rfl
  clear_value cnt_37
  -- b_37: loop iteration 37 output
  extract_lets -merge +onlyGivenNames b_37 at hr
  have e_b_37 : b_37 = round37.b := rfl
  clear_value b_37
  -- f0_37: loop iteration 37 output
  extract_lets -merge +onlyGivenNames f0_37 at hr
  have e_f0_37 : f0_37 = round37.f0 := rfl
  clear_value f0_37
  -- g0_37: loop iteration 37 output
  extract_lets -merge +onlyGivenNames g0_37 at hr
  have e_g0_37 : g0_37 = round37.g0 := rfl
  clear_value g0_37
  -- f1_37: loop iteration 37 output
  extract_lets -merge +onlyGivenNames f1_37 at hr
  have e_f1_37 : f1_37 = round37.f1 := rfl
  clear_value f1_37
  -- g1_37: loop iteration 37 output
  extract_lets -merge +onlyGivenNames g1_37 at hr
  have e_g1_37 : g1_37 = round37.g1 := rfl
  clear_value g1_37
  -- round38: loop iteration 38
  extract_lets -merge +onlyGivenNames round38 at hr
  have e_round38 : round38 = divsteps47Round ⟨a_37, cnt_37, b_37, f0_37, g0_37, f1_37, g1_37⟩ := rfl
  clear_value round38
  -- a_38: loop iteration 38 output
  extract_lets -merge +onlyGivenNames a_38 at hr
  have e_a_38 : a_38 = round38.a := rfl
  clear_value a_38
  -- cnt_38: loop iteration 38 output
  extract_lets -merge +onlyGivenNames cnt_38 at hr
  have e_cnt_38 : cnt_38 = round38.cnt := rfl
  clear_value cnt_38
  -- b_38: loop iteration 38 output
  extract_lets -merge +onlyGivenNames b_38 at hr
  have e_b_38 : b_38 = round38.b := rfl
  clear_value b_38
  -- f0_38: loop iteration 38 output
  extract_lets -merge +onlyGivenNames f0_38 at hr
  have e_f0_38 : f0_38 = round38.f0 := rfl
  clear_value f0_38
  -- g0_38: loop iteration 38 output
  extract_lets -merge +onlyGivenNames g0_38 at hr
  have e_g0_38 : g0_38 = round38.g0 := rfl
  clear_value g0_38
  -- f1_38: loop iteration 38 output
  extract_lets -merge +onlyGivenNames f1_38 at hr
  have e_f1_38 : f1_38 = round38.f1 := rfl
  clear_value f1_38
  -- g1_38: loop iteration 38 output
  extract_lets -merge +onlyGivenNames g1_38 at hr
  have e_g1_38 : g1_38 = round38.g1 := rfl
  clear_value g1_38
  -- round39: loop iteration 39
  extract_lets -merge +onlyGivenNames round39 at hr
  have e_round39 : round39 = divsteps47Round ⟨a_38, cnt_38, b_38, f0_38, g0_38, f1_38, g1_38⟩ := rfl
  clear_value round39
  -- a_39: loop iteration 39 output
  extract_lets -merge +onlyGivenNames a_39 at hr
  have e_a_39 : a_39 = round39.a := rfl
  clear_value a_39
  -- cnt_39: loop iteration 39 output
  extract_lets -merge +onlyGivenNames cnt_39 at hr
  have e_cnt_39 : cnt_39 = round39.cnt := rfl
  clear_value cnt_39
  -- b_39: loop iteration 39 output
  extract_lets -merge +onlyGivenNames b_39 at hr
  have e_b_39 : b_39 = round39.b := rfl
  clear_value b_39
  -- f0_39: loop iteration 39 output
  extract_lets -merge +onlyGivenNames f0_39 at hr
  have e_f0_39 : f0_39 = round39.f0 := rfl
  clear_value f0_39
  -- g0_39: loop iteration 39 output
  extract_lets -merge +onlyGivenNames g0_39 at hr
  have e_g0_39 : g0_39 = round39.g0 := rfl
  clear_value g0_39
  -- f1_39: loop iteration 39 output
  extract_lets -merge +onlyGivenNames f1_39 at hr
  have e_f1_39 : f1_39 = round39.f1 := rfl
  clear_value f1_39
  -- g1_39: loop iteration 39 output
  extract_lets -merge +onlyGivenNames g1_39 at hr
  have e_g1_39 : g1_39 = round39.g1 := rfl
  clear_value g1_39
  -- round40: loop iteration 40
  extract_lets -merge +onlyGivenNames round40 at hr
  have e_round40 : round40 = divsteps47Round ⟨a_39, cnt_39, b_39, f0_39, g0_39, f1_39, g1_39⟩ := rfl
  clear_value round40
  -- a_40: loop iteration 40 output
  extract_lets -merge +onlyGivenNames a_40 at hr
  have e_a_40 : a_40 = round40.a := rfl
  clear_value a_40
  -- cnt_40: loop iteration 40 output
  extract_lets -merge +onlyGivenNames cnt_40 at hr
  have e_cnt_40 : cnt_40 = round40.cnt := rfl
  clear_value cnt_40
  -- b_40: loop iteration 40 output
  extract_lets -merge +onlyGivenNames b_40 at hr
  have e_b_40 : b_40 = round40.b := rfl
  clear_value b_40
  -- f0_40: loop iteration 40 output
  extract_lets -merge +onlyGivenNames f0_40 at hr
  have e_f0_40 : f0_40 = round40.f0 := rfl
  clear_value f0_40
  -- g0_40: loop iteration 40 output
  extract_lets -merge +onlyGivenNames g0_40 at hr
  have e_g0_40 : g0_40 = round40.g0 := rfl
  clear_value g0_40
  -- f1_40: loop iteration 40 output
  extract_lets -merge +onlyGivenNames f1_40 at hr
  have e_f1_40 : f1_40 = round40.f1 := rfl
  clear_value f1_40
  -- g1_40: loop iteration 40 output
  extract_lets -merge +onlyGivenNames g1_40 at hr
  have e_g1_40 : g1_40 = round40.g1 := rfl
  clear_value g1_40
  -- round41: loop iteration 41
  extract_lets -merge +onlyGivenNames round41 at hr
  have e_round41 : round41 = divsteps47Round ⟨a_40, cnt_40, b_40, f0_40, g0_40, f1_40, g1_40⟩ := rfl
  clear_value round41
  -- a_41: loop iteration 41 output
  extract_lets -merge +onlyGivenNames a_41 at hr
  have e_a_41 : a_41 = round41.a := rfl
  clear_value a_41
  -- cnt_41: loop iteration 41 output
  extract_lets -merge +onlyGivenNames cnt_41 at hr
  have e_cnt_41 : cnt_41 = round41.cnt := rfl
  clear_value cnt_41
  -- b_41: loop iteration 41 output
  extract_lets -merge +onlyGivenNames b_41 at hr
  have e_b_41 : b_41 = round41.b := rfl
  clear_value b_41
  -- f0_41: loop iteration 41 output
  extract_lets -merge +onlyGivenNames f0_41 at hr
  have e_f0_41 : f0_41 = round41.f0 := rfl
  clear_value f0_41
  -- g0_41: loop iteration 41 output
  extract_lets -merge +onlyGivenNames g0_41 at hr
  have e_g0_41 : g0_41 = round41.g0 := rfl
  clear_value g0_41
  -- f1_41: loop iteration 41 output
  extract_lets -merge +onlyGivenNames f1_41 at hr
  have e_f1_41 : f1_41 = round41.f1 := rfl
  clear_value f1_41
  -- g1_41: loop iteration 41 output
  extract_lets -merge +onlyGivenNames g1_41 at hr
  have e_g1_41 : g1_41 = round41.g1 := rfl
  clear_value g1_41
  -- round42: loop iteration 42
  extract_lets -merge +onlyGivenNames round42 at hr
  have e_round42 : round42 = divsteps47Round ⟨a_41, cnt_41, b_41, f0_41, g0_41, f1_41, g1_41⟩ := rfl
  clear_value round42
  -- a_42: loop iteration 42 output
  extract_lets -merge +onlyGivenNames a_42 at hr
  have e_a_42 : a_42 = round42.a := rfl
  clear_value a_42
  -- cnt_42: loop iteration 42 output
  extract_lets -merge +onlyGivenNames cnt_42 at hr
  have e_cnt_42 : cnt_42 = round42.cnt := rfl
  clear_value cnt_42
  -- b_42: loop iteration 42 output
  extract_lets -merge +onlyGivenNames b_42 at hr
  have e_b_42 : b_42 = round42.b := rfl
  clear_value b_42
  -- f0_42: loop iteration 42 output
  extract_lets -merge +onlyGivenNames f0_42 at hr
  have e_f0_42 : f0_42 = round42.f0 := rfl
  clear_value f0_42
  -- g0_42: loop iteration 42 output
  extract_lets -merge +onlyGivenNames g0_42 at hr
  have e_g0_42 : g0_42 = round42.g0 := rfl
  clear_value g0_42
  -- f1_42: loop iteration 42 output
  extract_lets -merge +onlyGivenNames f1_42 at hr
  have e_f1_42 : f1_42 = round42.f1 := rfl
  clear_value f1_42
  -- g1_42: loop iteration 42 output
  extract_lets -merge +onlyGivenNames g1_42 at hr
  have e_g1_42 : g1_42 = round42.g1 := rfl
  clear_value g1_42
  -- round43: loop iteration 43
  extract_lets -merge +onlyGivenNames round43 at hr
  have e_round43 : round43 = divsteps47Round ⟨a_42, cnt_42, b_42, f0_42, g0_42, f1_42, g1_42⟩ := rfl
  clear_value round43
  -- a_43: loop iteration 43 output
  extract_lets -merge +onlyGivenNames a_43 at hr
  have e_a_43 : a_43 = round43.a := rfl
  clear_value a_43
  -- cnt_43: loop iteration 43 output
  extract_lets -merge +onlyGivenNames cnt_43 at hr
  have e_cnt_43 : cnt_43 = round43.cnt := rfl
  clear_value cnt_43
  -- b_43: loop iteration 43 output
  extract_lets -merge +onlyGivenNames b_43 at hr
  have e_b_43 : b_43 = round43.b := rfl
  clear_value b_43
  -- f0_43: loop iteration 43 output
  extract_lets -merge +onlyGivenNames f0_43 at hr
  have e_f0_43 : f0_43 = round43.f0 := rfl
  clear_value f0_43
  -- g0_43: loop iteration 43 output
  extract_lets -merge +onlyGivenNames g0_43 at hr
  have e_g0_43 : g0_43 = round43.g0 := rfl
  clear_value g0_43
  -- f1_43: loop iteration 43 output
  extract_lets -merge +onlyGivenNames f1_43 at hr
  have e_f1_43 : f1_43 = round43.f1 := rfl
  clear_value f1_43
  -- g1_43: loop iteration 43 output
  extract_lets -merge +onlyGivenNames g1_43 at hr
  have e_g1_43 : g1_43 = round43.g1 := rfl
  clear_value g1_43
  -- round44: loop iteration 44
  extract_lets -merge +onlyGivenNames round44 at hr
  have e_round44 : round44 = divsteps47Round ⟨a_43, cnt_43, b_43, f0_43, g0_43, f1_43, g1_43⟩ := rfl
  clear_value round44
  -- a_44: loop iteration 44 output
  extract_lets -merge +onlyGivenNames a_44 at hr
  have e_a_44 : a_44 = round44.a := rfl
  clear_value a_44
  -- cnt_44: loop iteration 44 output
  extract_lets -merge +onlyGivenNames cnt_44 at hr
  have e_cnt_44 : cnt_44 = round44.cnt := rfl
  clear_value cnt_44
  -- b_44: loop iteration 44 output
  extract_lets -merge +onlyGivenNames b_44 at hr
  have e_b_44 : b_44 = round44.b := rfl
  clear_value b_44
  -- f0_44: loop iteration 44 output
  extract_lets -merge +onlyGivenNames f0_44 at hr
  have e_f0_44 : f0_44 = round44.f0 := rfl
  clear_value f0_44
  -- g0_44: loop iteration 44 output
  extract_lets -merge +onlyGivenNames g0_44 at hr
  have e_g0_44 : g0_44 = round44.g0 := rfl
  clear_value g0_44
  -- f1_44: loop iteration 44 output
  extract_lets -merge +onlyGivenNames f1_44 at hr
  have e_f1_44 : f1_44 = round44.f1 := rfl
  clear_value f1_44
  -- g1_44: loop iteration 44 output
  extract_lets -merge +onlyGivenNames g1_44 at hr
  have e_g1_44 : g1_44 = round44.g1 := rfl
  clear_value g1_44
  -- round45: loop iteration 45
  extract_lets -merge +onlyGivenNames round45 at hr
  have e_round45 : round45 = divsteps47Round ⟨a_44, cnt_44, b_44, f0_44, g0_44, f1_44, g1_44⟩ := rfl
  clear_value round45
  -- a_45: loop iteration 45 output
  extract_lets -merge +onlyGivenNames a_45 at hr
  have e_a_45 : a_45 = round45.a := rfl
  clear_value a_45
  -- cnt_45: loop iteration 45 output
  extract_lets -merge +onlyGivenNames cnt_45 at hr
  have e_cnt_45 : cnt_45 = round45.cnt := rfl
  clear_value cnt_45
  -- b_45: loop iteration 45 output
  extract_lets -merge +onlyGivenNames b_45 at hr
  have e_b_45 : b_45 = round45.b := rfl
  clear_value b_45
  -- f0_45: loop iteration 45 output
  extract_lets -merge +onlyGivenNames f0_45 at hr
  have e_f0_45 : f0_45 = round45.f0 := rfl
  clear_value f0_45
  -- g0_45: loop iteration 45 output
  extract_lets -merge +onlyGivenNames g0_45 at hr
  have e_g0_45 : g0_45 = round45.g0 := rfl
  clear_value g0_45
  -- f1_45: loop iteration 45 output
  extract_lets -merge +onlyGivenNames f1_45 at hr
  have e_f1_45 : f1_45 = round45.f1 := rfl
  clear_value f1_45
  -- g1_45: loop iteration 45 output
  extract_lets -merge +onlyGivenNames g1_45 at hr
  have e_g1_45 : g1_45 = round45.g1 := rfl
  clear_value g1_45
  -- round46: loop iteration 46
  extract_lets -merge +onlyGivenNames round46 at hr
  have e_round46 : round46 = divsteps47Round ⟨a_45, cnt_45, b_45, f0_45, g0_45, f1_45, g1_45⟩ := rfl
  clear_value round46
  -- a_46: loop iteration 46 output
  extract_lets -merge +onlyGivenNames a_46 at hr
  have e_a_46 : a_46 = round46.a := rfl
  clear_value a_46
  -- cnt_46: loop iteration 46 output
  extract_lets -merge +onlyGivenNames cnt_46 at hr
  have e_cnt_46 : cnt_46 = round46.cnt := rfl
  clear_value cnt_46
  -- b_46: loop iteration 46 output
  extract_lets -merge +onlyGivenNames b_46 at hr
  have e_b_46 : b_46 = round46.b := rfl
  clear_value b_46
  -- f0_46: loop iteration 46 output
  extract_lets -merge +onlyGivenNames f0_46 at hr
  have e_f0_46 : f0_46 = round46.f0 := rfl
  clear_value f0_46
  -- g0_46: loop iteration 46 output
  extract_lets -merge +onlyGivenNames g0_46 at hr
  have e_g0_46 : g0_46 = round46.g0 := rfl
  clear_value g0_46
  -- f1_46: loop iteration 46 output
  extract_lets -merge +onlyGivenNames f1_46 at hr
  have e_f1_46 : f1_46 = round46.f1 := rfl
  clear_value f1_46
  -- g1_46: loop iteration 46 output
  extract_lets -merge +onlyGivenNames g1_46 at hr
  have e_g1_46 : g1_46 = round46.g1 := rfl
  clear_value g1_46
  -- round47: loop iteration 47
  extract_lets -merge +onlyGivenNames round47 at hr
  have e_round47 : round47 = divsteps47Round ⟨a_46, cnt_46, b_46, f0_46, g0_46, f1_46, g1_46⟩ := rfl
  clear_value round47
  -- f1_47: loop iteration 47 output
  extract_lets -merge +onlyGivenNames f1_47 at hr
  have e_f1_47 : f1_47 = round47.f1 := rfl
  clear_value f1_47
  -- g1_47: loop iteration 47 output
  extract_lets -merge +onlyGivenNames g1_47 at hr
  have e_g1_47 : g1_47 = round47.g1 := rfl
  clear_value g1_47
  subst hr
  -- BEGIN divsteps47 conclusion
  have hmatch1 : round1.Matches (forwardSteps 1 (ApproxState.initial a b)) := by
    rw [e_round1, forwardSteps]
    simpa only [e_a', e_cnt, e_b', e_f0, e_g0, e_f1, e_g1] using hmatch0.next
  clear hmatch0
  have hmatch2 : round2.Matches (forwardSteps 2 (ApproxState.initial a b)) := by
    rw [e_round2, forwardSteps]
    simpa only [e_a_1, e_cnt_1, e_b_1, e_f0_1, e_g0_1, e_f1_1, e_g1_1] using hmatch1.next
  clear hmatch1
  have hmatch3 : round3.Matches (forwardSteps 3 (ApproxState.initial a b)) := by
    rw [e_round3, forwardSteps]
    simpa only [e_a_2, e_cnt_2, e_b_2, e_f0_2, e_g0_2, e_f1_2, e_g1_2] using hmatch2.next
  clear hmatch2
  have hmatch4 : round4.Matches (forwardSteps 4 (ApproxState.initial a b)) := by
    rw [e_round4, forwardSteps]
    simpa only [e_a_3, e_cnt_3, e_b_3, e_f0_3, e_g0_3, e_f1_3, e_g1_3] using hmatch3.next
  clear hmatch3
  have hmatch5 : round5.Matches (forwardSteps 5 (ApproxState.initial a b)) := by
    rw [e_round5, forwardSteps]
    simpa only [e_a_4, e_cnt_4, e_b_4, e_f0_4, e_g0_4, e_f1_4, e_g1_4] using hmatch4.next
  clear hmatch4
  have hmatch6 : round6.Matches (forwardSteps 6 (ApproxState.initial a b)) := by
    rw [e_round6, forwardSteps]
    simpa only [e_a_5, e_cnt_5, e_b_5, e_f0_5, e_g0_5, e_f1_5, e_g1_5] using hmatch5.next
  clear hmatch5
  have hmatch7 : round7.Matches (forwardSteps 7 (ApproxState.initial a b)) := by
    rw [e_round7, forwardSteps]
    simpa only [e_a_6, e_cnt_6, e_b_6, e_f0_6, e_g0_6, e_f1_6, e_g1_6] using hmatch6.next
  clear hmatch6
  have hmatch8 : round8.Matches (forwardSteps 8 (ApproxState.initial a b)) := by
    rw [e_round8, forwardSteps]
    simpa only [e_a_7, e_cnt_7, e_b_7, e_f0_7, e_g0_7, e_f1_7, e_g1_7] using hmatch7.next
  clear hmatch7
  have hmatch9 : round9.Matches (forwardSteps 9 (ApproxState.initial a b)) := by
    rw [e_round9, forwardSteps]
    simpa only [e_a_8, e_cnt_8, e_b_8, e_f0_8, e_g0_8, e_f1_8, e_g1_8] using hmatch8.next
  clear hmatch8
  have hmatch10 : round10.Matches (forwardSteps 10 (ApproxState.initial a b)) := by
    rw [e_round10, forwardSteps]
    simpa only [e_a_9, e_cnt_9, e_b_9, e_f0_9, e_g0_9, e_f1_9, e_g1_9] using hmatch9.next
  clear hmatch9
  have hmatch11 : round11.Matches (forwardSteps 11 (ApproxState.initial a b)) := by
    rw [e_round11, forwardSteps]
    simpa only [e_a_10, e_cnt_10, e_b_10, e_f0_10, e_g0_10, e_f1_10, e_g1_10] using hmatch10.next
  clear hmatch10
  have hmatch12 : round12.Matches (forwardSteps 12 (ApproxState.initial a b)) := by
    rw [e_round12, forwardSteps]
    simpa only [e_a_11, e_cnt_11, e_b_11, e_f0_11, e_g0_11, e_f1_11, e_g1_11] using hmatch11.next
  clear hmatch11
  have hmatch13 : round13.Matches (forwardSteps 13 (ApproxState.initial a b)) := by
    rw [e_round13, forwardSteps]
    simpa only [e_a_12, e_cnt_12, e_b_12, e_f0_12, e_g0_12, e_f1_12, e_g1_12] using hmatch12.next
  clear hmatch12
  have hmatch14 : round14.Matches (forwardSteps 14 (ApproxState.initial a b)) := by
    rw [e_round14, forwardSteps]
    simpa only [e_a_13, e_cnt_13, e_b_13, e_f0_13, e_g0_13, e_f1_13, e_g1_13] using hmatch13.next
  clear hmatch13
  have hmatch15 : round15.Matches (forwardSteps 15 (ApproxState.initial a b)) := by
    rw [e_round15, forwardSteps]
    simpa only [e_a_14, e_cnt_14, e_b_14, e_f0_14, e_g0_14, e_f1_14, e_g1_14] using hmatch14.next
  clear hmatch14
  have hmatch16 : round16.Matches (forwardSteps 16 (ApproxState.initial a b)) := by
    rw [e_round16, forwardSteps]
    simpa only [e_a_15, e_cnt_15, e_b_15, e_f0_15, e_g0_15, e_f1_15, e_g1_15] using hmatch15.next
  clear hmatch15
  have hmatch17 : round17.Matches (forwardSteps 17 (ApproxState.initial a b)) := by
    rw [e_round17, forwardSteps]
    simpa only [e_a_16, e_cnt_16, e_b_16, e_f0_16, e_g0_16, e_f1_16, e_g1_16] using hmatch16.next
  clear hmatch16
  have hmatch18 : round18.Matches (forwardSteps 18 (ApproxState.initial a b)) := by
    rw [e_round18, forwardSteps]
    simpa only [e_a_17, e_cnt_17, e_b_17, e_f0_17, e_g0_17, e_f1_17, e_g1_17] using hmatch17.next
  clear hmatch17
  have hmatch19 : round19.Matches (forwardSteps 19 (ApproxState.initial a b)) := by
    rw [e_round19, forwardSteps]
    simpa only [e_a_18, e_cnt_18, e_b_18, e_f0_18, e_g0_18, e_f1_18, e_g1_18] using hmatch18.next
  clear hmatch18
  have hmatch20 : round20.Matches (forwardSteps 20 (ApproxState.initial a b)) := by
    rw [e_round20, forwardSteps]
    simpa only [e_a_19, e_cnt_19, e_b_19, e_f0_19, e_g0_19, e_f1_19, e_g1_19] using hmatch19.next
  clear hmatch19
  have hmatch21 : round21.Matches (forwardSteps 21 (ApproxState.initial a b)) := by
    rw [e_round21, forwardSteps]
    simpa only [e_a_20, e_cnt_20, e_b_20, e_f0_20, e_g0_20, e_f1_20, e_g1_20] using hmatch20.next
  clear hmatch20
  have hmatch22 : round22.Matches (forwardSteps 22 (ApproxState.initial a b)) := by
    rw [e_round22, forwardSteps]
    simpa only [e_a_21, e_cnt_21, e_b_21, e_f0_21, e_g0_21, e_f1_21, e_g1_21] using hmatch21.next
  clear hmatch21
  have hmatch23 : round23.Matches (forwardSteps 23 (ApproxState.initial a b)) := by
    rw [e_round23, forwardSteps]
    simpa only [e_a_22, e_cnt_22, e_b_22, e_f0_22, e_g0_22, e_f1_22, e_g1_22] using hmatch22.next
  clear hmatch22
  have hmatch24 : round24.Matches (forwardSteps 24 (ApproxState.initial a b)) := by
    rw [e_round24, forwardSteps]
    simpa only [e_a_23, e_cnt_23, e_b_23, e_f0_23, e_g0_23, e_f1_23, e_g1_23] using hmatch23.next
  clear hmatch23
  have hmatch25 : round25.Matches (forwardSteps 25 (ApproxState.initial a b)) := by
    rw [e_round25, forwardSteps]
    simpa only [e_a_24, e_cnt_24, e_b_24, e_f0_24, e_g0_24, e_f1_24, e_g1_24] using hmatch24.next
  clear hmatch24
  have hmatch26 : round26.Matches (forwardSteps 26 (ApproxState.initial a b)) := by
    rw [e_round26, forwardSteps]
    simpa only [e_a_25, e_cnt_25, e_b_25, e_f0_25, e_g0_25, e_f1_25, e_g1_25] using hmatch25.next
  clear hmatch25
  have hmatch27 : round27.Matches (forwardSteps 27 (ApproxState.initial a b)) := by
    rw [e_round27, forwardSteps]
    simpa only [e_a_26, e_cnt_26, e_b_26, e_f0_26, e_g0_26, e_f1_26, e_g1_26] using hmatch26.next
  clear hmatch26
  have hmatch28 : round28.Matches (forwardSteps 28 (ApproxState.initial a b)) := by
    rw [e_round28, forwardSteps]
    simpa only [e_a_27, e_cnt_27, e_b_27, e_f0_27, e_g0_27, e_f1_27, e_g1_27] using hmatch27.next
  clear hmatch27
  have hmatch29 : round29.Matches (forwardSteps 29 (ApproxState.initial a b)) := by
    rw [e_round29, forwardSteps]
    simpa only [e_a_28, e_cnt_28, e_b_28, e_f0_28, e_g0_28, e_f1_28, e_g1_28] using hmatch28.next
  clear hmatch28
  have hmatch30 : round30.Matches (forwardSteps 30 (ApproxState.initial a b)) := by
    rw [e_round30, forwardSteps]
    simpa only [e_a_29, e_cnt_29, e_b_29, e_f0_29, e_g0_29, e_f1_29, e_g1_29] using hmatch29.next
  clear hmatch29
  have hmatch31 : round31.Matches (forwardSteps 31 (ApproxState.initial a b)) := by
    rw [e_round31, forwardSteps]
    simpa only [e_a_30, e_cnt_30, e_b_30, e_f0_30, e_g0_30, e_f1_30, e_g1_30] using hmatch30.next
  clear hmatch30
  have hmatch32 : round32.Matches (forwardSteps 32 (ApproxState.initial a b)) := by
    rw [e_round32, forwardSteps]
    simpa only [e_a_31, e_cnt_31, e_b_31, e_f0_31, e_g0_31, e_f1_31, e_g1_31] using hmatch31.next
  clear hmatch31
  have hmatch33 : round33.Matches (forwardSteps 33 (ApproxState.initial a b)) := by
    rw [e_round33, forwardSteps]
    simpa only [e_a_32, e_cnt_32, e_b_32, e_f0_32, e_g0_32, e_f1_32, e_g1_32] using hmatch32.next
  clear hmatch32
  have hmatch34 : round34.Matches (forwardSteps 34 (ApproxState.initial a b)) := by
    rw [e_round34, forwardSteps]
    simpa only [e_a_33, e_cnt_33, e_b_33, e_f0_33, e_g0_33, e_f1_33, e_g1_33] using hmatch33.next
  clear hmatch33
  have hmatch35 : round35.Matches (forwardSteps 35 (ApproxState.initial a b)) := by
    rw [e_round35, forwardSteps]
    simpa only [e_a_34, e_cnt_34, e_b_34, e_f0_34, e_g0_34, e_f1_34, e_g1_34] using hmatch34.next
  clear hmatch34
  have hmatch36 : round36.Matches (forwardSteps 36 (ApproxState.initial a b)) := by
    rw [e_round36, forwardSteps]
    simpa only [e_a_35, e_cnt_35, e_b_35, e_f0_35, e_g0_35, e_f1_35, e_g1_35] using hmatch35.next
  clear hmatch35
  have hmatch37 : round37.Matches (forwardSteps 37 (ApproxState.initial a b)) := by
    rw [e_round37, forwardSteps]
    simpa only [e_a_36, e_cnt_36, e_b_36, e_f0_36, e_g0_36, e_f1_36, e_g1_36] using hmatch36.next
  clear hmatch36
  have hmatch38 : round38.Matches (forwardSteps 38 (ApproxState.initial a b)) := by
    rw [e_round38, forwardSteps]
    simpa only [e_a_37, e_cnt_37, e_b_37, e_f0_37, e_g0_37, e_f1_37, e_g1_37] using hmatch37.next
  clear hmatch37
  have hmatch39 : round39.Matches (forwardSteps 39 (ApproxState.initial a b)) := by
    rw [e_round39, forwardSteps]
    simpa only [e_a_38, e_cnt_38, e_b_38, e_f0_38, e_g0_38, e_f1_38, e_g1_38] using hmatch38.next
  clear hmatch38
  have hmatch40 : round40.Matches (forwardSteps 40 (ApproxState.initial a b)) := by
    rw [e_round40, forwardSteps]
    simpa only [e_a_39, e_cnt_39, e_b_39, e_f0_39, e_g0_39, e_f1_39, e_g1_39] using hmatch39.next
  clear hmatch39
  have hmatch41 : round41.Matches (forwardSteps 41 (ApproxState.initial a b)) := by
    rw [e_round41, forwardSteps]
    simpa only [e_a_40, e_cnt_40, e_b_40, e_f0_40, e_g0_40, e_f1_40, e_g1_40] using hmatch40.next
  clear hmatch40
  have hmatch42 : round42.Matches (forwardSteps 42 (ApproxState.initial a b)) := by
    rw [e_round42, forwardSteps]
    simpa only [e_a_41, e_cnt_41, e_b_41, e_f0_41, e_g0_41, e_f1_41, e_g1_41] using hmatch41.next
  clear hmatch41
  have hmatch43 : round43.Matches (forwardSteps 43 (ApproxState.initial a b)) := by
    rw [e_round43, forwardSteps]
    simpa only [e_a_42, e_cnt_42, e_b_42, e_f0_42, e_g0_42, e_f1_42, e_g1_42] using hmatch42.next
  clear hmatch42
  have hmatch44 : round44.Matches (forwardSteps 44 (ApproxState.initial a b)) := by
    rw [e_round44, forwardSteps]
    simpa only [e_a_43, e_cnt_43, e_b_43, e_f0_43, e_g0_43, e_f1_43, e_g1_43] using hmatch43.next
  clear hmatch43
  have hmatch45 : round45.Matches (forwardSteps 45 (ApproxState.initial a b)) := by
    rw [e_round45, forwardSteps]
    simpa only [e_a_44, e_cnt_44, e_b_44, e_f0_44, e_g0_44, e_f1_44, e_g1_44] using hmatch44.next
  clear hmatch44
  have hmatch46 : round46.Matches (forwardSteps 46 (ApproxState.initial a b)) := by
    rw [e_round46, forwardSteps]
    simpa only [e_a_45, e_cnt_45, e_b_45, e_f0_45, e_g0_45, e_f1_45, e_g1_45] using hmatch45.next
  clear hmatch45
  have hround47 : round47.Matches (forwardSteps 47 (ApproxState.initial a b)) := by
    rw [e_round47, forwardSteps]
    simpa only [e_a_46, e_cnt_46, e_b_46, e_f0_46, e_g0_46, e_f1_46, e_g1_46] using hmatch46.next
  clear hmatch46
  rw [forwardSteps_eq_approxSteps] at hround47
  exact finishDivsteps47 f1_47 g1_47 round47
    (approxSteps 47 (ApproxState.initial a b)) hround47 e_f1_47 e_g1_47
    (approxSteps_matrix_bounded 47 a b)
    (approxSteps_coeffSteps 47 (ApproxState.initial a b))
  -- END divsteps47 conclusion

end PastaAsm.AArch64
