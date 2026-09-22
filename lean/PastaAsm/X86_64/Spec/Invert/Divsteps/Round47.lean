/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.X86_64.Spec.Invert.Divsteps.Lemmas

/-!
# Correctness of one x86-64 final-tail divstep round

The instruction trace is generated from the mechanically factored assembly loop body.  The
handwritten conclusion relates its fixed-width state to the shared approximation recurrence.
-/

namespace PastaAsm.X86_64

open Spec.Invert Spec.Invert.Convergence

-- BEGIN divsteps47Round_spec statement
/-- One final-tail assembly iteration implements one exact nonnegative divstep and
one matching signed transition-row operation, modulo the 64-bit coefficient
bitpatterns. -/
theorem divsteps47Round_spec (s : Divsteps47State) (abstract : ApproxState)
    (hs : s.Bounded) (hstate : s.a = abstract.a ∧ s.b = abstract.b)
    (hmatrix : InvertMatrixRep ⟨s.f0, s.g0, s.f1, s.g1⟩ abstract.matrix) :
    ∀ s', s' = divsteps47Round s →
      s'.Bounded ∧ s'.a = (approxStep abstract).a ∧ s'.b = (approxStep abstract).b ∧
        InvertMatrixRep ⟨s'.f0, s'.g0, s'.f1, s'.g1⟩ (approxStep abstract).matrix := by
  intro s' hr
-- END divsteps47Round_spec statement
  -- generated skeleton for `divsteps47Round`: do not edit between the annotations
  unfold divsteps47Round at hr
  lift_lets -merge at hr
  -- a: input a
  extract_lets -merge +onlyGivenNames a at hr
  have e_a : a = s.a := rfl
  clear_value a
  have b_a : a < 2^64 := by rw [e_a]; exact hs.1
  -- b: input b
  extract_lets -merge +onlyGivenNames b at hr
  have e_b : b = s.b := rfl
  clear_value b
  have b_b : b < 2^64 := by rw [e_b]; exact hs.2.1
  -- f0: input f0
  extract_lets -merge +onlyGivenNames f0 at hr
  have e_f0 : f0 = s.f0 := rfl
  clear_value f0
  have b_f0 : f0 < 2^64 := by rw [e_f0]; exact hs.2.2.1
  -- g0: input g0
  extract_lets -merge +onlyGivenNames g0 at hr
  have e_g0 : g0 = s.g0 := rfl
  clear_value g0
  have b_g0 : g0 < 2^64 := by rw [e_g0]; exact hs.2.2.2.1
  -- f1: input f1
  extract_lets -merge +onlyGivenNames f1 at hr
  have e_f1 : f1 = s.f1 := rfl
  clear_value f1
  have b_f1 : f1 < 2^64 := by rw [e_f1]; exact hs.2.2.2.2.1
  -- g1: input g1
  extract_lets -merge +onlyGivenNames g1 at hr
  have e_g1 : g1 = s.g1 := rfl
  clear_value g1
  have b_g1 : g1 < 2^64 := by rw [e_g1]; exact hs.2.2.2.2.2.1
  -- t0: xor {t0:e}, {t0:e}
  extract_lets -merge +onlyGivenNames t0 cf ofl at hr
  have e_t0 : t0 = bitXor32 0 0 := rfl
  have e_cf : cf = 0 := rfl
  have e_ofl : ofl = 0 := rfl
  clear_value t0 cf ofl
  have b_t0 : t0 < 2^64 := by rw [e_t0]; exact bitXor32_lt _ _
  have b_cf : cf ≤ 1 := by rw [e_cf]; decide
  have b_ofl : ofl ≤ 1 := by rw [e_ofl]; decide
  -- zf: None
  extract_lets -merge +onlyGivenNames zf at hr
  have e_zf : zf = zeroFlag t0 := rfl
  clear_value zf
  have b_zf : zf ≤ 1 := by rw [e_zf]; exact zeroFlag_le_one _
  -- test: test {a}, 1
  extract_lets -merge +onlyGivenNames test cf_1 ofl_1 at hr
  have e_test : test = bitAnd a 1 := rfl
  have e_cf_1 : cf_1 = 0 := rfl
  have e_ofl_1 : ofl_1 = 0 := rfl
  clear_value test cf_1 ofl_1
  have b_test : test < 2^64 := by rw [e_test]; exact bitAnd_lt _ _
  have b_cf_1 : cf_1 ≤ 1 := by rw [e_cf_1]; decide
  have b_ofl_1 : ofl_1 ≤ 1 := by rw [e_ofl_1]; decide
  -- zf_1: None
  extract_lets -merge +onlyGivenNames zf_1 at hr
  have e_zf_1 : zf_1 = zeroFlag test := rfl
  clear_value zf_1
  have b_zf_1 : zf_1 ≤ 1 := by rw [e_zf_1]; exact zeroFlag_le_one _
  -- t1: mov {t1}, {b}
  extract_lets -merge +onlyGivenNames t1 at hr
  have e_t1 : t1 = b := rfl
  clear_value t1
  have b_t1 : t1 < 2^64 := by rw [e_t1]; exact b_b
  -- t0_1: cmovnz {t0}, {b}
  extract_lets -merge +onlyGivenNames t0_1 at hr
  have e_t0_1 : t0_1 = (if zf_1 = 0 then b else t0) := rfl
  clear_value t0_1
  have b_t0_1 : t0_1 < 2^64 := by
    rw [e_t0_1]; split <;> first | exact b_b | exact b_t0
  -- t1_1: sub {t1}, {a}
  extract_lets -merge +onlyGivenNames s t1_1 cf_2 at hr
  have e_t1_1 : t1_1 = (sbb t1 a 0).1 := rfl
  have e_cf_2 : cf_2 = (sbb t1 a 0).2 := rfl
  clear_value s t1_1 cf_2
  have l_t1_1 : t1_1 + a + 0 = t1 + 2^64 * cf_2 := by
    rw [e_t1_1, e_cf_2]; exact sbb_lin t1 a 0 b_t1 b_a (by decide)
  have b_t1_1 : t1_1 < 2^64 := by rw [e_t1_1]; exact sbb_value_lt t1 a 0
  have b_cf_2 : cf_2 ≤ 1 := by rw [e_cf_2]; exact sbb_borrow_le_one t1 a 0
  clear e_t1_1 e_cf_2
  -- BEGIN divsteps47Round clear initial flags
  clear e_cf e_ofl e_zf b_cf b_ofl b_zf e_cf_1 e_ofl_1 b_cf_1 b_ofl_1
    b_test b_zf_1 b_t1
  -- END divsteps47Round clear initial flags
  -- t2: mov {t2}, {a}
  extract_lets -merge +onlyGivenNames t2 at hr
  have e_t2 : t2 = a := rfl
  clear_value t2
  have b_t2 : t2 < 2^64 := by rw [e_t2]; exact b_a
  -- a_1: sub {a}, {t0}
  extract_lets -merge +onlyGivenNames s_1 a_1 cf_3 at hr
  have e_a_1 : a_1 = (sbb a t0_1 0).1 := rfl
  have e_cf_3 : cf_3 = (sbb a t0_1 0).2 := rfl
  clear_value s_1 a_1 cf_3
  have l_a_1 : a_1 + t0_1 + 0 = a + 2^64 * cf_3 := by
    rw [e_a_1, e_cf_3]; exact sbb_lin a t0_1 0 b_a b_t0_1 (by decide)
  have b_a_1 : a_1 < 2^64 := by rw [e_a_1]; exact sbb_value_lt a t0_1 0
  have b_cf_3 : cf_3 ≤ 1 := by rw [e_cf_3]; exact sbb_borrow_le_one a t0_1 0
  clear e_a_1 e_cf_3
  -- a_2: cmovc {a}, {t1}
  extract_lets -merge +onlyGivenNames a_2 at hr
  have e_a_2 : a_2 = (if cf_3 = 0 then a_1 else t1_1) := rfl
  clear_value a_2
  have b_a_2 : a_2 < 2^64 := by
    rw [e_a_2]; split <;> first | exact b_a_1 | exact b_t1_1
  -- b_1: cmovc {b}, {t2}
  extract_lets -merge +onlyGivenNames b_1 at hr
  have e_b_1 : b_1 = (if cf_3 = 0 then b else t2) := rfl
  clear_value b_1
  have b_b_1 : b_1 < 2^64 := by
    rw [e_b_1]; split <;> first | exact b_b | exact b_t2
  -- t0_2: mov {t0}, {f0}
  extract_lets -merge +onlyGivenNames t0_2 at hr
  have e_t0_2 : t0_2 = f0 := rfl
  clear_value t0_2
  have b_t0_2 : t0_2 < 2^64 := by rw [e_t0_2]; exact b_f0
  -- f0_1: cmovc {f0}, {f1}
  extract_lets -merge +onlyGivenNames f0_1 at hr
  have e_f0_1 : f0_1 = (if cf_3 = 0 then f0 else f1) := rfl
  clear_value f0_1
  have b_f0_1 : f0_1 < 2^64 := by
    rw [e_f0_1]; split <;> first | exact b_f0 | exact b_f1
  -- f1_1: cmovc {f1}, {t0}
  extract_lets -merge +onlyGivenNames f1_1 at hr
  have e_f1_1 : f1_1 = (if cf_3 = 0 then f1 else t0_2) := rfl
  clear_value f1_1
  have b_f1_1 : f1_1 < 2^64 := by
    rw [e_f1_1]; split <;> first | exact b_f1 | exact b_t0_2
  -- t1_2: mov {t1}, {g0}
  extract_lets -merge +onlyGivenNames t1_2 at hr
  have e_t1_2 : t1_2 = g0 := rfl
  clear_value t1_2
  have b_t1_2 : t1_2 < 2^64 := by rw [e_t1_2]; exact b_g0
  -- g0_1: cmovc {g0}, {g1}
  extract_lets -merge +onlyGivenNames g0_1 at hr
  have e_g0_1 : g0_1 = (if cf_3 = 0 then g0 else g1) := rfl
  clear_value g0_1
  have b_g0_1 : g0_1 < 2^64 := by
    rw [e_g0_1]; split <;> first | exact b_g0 | exact b_g1
  -- g1_1: cmovc {g1}, {t1}
  extract_lets -merge +onlyGivenNames g1_1 at hr
  have e_g1_1 : g1_1 = (if cf_3 = 0 then g1 else t1_2) := rfl
  clear_value g1_1
  have b_g1_1 : g1_1 < 2^64 := by
    rw [e_g1_1]; split <;> first | exact b_g1 | exact b_t1_2
  -- BEGIN divsteps47Round clear selected inputs
  clear hs b_b b_t0_1 b_t0_2 b_t1_2 b_f0 b_g0 b_f1 b_g1
  -- END divsteps47Round clear selected inputs
  -- t0_3: xor {t0:e}, {t0:e}
  extract_lets -merge +onlyGivenNames t0_3 cf_4 ofl_2 at hr
  have e_t0_3 : t0_3 = bitXor32 0 0 := rfl
  have e_cf_4 : cf_4 = 0 := rfl
  have e_ofl_2 : ofl_2 = 0 := rfl
  clear_value t0_3 cf_4 ofl_2
  have b_t0_3 : t0_3 < 2^64 := by rw [e_t0_3]; exact bitXor32_lt _ _
  have b_cf_4 : cf_4 ≤ 1 := by rw [e_cf_4]; decide
  have b_ofl_2 : ofl_2 ≤ 1 := by rw [e_ofl_2]; decide
  -- zf_2: None
  extract_lets -merge +onlyGivenNames zf_2 at hr
  have e_zf_2 : zf_2 = zeroFlag t0_3 := rfl
  clear_value zf_2
  have b_zf_2 : zf_2 ≤ 1 := by rw [e_zf_2]; exact zeroFlag_le_one _
  -- t1_3: xor {t1:e}, {t1:e}
  extract_lets -merge +onlyGivenNames t1_3 cf_5 ofl_3 at hr
  have e_t1_3 : t1_3 = bitXor32 0 0 := rfl
  have e_cf_5 : cf_5 = 0 := rfl
  have e_ofl_3 : ofl_3 = 0 := rfl
  clear_value t1_3 cf_5 ofl_3
  have b_t1_3 : t1_3 < 2^64 := by rw [e_t1_3]; exact bitXor32_lt _ _
  have b_cf_5 : cf_5 ≤ 1 := by rw [e_cf_5]; decide
  have b_ofl_3 : ofl_3 ≤ 1 := by rw [e_ofl_3]; decide
  -- zf_3: None
  extract_lets -merge +onlyGivenNames zf_3 at hr
  have e_zf_3 : zf_3 = zeroFlag t1_3 := rfl
  clear_value zf_3
  have b_zf_3 : zf_3 ≤ 1 := by rw [e_zf_3]; exact zeroFlag_le_one _
  -- a_3: shr {a}, 1
  extract_lets -merge +onlyGivenNames a_3 at hr
  have e_a_3 : a_3 = a_2 / 2^1 := rfl
  clear_value a_3
  have b_a_3 : a_3 < 2^63 := by
    rw [e_a_3]; exact Nat.div_lt_of_lt_mul (lt_of_lt_of_eq b_a_2 (by norm_num))
  -- test_1: test {t2}, 1
  extract_lets -merge +onlyGivenNames test_1 cf_6 ofl_4 at hr
  have e_test_1 : test_1 = bitAnd t2 1 := rfl
  have e_cf_6 : cf_6 = 0 := rfl
  have e_ofl_4 : ofl_4 = 0 := rfl
  clear_value test_1 cf_6 ofl_4
  have b_test_1 : test_1 < 2^64 := by rw [e_test_1]; exact bitAnd_lt _ _
  have b_cf_6 : cf_6 ≤ 1 := by rw [e_cf_6]; decide
  have b_ofl_4 : ofl_4 ≤ 1 := by rw [e_ofl_4]; decide
  -- zf_4: None
  extract_lets -merge +onlyGivenNames zf_4 at hr
  have e_zf_4 : zf_4 = zeroFlag test_1 := rfl
  clear_value zf_4
  have b_zf_4 : zf_4 ≤ 1 := by rw [e_zf_4]; exact zeroFlag_le_one _
  -- t0_4: cmovnz {t0}, {f1}
  extract_lets -merge +onlyGivenNames t0_4 at hr
  have e_t0_4 : t0_4 = (if zf_4 = 0 then f1_1 else t0_3) := rfl
  clear_value t0_4
  have b_t0_4 : t0_4 < 2^64 := by
    rw [e_t0_4]; split <;> first | exact b_f1_1 | exact b_t0_3
  -- t1_4: cmovnz {t1}, {g1}
  extract_lets -merge +onlyGivenNames t1_4 at hr
  have e_t1_4 : t1_4 = (if zf_4 = 0 then g1_1 else t1_3) := rfl
  clear_value t1_4
  have b_t1_4 : t1_4 < 2^64 := by
    rw [e_t1_4]; split <;> first | exact b_g1_1 | exact b_t1_3
  -- BEGIN divsteps47Round clear selector bounds
  have ht0 : t0 = 0 := by rw [e_t0]; rfl
  have ht0_3 : t0_3 = 0 := by rw [e_t0_3]; rfl
  have ht1_3 : t1_3 = 0 := by rw [e_t1_3]; rfl
  clear e_t0 b_t0 e_t0_3 b_t0_3 e_t1_3 b_t1_3
    e_cf_4 e_ofl_2 e_zf_2 b_cf_4 b_ofl_2 b_zf_2
    e_cf_5 e_ofl_3 e_zf_3 b_cf_5 b_ofl_3 b_zf_3
    e_cf_6 e_ofl_4 b_cf_6 b_ofl_4 b_a_2 b_test_1 b_zf_4
  -- END divsteps47Round clear selector bounds
  -- f1_2: add {f1}, {f1}
  extract_lets -merge +onlyGivenNames s_2 f1_2 cf_7 at hr
  have e_f1_2 : f1_2 = (addc f1_1 f1_1 0).1 := rfl
  have e_cf_7 : cf_7 = (addc f1_1 f1_1 0).2 := rfl
  clear_value s_2 f1_2 cf_7
  have l_f1_2 : f1_2 + 2^64 * cf_7 = f1_1 + f1_1 + 0 := by
    rw [e_f1_2, e_cf_7]; exact addc_lin f1_1 f1_1 0
  have b_f1_2 : f1_2 < 2^64 := by rw [e_f1_2]; exact addc_value_lt f1_1 f1_1 0
  have b_cf_7 : cf_7 ≤ 1 := by rw [e_cf_7]; exact addc_carry_le_one f1_1 f1_1 0 b_f1_1 b_f1_1 (by decide)
  clear e_f1_2 e_cf_7
  -- BEGIN divsteps47Round clear f1 arithmetic
  clear b_cf_7 b_f1_1
  -- END divsteps47Round clear f1 arithmetic
  -- g1_2: add {g1}, {g1}
  extract_lets -merge +onlyGivenNames s_3 g1_2 cf_8 at hr
  have e_g1_2 : g1_2 = (addc g1_1 g1_1 0).1 := rfl
  have e_cf_8 : cf_8 = (addc g1_1 g1_1 0).2 := rfl
  clear_value s_3 g1_2 cf_8
  have l_g1_2 : g1_2 + 2^64 * cf_8 = g1_1 + g1_1 + 0 := by
    rw [e_g1_2, e_cf_8]; exact addc_lin g1_1 g1_1 0
  have b_g1_2 : g1_2 < 2^64 := by rw [e_g1_2]; exact addc_value_lt g1_1 g1_1 0
  have b_cf_8 : cf_8 ≤ 1 := by rw [e_cf_8]; exact addc_carry_le_one g1_1 g1_1 0 b_g1_1 b_g1_1 (by decide)
  clear e_g1_2 e_cf_8
  -- BEGIN divsteps47Round clear g1 arithmetic
  clear b_cf_8 b_g1_1
  -- END divsteps47Round clear g1 arithmetic
  -- f0_2: sub {f0}, {t0}
  extract_lets -merge +onlyGivenNames s_4 f0_2 cf_9 at hr
  have e_f0_2 : f0_2 = (sbb f0_1 t0_4 0).1 := rfl
  have e_cf_9 : cf_9 = (sbb f0_1 t0_4 0).2 := rfl
  clear_value s_4 f0_2 cf_9
  have l_f0_2 : f0_2 + t0_4 + 0 = f0_1 + 2^64 * cf_9 := by
    rw [e_f0_2, e_cf_9]; exact sbb_lin f0_1 t0_4 0 b_f0_1 b_t0_4 (by decide)
  have b_f0_2 : f0_2 < 2^64 := by rw [e_f0_2]; exact sbb_value_lt f0_1 t0_4 0
  have b_cf_9 : cf_9 ≤ 1 := by rw [e_cf_9]; exact sbb_borrow_le_one f0_1 t0_4 0
  clear e_f0_2 e_cf_9
  -- BEGIN divsteps47Round clear f0 arithmetic
  clear b_cf_9 b_f0_1
  -- END divsteps47Round clear f0 arithmetic
  -- g0_2: sub {g0}, {t1}
  extract_lets -merge +onlyGivenNames s_5 g0_2 cf_10 at hr
  have e_g0_2 : g0_2 = (sbb g0_1 t1_4 0).1 := rfl
  have e_cf_10 : cf_10 = (sbb g0_1 t1_4 0).2 := rfl
  clear_value s_5 g0_2 cf_10
  have l_g0_2 : g0_2 + t1_4 + 0 = g0_1 + 2^64 * cf_10 := by
    rw [e_g0_2, e_cf_10]; exact sbb_lin g0_1 t1_4 0 b_g0_1 b_t1_4 (by decide)
  have b_g0_2 : g0_2 < 2^64 := by rw [e_g0_2]; exact sbb_value_lt g0_1 t1_4 0
  have b_cf_10 : cf_10 ≤ 1 := by rw [e_cf_10]; exact sbb_borrow_le_one g0_1 t1_4 0
  clear e_g0_2 e_cf_10
  -- BEGIN divsteps47Round clear g0 arithmetic
  clear b_cf_10 b_g0_1
  -- END divsteps47Round clear g0 arithmetic
  subst hr
  -- BEGIN divsteps47Round conclusion
  rcases hstate with ⟨hsa, hsb⟩
  rcases hmatrix with ⟨hf0, hg0, hf1, hg1⟩
  have ha_abs : a = abstract.a := e_a.trans hsa
  have hb_abs : b = abstract.b := e_b.trans hsb
  have hf0' : SignedWordRep f0 abstract.matrix.row0.left := by rwa [e_f0]
  have hg0' : SignedWordRep g0 abstract.matrix.row0.right := by rwa [e_g0]
  have hf1' : SignedWordRep f1 abstract.matrix.row1.left := by rwa [e_f1]
  have hg1' : SignedWordRep g1 abstract.matrix.row1.right := by rwa [e_g1]
  have hbounded : (⟨a_3, b_1, f0_2, g0_2, f1_2, g1_2, t0_4, t1_4, t2⟩ :
      Divsteps47State).Bounded :=
    ⟨b_a_3.trans (by norm_num), b_b_1, b_f0_2, b_g0_2, b_f1_2,
      b_g1_2, b_t0_4, b_t1_4, b_t2⟩
  clear * - hbounded ha_abs hb_abs hf0' hg0' hf1' hg1' ht0 ht0_3 ht1_3 b_a
    e_zf_1 e_test e_t0_1 l_a_1 b_a_1 b_cf_3 e_a_2 e_b_1 e_a_3
    e_zf_4 e_test_1 e_t2 e_f0_1 e_g0_1 e_f1_1 e_g1_1 e_t0_2 e_t1_2
    l_f0_2 l_g0_2 l_f1_2 l_g1_2 e_t0_4 e_t1_4 e_t1 l_t1_1
    b_t1_1 b_cf_2 b_f0_2 b_g0_2 b_f1_2 b_g1_2
  have hzf1 : zf_1 = zeroFlag (bitAnd a 1) := by rw [e_zf_1, e_test]
  have hzf4 : zf_4 = zeroFlag (bitAnd a 1) := by rw [e_zf_4, e_test_1, e_t2]
  have ht11 : t1_1 + a + 0 = b + 2^64 * cf_2 := by simpa [e_t1] using l_t1_1
  refine ⟨hbounded, divsteps47_trace_conclusion abstract ha_abs hb_abs
    hf0' hg0' hf1' hg1' ht0 b_a hzf1 hzf4 e_t0_1 l_a_1 b_a_1 b_cf_3
    ht11 b_t1_1 b_cf_2 e_a_2 (by simpa [e_t2] using e_b_1)
    e_f0_1 e_g0_1 (by simpa [e_t0_2] using e_f1_1)
    (by simpa [e_t1_2] using e_g1_1) e_a_3
    (by simpa [ht0_3, ht0] using e_t0_4) (by simpa [ht1_3, ht0] using e_t1_4)
    l_f0_2 b_f0_2 l_g0_2 b_g0_2 l_f1_2 b_f1_2 l_g1_2 b_g1_2⟩
  -- END divsteps47Round conclusion

end PastaAsm.X86_64
