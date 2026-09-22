/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.X86_64.Spec.Invert.Divsteps.Approximation
import PastaAsm.X86_64.Spec.Invert.Divsteps.Round31
import PastaAsm.X86_64.Spec.Invert.Divsteps.Round47

/-!
# Correctness of the x86-64 inversion divstep helpers

The proof traces in this file are generated from the x86-64 assembly.  The
handwritten annotations relate fixed-width wrapper states to the shared integer
row recurrence and approximation model.
-/

namespace PastaAsm.X86_64

open Spec.Invert Spec.Invert.Convergence

-- BEGIN divsteps47_spec statement
/-- The fixed final helper performs exactly 47 shared divsteps from identity rows.  Its returned
64-bit words represent the resulting signed matrix, whose rows have norm at most `2^47`. -/
theorem divsteps47_spec (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) (hodd : Odd b) :
    ∀ out, out = divsteps47 a b →
      let final := approxSteps 47 (ApproxState.initial a b)
      InvertMatrixRep out final.matrix ∧ Odd final.b ∧ final.matrix.Bounded (2^47) := by
  intro out hr
-- END divsteps47_spec statement
  -- generated skeleton for `divsteps47`: do not edit between the annotations
  unfold divsteps47 at hr
  lift_lets -merge at hr
  -- a': input a
  extract_lets -merge +onlyGivenNames a' at hr
  have e_a' : a' = a := rfl
  clear_value a'
  have b_a' : a' < 2^64 := by rw [e_a']; exact ha
  -- b': input b
  extract_lets -merge +onlyGivenNames b' at hr
  have e_b' : b' = b := rfl
  clear_value b'
  have b_b' : b' < 2^64 := by rw [e_b']; exact hb
  -- f0: input f0
  extract_lets -merge +onlyGivenNames f0 at hr
  have e_f0 : f0 = 1 := rfl
  clear_value f0
  have b_f0 : f0 < 2^64 := by rw [e_f0]; exact by decide
  -- g0: input g0
  extract_lets -merge +onlyGivenNames g0 at hr
  have e_g0 : g0 = 0 := rfl
  clear_value g0
  have b_g0 : g0 < 2^64 := by rw [e_g0]; exact by decide
  -- f1: input f1
  extract_lets -merge +onlyGivenNames f1 at hr
  have e_f1 : f1 = 0 := rfl
  clear_value f1
  have b_f1 : f1 < 2^64 := by rw [e_f1]; exact by decide
  -- g1: input g1
  extract_lets -merge +onlyGivenNames g1 at hr
  have e_g1 : g1 = 1 := rfl
  clear_value g1
  have b_g1 : g1 < 2^64 := by rw [e_g1]; exact by decide
  -- count: mov {count:e}, 47
  extract_lets -merge +onlyGivenNames count at hr
  have e_count : count = word32 47 := rfl
  clear_value count
  have b_count : count < 2^64 := by rw [e_count]; exact Nat.lt_trans (word32_lt _) (by decide)
  -- t0: unread scratch initialization
  extract_lets -merge +onlyGivenNames t0 at hr
  have e_t0 : t0 = 0 := rfl
  clear_value t0
  have b_t0 : t0 < 2^64 := by rw [e_t0]; decide
  -- t1: unread scratch initialization
  extract_lets -merge +onlyGivenNames t1 at hr
  have e_t1 : t1 = 0 := rfl
  clear_value t1
  have b_t1 : t1 < 2^64 := by rw [e_t1]; decide
  -- t2: unread scratch initialization
  extract_lets -merge +onlyGivenNames t2 at hr
  have e_t2 : t2 = 0 := rfl
  clear_value t2
  have b_t2 : t2 < 2^64 := by rw [e_t2]; decide
  -- loop: factored fixed 47-iteration loop
  extract_lets -merge +onlyGivenNames loop at hr
  have e_loop : loop = iterate divsteps47Round 47 ⟨a', b', f0, g0, f1, g1, t0, t1, t2⟩ := rfl
  clear_value loop
  -- a_1: fixed loop output
  extract_lets -merge +onlyGivenNames a_1 at hr
  have e_a_1 : a_1 = loop.a := rfl
  clear_value a_1
  -- b_1: fixed loop output
  extract_lets -merge +onlyGivenNames b_1 at hr
  have e_b_1 : b_1 = loop.b := rfl
  clear_value b_1
  -- f0_1: fixed loop output
  extract_lets -merge +onlyGivenNames f0_1 at hr
  have e_f0_1 : f0_1 = loop.f0 := rfl
  clear_value f0_1
  -- g0_1: fixed loop output
  extract_lets -merge +onlyGivenNames g0_1 at hr
  have e_g0_1 : g0_1 = loop.g0 := rfl
  clear_value g0_1
  -- f1_1: fixed loop output
  extract_lets -merge +onlyGivenNames f1_1 at hr
  have e_f1_1 : f1_1 = loop.f1 := rfl
  clear_value f1_1
  -- g1_1: fixed loop output
  extract_lets -merge +onlyGivenNames g1_1 at hr
  have e_g1_1 : g1_1 = loop.g1 := rfl
  clear_value g1_1
  -- t0_1: fixed loop output
  extract_lets -merge +onlyGivenNames t0_1 at hr
  have e_t0_1 : t0_1 = loop.t0 := rfl
  clear_value t0_1
  -- t1_1: fixed loop output
  extract_lets -merge +onlyGivenNames t1_1 at hr
  have e_t1_1 : t1_1 = loop.t1 := rfl
  clear_value t1_1
  -- t2_1: fixed loop output
  extract_lets -merge +onlyGivenNames t2_1 at hr
  have e_t2_1 : t2_1 = loop.t2 := rfl
  clear_value t2_1
  subst hr
  -- BEGIN divsteps47 conclusion
  have h_f1 : f1 = g0 := by omega
  have h_g1 : g1 = f0 := by omega
  have h_t0 : t0 = g0 := by omega
  have h_t1 : t1 = g0 := by omega
  have h_t2 : t2 = g0 := by omega
  simp only [h_f1, h_g1, h_t0, h_t1, h_t2] at e_loop
  have hs0 : (⟨a', b', f0, g0, g0, f0, g0, g0, g0⟩ : Divsteps47State).Bounded := by
    exact ⟨b_a', b_b', b_f0, b_g0, b_g0, b_f0, b_g0, b_g0, b_g0⟩
  have hm0 : InvertMatrixRep ⟨f0, g0, g0, f0⟩ identityMatrix := by
    simp [InvertMatrixRep, e_f0, e_g0, identityMatrix]
  have hloop := divsteps47_iterate_spec 47
    (⟨a', b', f0, g0, g0, f0, g0, g0, g0⟩ : Divsteps47State)
    (ApproxState.initial a b) hs0
    (by simp [ApproxState.initial, e_a', e_b']) hm0
    (by
      intro state abstract hstate hvalues hmatrix
      exact divsteps47Round_spec state abstract hstate hvalues hmatrix
        (divsteps47Round state) rfl)
  rw [← e_loop] at hloop
  rcases hloop with ⟨_, _, _, hm⟩
  refine ⟨?_, approxSteps_second_odd 47 (ApproxState.initial a b) ?_,
    approxSteps_matrix_bounded 47 a b⟩
  · simpa [e_f0_1, e_g0_1, e_f1_1, e_g1_1] using hm
  · simpa [ApproxState.initial] using hodd
  -- END divsteps47 conclusion

-- BEGIN divsteps31_spec statement
/-- The packed approximation helper performs exactly 31 shared divsteps on `semolinaApprox`.
Its returned words represent the resulting signed matrix with the full `2^31` row bound. -/
theorem divsteps31_spec (a b : Limbs) (ha : a.Bounded) (hb : b.Bounded) (hodd : Odd b.toNat) :
    ∀ out, out = divsteps31 a b →
      InvertMatrixRep out (semolinaShort a.toNat b.toNat).matrix ∧
        (semolinaShort a.toNat b.toNat).matrix.Bounded (2^31) := by
  intro out hr
-- END divsteps31_spec statement
  -- generated skeleton for `divsteps31`: do not edit between the annotations
  unfold divsteps31 at hr
  lift_lets -merge at hr
  -- a0: input a0
  extract_lets -merge +onlyGivenNames a0 at hr
  have e_a0 : a0 = a.l0 := rfl
  clear_value a0
  have b_a0 : a0 < 2^64 := by rw [e_a0]; exact ha.1
  -- a1: input a1
  extract_lets -merge +onlyGivenNames a1 at hr
  have e_a1 : a1 = a.l1 := rfl
  clear_value a1
  have b_a1 : a1 < 2^64 := by rw [e_a1]; exact ha.2.1
  -- a2: input a2
  extract_lets -merge +onlyGivenNames a2 at hr
  have e_a2 : a2 = a.l2 := rfl
  clear_value a2
  have b_a2 : a2 < 2^64 := by rw [e_a2]; exact ha.2.2.1
  -- a3: input a3
  extract_lets -merge +onlyGivenNames a3 at hr
  have e_a3 : a3 = a.l3 := rfl
  clear_value a3
  have b_a3 : a3 < 2^64 := by rw [e_a3]; exact ha.2.2.2
  -- b0: input b0
  extract_lets -merge +onlyGivenNames b0 at hr
  have e_b0 : b0 = b.l0 := rfl
  clear_value b0
  have b_b0 : b0 < 2^64 := by rw [e_b0]; exact hb.1
  -- b1: input b1
  extract_lets -merge +onlyGivenNames b1 at hr
  have e_b1 : b1 = b.l1 := rfl
  clear_value b1
  have b_b1 : b1 < 2^64 := by rw [e_b1]; exact hb.2.1
  -- b2: input b2
  extract_lets -merge +onlyGivenNames b2 at hr
  have e_b2 : b2 = b.l2 := rfl
  clear_value b2
  have b_b2 : b2 < 2^64 := by rw [e_b2]; exact hb.2.2.1
  -- b3: input b3
  extract_lets -merge +onlyGivenNames b3 at hr
  have e_b3 : b3 = b.l3 := rfl
  clear_value b3
  have b_b3 : b3 < 2^64 := by rw [e_b3]; exact hb.2.2.2
  -- t: mov {t}, {a3}
  extract_lets -merge +onlyGivenNames t at hr
  have e_t : t = a3 := rfl
  clear_value t
  have b_t : t < 2^64 := by rw [e_t]; exact b_a3
  -- t_1: or {t}, {b3}
  extract_lets -merge +onlyGivenNames t_1 cf ofl at hr
  have e_t_1 : t_1 = bitOr t b3 := rfl
  have e_cf : cf = 0 := rfl
  have e_ofl : ofl = 0 := rfl
  clear_value t_1 cf ofl
  have b_t_1 : t_1 < 2^64 := by rw [e_t_1]; exact bitOr_lt _ _
  have b_cf : cf ≤ 1 := by rw [e_cf]; decide
  have b_ofl : ofl ≤ 1 := by rw [e_ofl]; decide
  -- zf: None
  extract_lets -merge +onlyGivenNames zf at hr
  have e_zf : zf = zeroFlag t_1 := rfl
  clear_value zf
  have b_zf : zf ≤ 1 := by rw [e_zf]; exact zeroFlag_le_one _
  -- a3_1: cmovz {a3}, {a2}
  extract_lets -merge +onlyGivenNames a3_1 at hr
  have e_a3_1 : a3_1 = (if zf = 0 then a3 else a2) := rfl
  clear_value a3_1
  have b_a3_1 : a3_1 < 2^64 := by
    rw [e_a3_1]; split <;> first | exact b_a3 | exact b_a2
  -- b3_1: cmovz {b3}, {b2}
  extract_lets -merge +onlyGivenNames b3_1 at hr
  have e_b3_1 : b3_1 = (if zf = 0 then b3 else b2) := rfl
  clear_value b3_1
  have b_b3_1 : b3_1 < 2^64 := by
    rw [e_b3_1]; split <;> first | exact b_b3 | exact b_b2
  -- a2_1: cmovz {a2}, {a1}
  extract_lets -merge +onlyGivenNames a2_1 at hr
  have e_a2_1 : a2_1 = (if zf = 0 then a2 else a1) := rfl
  clear_value a2_1
  have b_a2_1 : a2_1 < 2^64 := by
    rw [e_a2_1]; split <;> first | exact b_a2 | exact b_a1
  -- b2_1: cmovz {b2}, {b1}
  extract_lets -merge +onlyGivenNames b2_1 at hr
  have e_b2_1 : b2_1 = (if zf = 0 then b2 else b1) := rfl
  clear_value b2_1
  have b_b2_1 : b2_1 < 2^64 := by
    rw [e_b2_1]; split <;> first | exact b_b2 | exact b_b1
  -- a1_1: cmovz {a1}, {a0}
  extract_lets -merge +onlyGivenNames a1_1 at hr
  have e_a1_1 : a1_1 = (if zf = 0 then a1 else a0) := rfl
  clear_value a1_1
  have b_a1_1 : a1_1 < 2^64 := by
    rw [e_a1_1]; split <;> first | exact b_a1 | exact b_a0
  -- b1_1: cmovz {b1}, {b0}
  extract_lets -merge +onlyGivenNames b1_1 at hr
  have e_b1_1 : b1_1 = (if zf = 0 then b1 else b0) := rfl
  clear_value b1_1
  have b_b1_1 : b1_1 < 2^64 := by
    rw [e_b1_1]; split <;> first | exact b_b1 | exact b_b0
  -- t_2: mov {t}, {a3}
  extract_lets -merge +onlyGivenNames t_2 at hr
  have e_t_2 : t_2 = a3_1 := rfl
  clear_value t_2
  have b_t_2 : t_2 < 2^64 := by rw [e_t_2]; exact b_a3_1
  -- t_3: or {t}, {b3}
  extract_lets -merge +onlyGivenNames t_3 cf_1 ofl_1 at hr
  have e_t_3 : t_3 = bitOr t_2 b3_1 := rfl
  have e_cf_1 : cf_1 = 0 := rfl
  have e_ofl_1 : ofl_1 = 0 := rfl
  clear_value t_3 cf_1 ofl_1
  have b_t_3 : t_3 < 2^64 := by rw [e_t_3]; exact bitOr_lt _ _
  have b_cf_1 : cf_1 ≤ 1 := by rw [e_cf_1]; decide
  have b_ofl_1 : ofl_1 ≤ 1 := by rw [e_ofl_1]; decide
  -- zf_1: None
  extract_lets -merge +onlyGivenNames zf_1 at hr
  have e_zf_1 : zf_1 = zeroFlag t_3 := rfl
  clear_value zf_1
  have b_zf_1 : zf_1 ≤ 1 := by rw [e_zf_1]; exact zeroFlag_le_one _
  -- a3_2: cmovz {a3}, {a2}
  extract_lets -merge +onlyGivenNames a3_2 at hr
  have e_a3_2 : a3_2 = (if zf_1 = 0 then a3_1 else a2_1) := rfl
  clear_value a3_2
  have b_a3_2 : a3_2 < 2^64 := by
    rw [e_a3_2]; split <;> first | exact b_a3_1 | exact b_a2_1
  -- b3_2: cmovz {b3}, {b2}
  extract_lets -merge +onlyGivenNames b3_2 at hr
  have e_b3_2 : b3_2 = (if zf_1 = 0 then b3_1 else b2_1) := rfl
  clear_value b3_2
  have b_b3_2 : b3_2 < 2^64 := by
    rw [e_b3_2]; split <;> first | exact b_b3_1 | exact b_b2_1
  -- a2_2: cmovz {a2}, {a1}
  extract_lets -merge +onlyGivenNames a2_2 at hr
  have e_a2_2 : a2_2 = (if zf_1 = 0 then a2_1 else a1_1) := rfl
  clear_value a2_2
  have b_a2_2 : a2_2 < 2^64 := by
    rw [e_a2_2]; split <;> first | exact b_a2_1 | exact b_a1_1
  -- b2_2: cmovz {b2}, {b1}
  extract_lets -merge +onlyGivenNames b2_2 at hr
  have e_b2_2 : b2_2 = (if zf_1 = 0 then b2_1 else b1_1) := rfl
  clear_value b2_2
  have b_b2_2 : b2_2 < 2^64 := by
    rw [e_b2_2]; split <;> first | exact b_b2_1 | exact b_b1_1
  -- t_4: mov {t}, {a3}
  extract_lets -merge +onlyGivenNames t_4 at hr
  have e_t_4 : t_4 = a3_2 := rfl
  clear_value t_4
  have b_t_4 : t_4 < 2^64 := by rw [e_t_4]; exact b_a3_2
  -- t_5: or {t}, {b3}
  extract_lets -merge +onlyGivenNames t_5 cf_2 ofl_2 at hr
  have e_t_5 : t_5 = bitOr t_4 b3_2 := rfl
  have e_cf_2 : cf_2 = 0 := rfl
  have e_ofl_2 : ofl_2 = 0 := rfl
  clear_value t_5 cf_2 ofl_2
  have b_t_5 : t_5 < 2^64 := by rw [e_t_5]; exact bitOr_lt _ _
  have b_cf_2 : cf_2 ≤ 1 := by rw [e_cf_2]; decide
  have b_ofl_2 : ofl_2 ≤ 1 := by rw [e_ofl_2]; decide
  -- zf_2: None
  extract_lets -merge +onlyGivenNames zf_2 at hr
  have e_zf_2 : zf_2 = zeroFlag t_5 := rfl
  clear_value zf_2
  have b_zf_2 : zf_2 ≤ 1 := by rw [e_zf_2]; exact zeroFlag_le_one _
  -- rcx: bsr rcx, {t}
  extract_lets -merge +onlyGivenNames rcx at hr
  have e_rcx : rcx = (bsr t_5).getD 0 := rfl
  clear_value rcx
  have b_rcx : rcx < 2^64 := by rw [e_rcx]; exact bsr_getD_lt _
  -- zf_3: None
  extract_lets -merge +onlyGivenNames zf_3 at hr
  have e_zf_3 : zf_3 = zeroFlag t_5 := rfl
  clear_value zf_3
  have b_zf_3 : zf_3 ≤ 1 := by rw [e_zf_3]; exact zeroFlag_le_one _
  -- rcx_1: lea rcx, [rcx + 1]
  extract_lets -merge +onlyGivenNames rcx_1 at hr
  have e_rcx_1 : rcx_1 = lea rcx 1 := rfl
  clear_value rcx_1
  have b_rcx_1 : rcx_1 < 2^64 := by rw [e_rcx_1]; exact word_lt _
  -- a3_3: cmovz {a3}, {a0}
  extract_lets -merge +onlyGivenNames a3_3 at hr
  have e_a3_3 : a3_3 = (if zf_3 = 0 then a3_2 else a0) := rfl
  clear_value a3_3
  have b_a3_3 : a3_3 < 2^64 := by
    rw [e_a3_3]; split <;> first | exact b_a3_2 | exact b_a0
  -- b3_3: cmovz {b3}, {b0}
  extract_lets -merge +onlyGivenNames b3_3 at hr
  have e_b3_3 : b3_3 = (if zf_3 = 0 then b3_2 else b0) := rfl
  clear_value b3_3
  have b_b3_3 : b3_3 < 2^64 := by
    rw [e_b3_3]; split <;> first | exact b_b3_2 | exact b_b0
  -- rcx_2: cmovz rcx, {t}
  extract_lets -merge +onlyGivenNames rcx_2 at hr
  have e_rcx_2 : rcx_2 = (if zf_3 = 0 then rcx_1 else t_5) := rfl
  clear_value rcx_2
  have b_rcx_2 : rcx_2 < 2^64 := by
    rw [e_rcx_2]; split <;> first | exact b_rcx_1 | exact b_t_5
  -- s: neg rcx
  extract_lets -merge +onlyGivenNames s rcx_3 cf_3 at hr
  have e_rcx_3 : rcx_3 = (neg rcx_2).1 := rfl
  have e_cf_3 : cf_3 = (neg rcx_2).2 := rfl
  clear_value s rcx_3 cf_3
  have b_rcx_3 : rcx_3 < 2^64 := by rw [e_rcx_3]; exact sbb_value_lt 0 rcx_2 0
  have b_cf_3 : cf_3 ≤ 1 := by
    rw [e_cf_3]; simp only [neg]; split <;> omega
  -- a3_4: shld {a3}, {a2}, cl
  extract_lets -merge +onlyGivenNames a3_4 at hr
  have e_a3_4 : a3_4 = shld a3_3 a2_2 rcx_3 := rfl
  clear_value a3_4
  have b_a3_4 : a3_4 < 2^64 := by rw [e_a3_4]; exact shld_lt _ _ _
  -- b3_4: shld {b3}, {b2}, cl
  extract_lets -merge +onlyGivenNames b3_4 at hr
  have e_b3_4 : b3_4 = shld b3_3 b2_2 rcx_3 := rfl
  clear_value b3_4
  have b_b3_4 : b3_4 < 2^64 := by rw [e_b3_4]; exact shld_lt _ _ _
  -- t_6: mov {t:e}, 0x7fffffff
  extract_lets -merge +onlyGivenNames t_6 at hr
  have e_t_6 : t_6 = word32 2147483647 := rfl
  clear_value t_6
  have b_t_6 : t_6 < 2^64 := by rw [e_t_6]; exact Nat.lt_trans (word32_lt _) (by decide)
  -- a0_1: and {a0}, {t}
  extract_lets -merge +onlyGivenNames a0_1 cf_4 ofl_3 at hr
  have e_a0_1 : a0_1 = bitAnd a0 t_6 := rfl
  have e_cf_4 : cf_4 = 0 := rfl
  have e_ofl_3 : ofl_3 = 0 := rfl
  clear_value a0_1 cf_4 ofl_3
  have b_a0_1 : a0_1 < 2^64 := by rw [e_a0_1]; exact bitAnd_lt _ _
  have b_cf_4 : cf_4 ≤ 1 := by rw [e_cf_4]; decide
  have b_ofl_3 : ofl_3 ≤ 1 := by rw [e_ofl_3]; decide
  -- zf_4: None
  extract_lets -merge +onlyGivenNames zf_4 at hr
  have e_zf_4 : zf_4 = zeroFlag a0_1 := rfl
  clear_value zf_4
  have b_zf_4 : zf_4 ≤ 1 := by rw [e_zf_4]; exact zeroFlag_le_one _
  -- b0_1: and {b0}, {t}
  extract_lets -merge +onlyGivenNames b0_1 cf_5 ofl_4 at hr
  have e_b0_1 : b0_1 = bitAnd b0 t_6 := rfl
  have e_cf_5 : cf_5 = 0 := rfl
  have e_ofl_4 : ofl_4 = 0 := rfl
  clear_value b0_1 cf_5 ofl_4
  have b_b0_1 : b0_1 < 2^64 := by rw [e_b0_1]; exact bitAnd_lt _ _
  have b_cf_5 : cf_5 ≤ 1 := by rw [e_cf_5]; decide
  have b_ofl_4 : ofl_4 ≤ 1 := by rw [e_ofl_4]; decide
  -- zf_5: None
  extract_lets -merge +onlyGivenNames zf_5 at hr
  have e_zf_5 : zf_5 = zeroFlag b0_1 := rfl
  clear_value zf_5
  have b_zf_5 : zf_5 ≤ 1 := by rw [e_zf_5]; exact zeroFlag_le_one _
  -- t_7: not {t}
  extract_lets -merge +onlyGivenNames t_7 at hr
  have e_t_7 : t_7 = bitNot t_6 := rfl
  clear_value t_7
  have b_t_7 : t_7 < 2^64 := by rw [e_t_7]; exact bitNot_lt _
  -- a3_5: and {a3}, {t}
  extract_lets -merge +onlyGivenNames a3_5 cf_6 ofl_5 at hr
  have e_a3_5 : a3_5 = bitAnd a3_4 t_7 := rfl
  have e_cf_6 : cf_6 = 0 := rfl
  have e_ofl_5 : ofl_5 = 0 := rfl
  clear_value a3_5 cf_6 ofl_5
  have b_a3_5 : a3_5 < 2^64 := by rw [e_a3_5]; exact bitAnd_lt _ _
  have b_cf_6 : cf_6 ≤ 1 := by rw [e_cf_6]; decide
  have b_ofl_5 : ofl_5 ≤ 1 := by rw [e_ofl_5]; decide
  -- zf_6: None
  extract_lets -merge +onlyGivenNames zf_6 at hr
  have e_zf_6 : zf_6 = zeroFlag a3_5 := rfl
  clear_value zf_6
  have b_zf_6 : zf_6 ≤ 1 := by rw [e_zf_6]; exact zeroFlag_le_one _
  -- b3_5: and {b3}, {t}
  extract_lets -merge +onlyGivenNames b3_5 cf_7 ofl_6 at hr
  have e_b3_5 : b3_5 = bitAnd b3_4 t_7 := rfl
  have e_cf_7 : cf_7 = 0 := rfl
  have e_ofl_6 : ofl_6 = 0 := rfl
  clear_value b3_5 cf_7 ofl_6
  have b_b3_5 : b3_5 < 2^64 := by rw [e_b3_5]; exact bitAnd_lt _ _
  have b_cf_7 : cf_7 ≤ 1 := by rw [e_cf_7]; decide
  have b_ofl_6 : ofl_6 ≤ 1 := by rw [e_ofl_6]; decide
  -- zf_7: None
  extract_lets -merge +onlyGivenNames zf_7 at hr
  have e_zf_7 : zf_7 = zeroFlag b3_5 := rfl
  clear_value zf_7
  have b_zf_7 : zf_7 ≤ 1 := by rw [e_zf_7]; exact zeroFlag_le_one _
  -- a0_2: or {a0}, {a3}
  extract_lets -merge +onlyGivenNames a0_2 cf_8 ofl_7 at hr
  have e_a0_2 : a0_2 = bitOr a0_1 a3_5 := rfl
  have e_cf_8 : cf_8 = 0 := rfl
  have e_ofl_7 : ofl_7 = 0 := rfl
  clear_value a0_2 cf_8 ofl_7
  have b_a0_2 : a0_2 < 2^64 := by rw [e_a0_2]; exact bitOr_lt _ _
  have b_cf_8 : cf_8 ≤ 1 := by rw [e_cf_8]; decide
  have b_ofl_7 : ofl_7 ≤ 1 := by rw [e_ofl_7]; decide
  -- zf_8: None
  extract_lets -merge +onlyGivenNames zf_8 at hr
  have e_zf_8 : zf_8 = zeroFlag a0_2 := rfl
  clear_value zf_8
  have b_zf_8 : zf_8 ≤ 1 := by rw [e_zf_8]; exact zeroFlag_le_one _
  -- b0_2: or {b0}, {b3}
  extract_lets -merge +onlyGivenNames b0_2 cf_9 ofl_8 at hr
  have e_b0_2 : b0_2 = bitOr b0_1 b3_5 := rfl
  have e_cf_9 : cf_9 = 0 := rfl
  have e_ofl_8 : ofl_8 = 0 := rfl
  clear_value b0_2 cf_9 ofl_8
  have b_b0_2 : b0_2 < 2^64 := by rw [e_b0_2]; exact bitOr_lt _ _
  have b_cf_9 : cf_9 ≤ 1 := by rw [e_cf_9]; decide
  have b_ofl_8 : ofl_8 ≤ 1 := by rw [e_ofl_8]; decide
  -- zf_9: None
  extract_lets -merge +onlyGivenNames zf_9 at hr
  have e_zf_9 : zf_9 = zeroFlag b0_2 := rfl
  clear_value zf_9
  have b_zf_9 : zf_9 ≤ 1 := by rw [e_zf_9]; exact zeroFlag_le_one _
  -- a1_2: movabs {a1}, 0x7fffffff80000000
  extract_lets -merge +onlyGivenNames a1_2 at hr
  have e_a1_2 : a1_2 = 9223372034707292160 := rfl
  clear_value a1_2
  have b_a1_2 : a1_2 < 2^64 := by rw [e_a1_2]; decide
  -- a2_3: movabs {a2}, 0x800000007fffffff
  extract_lets -merge +onlyGivenNames a2_3 at hr
  have e_a2_3 : a2_3 = 9223372039002259455 := rfl
  clear_value a2_3
  have b_a2_3 : a2_3 < 2^64 := by rw [e_a2_3]; decide
  -- a3_6: movabs {a3}, 0x7fffffff7fffffff
  extract_lets -merge +onlyGivenNames a3_6 at hr
  have e_a3_6 : a3_6 = 9223372034707292159 := rfl
  clear_value a3_6
  have b_a3_6 : a3_6 < 2^64 := by rw [e_a3_6]; decide
  -- rcx_4: mov ecx, 31
  extract_lets -merge +onlyGivenNames rcx_4 at hr
  have e_rcx_4 : rcx_4 = word32 31 := rfl
  clear_value rcx_4
  have b_rcx_4 : rcx_4 < 2^64 := by rw [e_rcx_4]; exact Nat.lt_trans (word32_lt _) (by decide)
  -- loop: factored fixed 31-iteration loop
  extract_lets -merge +onlyGivenNames loop at hr
  have e_loop : loop = iterate divsteps31Round 31 ⟨a0_2, a1_2, a2_3, a3_6, b0_2, b1_1, b2_2, b3_5, t_7⟩ := rfl
  clear_value loop
  -- BEGIN divsteps31 loop setup
  have hinit : (a0_2, b0_2) = divsteps31Init a b := by
    simp only [divsteps31Init, e_a0_2, e_b0_2, e_a0_1, e_b0_1, e_a3_5, e_b3_5,
      e_a3_4, e_b3_4, e_rcx_3, e_rcx_2, e_rcx_1, e_rcx, e_t_7, e_t_6, e_a3_3,
      e_b3_3, e_zf_3, e_t_5, e_t_4, e_a3_2, e_b3_2, e_a2_2, e_b2_2, e_zf_1,
      e_t_3, e_t_2, e_a3_1, e_b3_1, e_a2_1, e_b2_1, e_a1_1, e_b1_1, e_zf,
      e_t_1, e_t, e_a0, e_a1, e_a2, e_a3, e_b0, e_b1, e_b2, e_b3]
    rfl
  have happ : (a0_2, b0_2) = semolinaApprox a.toNat b.toNat :=
    hinit.trans (divsteps31Init_spec a b ha hb)
  let abstract0 := ApproxState.initial (semolinaApprox a.toNat b.toNat).1
    (semolinaApprox a.toNat b.toNat).2
  have hs0 : (⟨a0_2, a1_2, a2_3, a3_6, b0_2, b1_1, b2_2, b3_5, t_7⟩ :
      Divsteps31State).Bounded :=
    ⟨b_a0_2, b_a1_2, b_a2_3, b_a3_6, b_b0_2, b_b1_1, b_b2_2, b_b3_5, b_t_7⟩
  have hloop := divsteps31_iterate_spec 31
    (⟨a0_2, a1_2, a2_3, a3_6, b0_2, b1_1, b2_2, b3_5, t_7⟩ : Divsteps31State)
    abstract0 hs0 (by
      simp only [abstract0, ApproxState.initial]
      exact ⟨congrArg Prod.fst happ, congrArg Prod.snd happ⟩)
    (by simpa only [e_a1_2, e_a2_3] using
      And.intro packedRowRep_identity_row0 packedRowRep_identity_row1)
    (by simpa only [e_a3_6] using packedRowBias_eq.symm)
    (by simpa only [abstract0, ApproxState.initial] using semolinaApprox_snd_odd hodd)
    (by
      intro state abstract hstate hvalues hrows hbias hstateOdd
      exact divsteps31Round_spec state abstract hstate hvalues hrows hbias hstateOdd
        (divsteps31Round state) rfl)
  rw [← e_loop] at hloop
  have b_loop_a1 : loop.a1 < 2^64 := hloop.1.2.1
  have b_loop_a2 : loop.a2 < 2^64 := hloop.1.2.2.1
  have b_loop_a3 : loop.a3 < 2^64 := hloop.1.2.2.2.1
  -- END divsteps31 loop setup
  -- a0_3: fixed loop output
  extract_lets -merge +onlyGivenNames a0_3 at hr
  have e_a0_3 : a0_3 = loop.a0 := rfl
  clear_value a0_3
  -- a1_3: fixed loop output
  extract_lets -merge +onlyGivenNames a1_3 at hr
  have e_a1_3 : a1_3 = loop.a1 := rfl
  clear_value a1_3
  -- BEGIN divsteps31 a1 output bound
  have b_a1_3 : a1_3 < 2^64 := by rw [e_a1_3]; exact b_loop_a1
  -- END divsteps31 a1 output bound
  -- a2_4: fixed loop output
  extract_lets -merge +onlyGivenNames a2_4 at hr
  have e_a2_4 : a2_4 = loop.a2 := rfl
  clear_value a2_4
  -- BEGIN divsteps31 a2 output bound
  have b_a2_4 : a2_4 < 2^64 := by rw [e_a2_4]; exact b_loop_a2
  -- END divsteps31 a2 output bound
  -- a3_7: fixed loop output
  extract_lets -merge +onlyGivenNames a3_7 at hr
  have e_a3_7 : a3_7 = loop.a3 := rfl
  clear_value a3_7
  -- BEGIN divsteps31 a3 output bound
  have b_a3_7 : a3_7 < 2^64 := by rw [e_a3_7]; exact b_loop_a3
  -- END divsteps31 a3 output bound
  -- b0_3: fixed loop output
  extract_lets -merge +onlyGivenNames b0_3 at hr
  have e_b0_3 : b0_3 = loop.b0 := rfl
  clear_value b0_3
  -- b1_2: fixed loop output
  extract_lets -merge +onlyGivenNames b1_2 at hr
  have e_b1_2 : b1_2 = loop.b1 := rfl
  clear_value b1_2
  -- b2_3: fixed loop output
  extract_lets -merge +onlyGivenNames b2_3 at hr
  have e_b2_3 : b2_3 = loop.b2 := rfl
  clear_value b2_3
  -- b3_6: fixed loop output
  extract_lets -merge +onlyGivenNames b3_6 at hr
  have e_b3_6 : b3_6 = loop.b3 := rfl
  clear_value b3_6
  -- t_8: fixed loop output
  extract_lets -merge +onlyGivenNames t_8 at hr
  have e_t_8 : t_8 = loop.t := rfl
  clear_value t_8
  -- a3_8: shr {a3}, 32
  extract_lets -merge +onlyGivenNames a3_8 at hr
  have e_a3_8 : a3_8 = a3_7 / 2^32 := rfl
  clear_value a3_8
  have b_a3_8 : a3_8 < 2^32 := by
    rw [e_a3_8]; exact Nat.div_lt_of_lt_mul (lt_of_lt_of_eq b_a3_7 (by norm_num))
  -- a0_4: mov {a0:e}, {a1:e}
  extract_lets -merge +onlyGivenNames a0_4 at hr
  have e_a0_4 : a0_4 = word32 (word32 a1_3) := rfl
  clear_value a0_4
  have b_a0_4 : a0_4 < 2^64 := by rw [e_a0_4]; exact Nat.lt_trans (word32_lt _) (by decide)
  -- b0_4: mov {b0:e}, {a2:e}
  extract_lets -merge +onlyGivenNames b0_4 at hr
  have e_b0_4 : b0_4 = word32 (word32 a2_4) := rfl
  clear_value b0_4
  have b_b0_4 : b0_4 < 2^64 := by rw [e_b0_4]; exact Nat.lt_trans (word32_lt _) (by decide)
  -- a1_4: shr {a1}, 32
  extract_lets -merge +onlyGivenNames a1_4 at hr
  have e_a1_4 : a1_4 = a1_3 / 2^32 := rfl
  clear_value a1_4
  have b_a1_4 : a1_4 < 2^32 := by
    rw [e_a1_4]; exact Nat.div_lt_of_lt_mul (lt_of_lt_of_eq b_a1_3 (by norm_num))
  -- a2_5: shr {a2}, 32
  extract_lets -merge +onlyGivenNames a2_5 at hr
  have e_a2_5 : a2_5 = a2_4 / 2^32 := rfl
  clear_value a2_5
  have b_a2_5 : a2_5 < 2^32 := by
    rw [e_a2_5]; exact Nat.div_lt_of_lt_mul (lt_of_lt_of_eq b_a2_4 (by norm_num))
  -- a0_5: sub {a0}, {a3}
  extract_lets -merge +onlyGivenNames s_1 a0_5 cf_10 at hr
  have e_a0_5 : a0_5 = (sbb a0_4 a3_8 0).1 := rfl
  have e_cf_10 : cf_10 = (sbb a0_4 a3_8 0).2 := rfl
  clear_value s_1 a0_5 cf_10
  have l_a0_5 : a0_5 + a3_8 + 0 = a0_4 + 2^64 * cf_10 := by
    rw [e_a0_5, e_cf_10]; exact sbb_lin a0_4 a3_8 0 b_a0_4 (lt_of_lt_of_le b_a3_8 (by norm_num)) (by decide)
  have b_a0_5 : a0_5 < 2^64 := by rw [e_a0_5]; exact sbb_value_lt a0_4 a3_8 0
  have b_cf_10 : cf_10 ≤ 1 := by rw [e_cf_10]; exact sbb_borrow_le_one a0_4 a3_8 0
  clear e_a0_5 e_cf_10
  -- a1_5: sub {a1}, {a3}
  extract_lets -merge +onlyGivenNames s_2 a1_5 cf_11 at hr
  have e_a1_5 : a1_5 = (sbb a1_4 a3_8 0).1 := rfl
  have e_cf_11 : cf_11 = (sbb a1_4 a3_8 0).2 := rfl
  clear_value s_2 a1_5 cf_11
  have l_a1_5 : a1_5 + a3_8 + 0 = a1_4 + 2^64 * cf_11 := by
    rw [e_a1_5, e_cf_11]; exact sbb_lin a1_4 a3_8 0 (lt_of_lt_of_le b_a1_4 (by norm_num)) (lt_of_lt_of_le b_a3_8 (by norm_num)) (by decide)
  have b_a1_5 : a1_5 < 2^64 := by rw [e_a1_5]; exact sbb_value_lt a1_4 a3_8 0
  have b_cf_11 : cf_11 ≤ 1 := by rw [e_cf_11]; exact sbb_borrow_le_one a1_4 a3_8 0
  clear e_a1_5 e_cf_11
  -- b0_5: sub {b0}, {a3}
  extract_lets -merge +onlyGivenNames s_3 b0_5 cf_12 at hr
  have e_b0_5 : b0_5 = (sbb b0_4 a3_8 0).1 := rfl
  have e_cf_12 : cf_12 = (sbb b0_4 a3_8 0).2 := rfl
  clear_value s_3 b0_5 cf_12
  have l_b0_5 : b0_5 + a3_8 + 0 = b0_4 + 2^64 * cf_12 := by
    rw [e_b0_5, e_cf_12]; exact sbb_lin b0_4 a3_8 0 b_b0_4 (lt_of_lt_of_le b_a3_8 (by norm_num)) (by decide)
  have b_b0_5 : b0_5 < 2^64 := by rw [e_b0_5]; exact sbb_value_lt b0_4 a3_8 0
  have b_cf_12 : cf_12 ≤ 1 := by rw [e_cf_12]; exact sbb_borrow_le_one b0_4 a3_8 0
  clear e_b0_5 e_cf_12
  -- a2_6: sub {a2}, {a3}
  extract_lets -merge +onlyGivenNames s_4 a2_6 cf_13 at hr
  have e_a2_6 : a2_6 = (sbb a2_5 a3_8 0).1 := rfl
  have e_cf_13 : cf_13 = (sbb a2_5 a3_8 0).2 := rfl
  clear_value s_4 a2_6 cf_13
  have l_a2_6 : a2_6 + a3_8 + 0 = a2_5 + 2^64 * cf_13 := by
    rw [e_a2_6, e_cf_13]; exact sbb_lin a2_5 a3_8 0 (lt_of_lt_of_le b_a2_5 (by norm_num)) (lt_of_lt_of_le b_a3_8 (by norm_num)) (by decide)
  have b_a2_6 : a2_6 < 2^64 := by rw [e_a2_6]; exact sbb_value_lt a2_5 a3_8 0
  have b_cf_13 : cf_13 ≤ 1 := by rw [e_cf_13]; exact sbb_borrow_le_one a2_5 a3_8 0
  clear e_a2_6 e_cf_13
  subst hr
  -- BEGIN divsteps31 conclusion
  have hrow0 : PackedRowRep loop.a1 (semolinaShort a.toNat b.toNat).matrix.row0 := by
    simpa only [semolinaShort, abstract0] using hloop.2.2.2.1
  have hrow1 : PackedRowRep loop.a2 (semolinaShort a.toNat b.toNat).matrix.row1 := by
    simpa only [semolinaShort, abstract0] using hloop.2.2.2.2.1
  have hbiasOut : loop.a3 = packedRowBias := hloop.2.2.2.2.2
  have hbiasLane : a3_8 = packedBias := by
    rw [e_a3_8, e_a3_7, hbiasOut, packedRowBias_eq]
    norm_num [packedBias]
  have hbound := semolinaShort_biasBounded a.toNat b.toNat
  have hsub00 : a0_5 + packedBias + 0 = a0_4 + 2^64 * cf_10 := by
    simpa only [hbiasLane] using l_a0_5
  have hsub01 : a1_5 + packedBias + 0 = a1_4 + 2^64 * cf_11 := by
    simpa only [hbiasLane] using l_a1_5
  have hsub10 : b0_5 + packedBias + 0 = b0_4 + 2^64 * cf_12 := by
    simpa only [hbiasLane] using l_b0_5
  have hsub11 : a2_6 + packedBias + 0 = a2_5 + 2^64 * cf_13 := by
    simpa only [hbiasLane] using l_a2_6
  have hdecode0 := packedRowRep_decode
    (word := loop.a1) (low := a0_4) (high := a1_4)
    (lowOut := a0_5) (highOut := a1_5) (lowBorrow := cf_10) (highBorrow := cf_11)
    hrow0 hbound.1 (by rw [e_a0_4, e_a1_3]; exact Nat.mod_mod _ _)
    (by rw [e_a1_4, e_a1_3]) hsub00 hsub01 b_a0_5 b_a1_5
  have hdecode1 := packedRowRep_decode
    (word := loop.a2) (low := b0_4) (high := a2_5)
    (lowOut := b0_5) (highOut := a2_6) (lowBorrow := cf_12) (highBorrow := cf_13)
    hrow1 hbound.2 (by rw [e_b0_4, e_a2_4]; exact Nat.mod_mod _ _)
    (by rw [e_a2_5, e_a2_4]) hsub10 hsub11 b_b0_5 b_a2_6
  refine ⟨?_, semolinaShort_matrix_bounded a.toNat b.toNat⟩
  simpa only [InvertMatrixRep, hbiasLane] using
    And.intro hdecode0.1 (And.intro hdecode0.2 (And.intro hdecode1.1 hdecode1.2))
  -- END divsteps31 conclusion

end PastaAsm.X86_64
