/-
Copyright Supranational LLC (the routines, transcribed from Semolina v0.1.4).
Copyright (c) 2026 the pasta-asm contributors (the transcription and the proofs).
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.AArch64.Spec.Invert.Divsteps.Approximation

/-!
# Correctness of the AArch64 31-step inversion wrapper

The checked wrapper constructs Semolina's 64-bit approximation of two bounded four-limb
inputs, performs exactly 31 packed divsteps, and decodes the two biased coefficient rows.
-/

namespace PastaAsm.AArch64

open Spec.Invert Spec.Invert.Convergence

/-- The four returned AArch64 words represent the rows of an integer transition matrix. -/
def InvertMatrixRep (words : InvertMatrix) (matrix : SignedMatrix) : Prop :=
  WordRep words.f0 matrix.row0.left ∧
  WordRep words.g0 matrix.row0.right ∧
  WordRep words.f1 matrix.row1.left ∧
  WordRep words.g1 matrix.row1.right

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
  -- a0: argument
  extract_lets -merge +onlyGivenNames a0 at hr
  have e_a0 : a0 = a.l0 := rfl
  clear_value a0
  have b_a0 : a0 < 2^64 := by rw [e_a0]; exact ha.1
  -- a1: argument
  extract_lets -merge +onlyGivenNames a1 at hr
  have e_a1 : a1 = a.l1 := rfl
  clear_value a1
  have b_a1 : a1 < 2^64 := by rw [e_a1]; exact ha.2.1
  -- a2: argument
  extract_lets -merge +onlyGivenNames a2 at hr
  have e_a2 : a2 = a.l2 := rfl
  clear_value a2
  have b_a2 : a2 < 2^64 := by rw [e_a2]; exact ha.2.2.1
  -- a3: argument
  extract_lets -merge +onlyGivenNames a3 at hr
  have e_a3 : a3 = a.l3 := rfl
  clear_value a3
  have b_a3 : a3 < 2^64 := by rw [e_a3]; exact ha.2.2.2
  -- b0: argument
  extract_lets -merge +onlyGivenNames b0 at hr
  have e_b0 : b0 = b.l0 := rfl
  clear_value b0
  have b_b0 : b0 < 2^64 := by rw [e_b0]; exact hb.1
  -- b1: argument
  extract_lets -merge +onlyGivenNames b1 at hr
  have e_b1 : b1 = b.l1 := rfl
  clear_value b1
  have b_b1 : b1 < 2^64 := by rw [e_b1]; exact hb.2.1
  -- b2: argument
  extract_lets -merge +onlyGivenNames b2 at hr
  have e_b2 : b2 = b.l2 := rfl
  clear_value b2
  have b_b2 : b2 < 2^64 := by rw [e_b2]; exact hb.2.2.1
  -- b3: argument
  extract_lets -merge +onlyGivenNames b3 at hr
  have e_b3 : b3 = b.l3 := rfl
  clear_value b3
  have b_b3 : b3 < 2^64 := by rw [e_b3]; exact hb.2.2.2
  -- fg0: argument
  extract_lets -merge +onlyGivenNames fg0 at hr
  have e_fg0 : fg0 = 9223372034707292160 := rfl
  clear_value fg0
  have b_fg0 : fg0 < 2^64 := by rw [e_fg0]; decide
  -- fg1: argument
  extract_lets -merge +onlyGivenNames fg1 at hr
  have e_fg1 : fg1 = 9223372039002259455 := rfl
  clear_value fg1
  have b_fg1 : fg1 < 2^64 := by rw [e_fg1]; decide
  -- bias: argument
  extract_lets -merge +onlyGivenNames bias at hr
  have e_bias : bias = 9223372034707292159 := rfl
  clear_value bias
  have b_bias : bias < 2^64 := by rw [e_bias]; decide
  -- cnt: argument
  extract_lets -merge +onlyGivenNames cnt at hr
  have e_cnt : cnt = 31 := rfl
  clear_value cnt
  have b_cnt : cnt < 2^64 := by rw [e_cnt]; decide
  -- t0: orr t0,a3,b3
  extract_lets -merge +onlyGivenNames t0 at hr
  have e_t0 : t0 = orr a3 b3 := rfl
  clear_value t0
  have b_t0 : t0 < 2^64 := by rw [e_t0]; exact orr_lt _ _
  -- z: cmp t0,#0
  extract_lets -merge +onlyGivenNames z at hr
  have e_z : z = (cmp t0 0).z := rfl
  clear_value z
  have b_z : z ≤ 1 := calc
    z = (cmp t0 0).z := e_z
    _ ≤ 1 := cmp_z_le_one t0 0
  -- a3_1: csel a3,a3,a2,ne
  extract_lets -merge +onlyGivenNames a3_1 at hr
  have e_a3_1 : a3_1 = (if z = 0 then a3 else a2) := rfl
  clear_value a3_1
  have b_a3_1 : a3_1 < 2^64 := by
    rw [e_a3_1]; split <;> first | exact b_a3 | exact b_a2
  -- b3_1: csel b3,b3,b2,ne
  extract_lets -merge +onlyGivenNames b3_1 at hr
  have e_b3_1 : b3_1 = (if z = 0 then b3 else b2) := rfl
  clear_value b3_1
  have b_b3_1 : b3_1 < 2^64 := by
    rw [e_b3_1]; split <;> first | exact b_b3 | exact b_b2
  -- a2_1: csel a2,a2,a1,ne
  extract_lets -merge +onlyGivenNames a2_1 at hr
  have e_a2_1 : a2_1 = (if z = 0 then a2 else a1) := rfl
  clear_value a2_1
  have b_a2_1 : a2_1 < 2^64 := by
    rw [e_a2_1]; split <;> first | exact b_a2 | exact b_a1
  -- t0_1: orr t0,a3,b3
  extract_lets -merge +onlyGivenNames t0_1 at hr
  have e_t0_1 : t0_1 = orr a3_1 b3_1 := rfl
  clear_value t0_1
  have b_t0_1 : t0_1 < 2^64 := by rw [e_t0_1]; exact orr_lt _ _
  -- b2_1: csel b2,b2,b1,ne
  extract_lets -merge +onlyGivenNames b2_1 at hr
  have e_b2_1 : b2_1 = (if z = 0 then b2 else b1) := rfl
  clear_value b2_1
  have b_b2_1 : b2_1 < 2^64 := by
    rw [e_b2_1]; split <;> first | exact b_b2 | exact b_b1
  -- z_1: cmp t0,#0
  extract_lets -merge +onlyGivenNames z_1 at hr
  have e_z_1 : z_1 = (cmp t0_1 0).z := rfl
  clear_value z_1
  have b_z_1 : z_1 ≤ 1 := calc
    z_1 = (cmp t0_1 0).z := e_z_1
    _ ≤ 1 := cmp_z_le_one t0_1 0
  -- a3_2: csel a3,a3,a2,ne
  extract_lets -merge +onlyGivenNames a3_2 at hr
  have e_a3_2 : a3_2 = (if z_1 = 0 then a3_1 else a2_1) := rfl
  clear_value a3_2
  have b_a3_2 : a3_2 < 2^64 := by
    rw [e_a3_2]; split <;> first | exact b_a3_1 | exact b_a2_1
  -- b3_2: csel b3,b3,b2,ne
  extract_lets -merge +onlyGivenNames b3_2 at hr
  have e_b3_2 : b3_2 = (if z_1 = 0 then b3_1 else b2_1) := rfl
  clear_value b3_2
  have b_b3_2 : b3_2 < 2^64 := by
    rw [e_b3_2]; split <;> first | exact b_b3_1 | exact b_b2_1
  -- a2_2: csel a2,a2,a0,ne
  extract_lets -merge +onlyGivenNames a2_2 at hr
  have e_a2_2 : a2_2 = (if z_1 = 0 then a2_1 else a0) := rfl
  clear_value a2_2
  have b_a2_2 : a2_2 < 2^64 := by
    rw [e_a2_2]; split <;> first | exact b_a2_1 | exact b_a0
  -- t0_2: orr t0,a3,b3
  extract_lets -merge +onlyGivenNames t0_2 at hr
  have e_t0_2 : t0_2 = orr a3_2 b3_2 := rfl
  clear_value t0_2
  have b_t0_2 : t0_2 < 2^64 := by rw [e_t0_2]; exact orr_lt _ _
  -- b2_2: csel b2,b2,b0,ne
  extract_lets -merge +onlyGivenNames b2_2 at hr
  have e_b2_2 : b2_2 = (if z_1 = 0 then b2_1 else b0) := rfl
  clear_value b2_2
  have b_b2_2 : b2_2 < 2^64 := by
    rw [e_b2_2]; split <;> first | exact b_b2_1 | exact b_b0
  -- t0_3: clz t0,t0
  extract_lets -merge +onlyGivenNames t0_3 at hr
  have e_t0_3 : t0_3 = clz t0_2 := rfl
  clear_value t0_3
  have b_t0_3 : t0_3 < 2^64 := by rw [e_t0_3]; exact lt_of_le_of_lt (clz_le _) (by norm_num)
  -- z_2: cmp t0,#64
  extract_lets -merge +onlyGivenNames z_2 at hr
  have e_z_2 : z_2 = (cmp t0_3 64).z := rfl
  clear_value z_2
  have b_z_2 : z_2 ≤ 1 := calc
    z_2 = (cmp t0_3 64).z := e_z_2
    _ ≤ 1 := cmp_z_le_one t0_3 64
  -- t0_4: csel t0,t0,xzr,ne
  extract_lets -merge +onlyGivenNames t0_4 at hr
  have e_t0_4 : t0_4 = (if z_2 = 0 then t0_3 else 0) := rfl
  clear_value t0_4
  have b_t0_4 : t0_4 < 2^64 := by
    rw [e_t0_4]; split <;> first | exact b_t0_3 | exact (by decide)
  -- a3_3: csel a3,a3,a2,ne
  extract_lets -merge +onlyGivenNames a3_3 at hr
  have e_a3_3 : a3_3 = (if z_2 = 0 then a3_2 else a2_2) := rfl
  clear_value a3_3
  have b_a3_3 : a3_3 < 2^64 := by
    rw [e_a3_3]; split <;> first | exact b_a3_2 | exact b_a2_2
  -- b3_3: csel b3,b3,b2,ne
  extract_lets -merge +onlyGivenNames b3_3 at hr
  have e_b3_3 : b3_3 = (if z_2 = 0 then b3_2 else b2_2) := rfl
  clear_value b3_3
  have b_b3_3 : b3_3 < 2^64 := by
    rw [e_b3_3]; split <;> first | exact b_b3_2 | exact b_b2_2
  -- t1: neg t1,t0
  extract_lets -merge +onlyGivenNames t1 at hr
  have e_t1 : t1 = neg t0_4 := rfl
  clear_value t1
  have b_t1 : t1 < 2^64 := by rw [e_t1]; exact neg_lt _
  -- a3_4: lslv a3,a3,t0
  extract_lets -merge +onlyGivenNames a3_4 at hr
  have e_a3_4 : a3_4 = lslv a3_3 t0_4 := rfl
  clear_value a3_4
  have b_a3_4 : a3_4 < 2^64 := by rw [e_a3_4]; exact lslv_lt _ _
  -- b3_4: lslv b3,b3,t0
  extract_lets -merge +onlyGivenNames b3_4 at hr
  have e_b3_4 : b3_4 = lslv b3_3 t0_4 := rfl
  clear_value b3_4
  have b_b3_4 : b3_4 < 2^64 := by rw [e_b3_4]; exact lslv_lt _ _
  -- a2_3: lsrv a2,a2,t1
  extract_lets -merge +onlyGivenNames a2_3 at hr
  have e_a2_3 : a2_3 = lsrv a2_2 t1 := rfl
  clear_value a2_3
  have b_a2_3 : a2_3 < 2^64 := by rw [e_a2_3]; exact lsrv_lt _ _
  -- b2_3: lsrv b2,b2,t1
  extract_lets -merge +onlyGivenNames b2_3 at hr
  have e_b2_3 : b2_3 = lsrv b2_2 t1 := rfl
  clear_value b2_3
  have b_b2_3 : b2_3 < 2^64 := by rw [e_b2_3]; exact lsrv_lt _ _
  -- a2_4: and a2,a2,t1,asr #6
  extract_lets -merge +onlyGivenNames a2_4 at hr
  have e_a2_4 : a2_4 = bitAnd a2_3 (asr t1 6) := rfl
  clear_value a2_4
  have b_a2_4 : a2_4 < 2^64 := by rw [e_a2_4]; exact bitAnd_lt _ _
  -- b2_4: and b2,b2,t1,asr #6
  extract_lets -merge +onlyGivenNames b2_4 at hr
  have e_b2_4 : b2_4 = bitAnd b2_3 (asr t1 6) := rfl
  clear_value b2_4
  have b_b2_4 : b2_4 < 2^64 := by rw [e_b2_4]; exact bitAnd_lt _ _
  -- a3_5: orr a3,a3,a2
  extract_lets -merge +onlyGivenNames a3_5 at hr
  have e_a3_5 : a3_5 = orr a3_4 a2_4 := rfl
  clear_value a3_5
  have b_a3_5 : a3_5 < 2^64 := by rw [e_a3_5]; exact orr_lt _ _
  -- b3_5: orr b3,b3,b2
  extract_lets -merge +onlyGivenNames b3_5 at hr
  have e_b3_5 : b3_5 = orr b3_4 b2_4 := rfl
  clear_value b3_5
  have b_b3_5 : b3_5 < 2^64 := by rw [e_b3_5]; exact orr_lt _ _
  -- a3_6: bfxil a3,a0,#0,#31
  extract_lets -merge +onlyGivenNames a3_6 at hr
  have e_a3_6 : a3_6 = bfxil a3_5 a0 0 31 := rfl
  clear_value a3_6
  have b_a3_6 : a3_6 < 2^64 := by rw [e_a3_6]; exact bfxil_lt _ _ _ _
  -- b3_6: bfxil b3,b0,#0,#31
  extract_lets -merge +onlyGivenNames b3_6 at hr
  have e_b3_6 : b3_6 = bfxil b3_5 b0 0 31 := rfl
  clear_value b3_6
  have b_b3_6 : b3_6 < 2^64 := by rw [e_b3_6]; exact bfxil_lt _ _ _ _
  -- BEGIN divsteps31 initial invariant
  let iz0 := (cmp (orr a.l3 b.l3) 0).z
  let ia3₁ := cselNe iz0 a.l3 a.l2
  let ib3₁ := cselNe iz0 b.l3 b.l2
  let ia2₁ := cselNe iz0 a.l2 a.l1
  let ib2₁ := cselNe iz0 b.l2 b.l1
  let iz1 := (cmp (orr ia3₁ ib3₁) 0).z
  let ia3₂ := cselNe iz1 ia3₁ ia2₁
  let ib3₂ := cselNe iz1 ib3₁ ib2₁
  let ia2₂ := cselNe iz1 ia2₁ a.l0
  let ib2₂ := cselNe iz1 ib2₁ b.l0
  let icount0 := clz (orr ia3₂ ib3₂)
  let iz2 := (cmp icount0 64).z
  let icount := cselNe iz2 icount0 0
  have hi0 : t0 = orr a.l3 b.l3 := by simp only [e_t0, e_a3, e_b3]
  have hiz0 : z = iz0 := by simp only [iz0, e_z, hi0]
  have hia3₁ : a3_1 = ia3₁ := by simp only [ia3₁, e_a3_1, hiz0, e_a3, e_a2, cselNe]
  have hib3₁ : b3_1 = ib3₁ := by simp only [ib3₁, e_b3_1, hiz0, e_b3, e_b2, cselNe]
  have hia2₁ : a2_1 = ia2₁ := by simp only [ia2₁, e_a2_1, hiz0, e_a2, e_a1, cselNe]
  have hib2₁ : b2_1 = ib2₁ := by simp only [ib2₁, e_b2_1, hiz0, e_b2, e_b1, cselNe]
  have hi1 : t0_1 = orr ia3₁ ib3₁ := by simp only [e_t0_1, hia3₁, hib3₁]
  have hiz1 : z_1 = iz1 := by simp only [iz1, e_z_1, hi1]
  have hia3₂ : a3_2 = ia3₂ := by simp only [ia3₂, e_a3_2, hiz1, hia3₁, hia2₁, cselNe]
  have hib3₂ : b3_2 = ib3₂ := by simp only [ib3₂, e_b3_2, hiz1, hib3₁, hib2₁, cselNe]
  have hia2₂ : a2_2 = ia2₂ := by simp only [ia2₂, e_a2_2, hiz1, hia2₁, e_a0, cselNe]
  have hib2₂ : b2_2 = ib2₂ := by simp only [ib2₂, e_b2_2, hiz1, hib2₁, e_b0, cselNe]
  have hi2 : t0_2 = orr ia3₂ ib3₂ := by simp only [e_t0_2, hia3₂, hib3₂]
  have hicount0 : t0_3 = icount0 := by simp only [icount0, e_t0_3, hi2]
  have hiz2 : z_2 = iz2 := by simp only [iz2, e_z_2, hicount0]
  have hicount : t0_4 = icount := by simp only [icount, e_t0_4, hiz2, hicount0, cselNe]
  have hia3₃ : a3_3 = cselNe iz2 ia3₂ ia2₂ := by
    simp only [e_a3_3, hiz2, hia3₂, hia2₂, cselNe]
  have hib3₃ : b3_3 = cselNe iz2 ib3₂ ib2₂ := by
    simp only [e_b3_3, hiz2, hib3₂, hib2₂, cselNe]
  have hit1 : t1 = neg icount := by simp only [e_t1, hicount]
  have hia3₅ : a3_5 = finishWindow ia3₂ ia2₂ ia2₂ ib3₂ := by
    unfold finishWindow
    rw [e_a3_5, e_a3_4, e_a2_4, e_a2_3, hia3₃, hia2₂, hit1, hicount]
  have hior : orr ib3₂ ia3₂ = orr ia3₂ ib3₂ := by
    unfold orr PastaAsm.word PastaAsm.regMod
    rw [Nat.or_comm]
  have hib3₅ : b3_5 = finishWindow ib3₂ ib2₂ ib2₂ ia3₂ := by
    unfold finishWindow
    rw [hior]
    change b3_5 = orr (lslv (cselNe iz2 ib3₂ ib2₂) icount)
      (bitAnd (lsrv ib2₂ (neg icount)) (asr (neg icount) 6))
    rw [e_b3_5, e_b3_4, e_b2_4, e_b2_3, hib3₃, hib2₂, hit1, hicount]
  have hinit : (a3_6, b3_6) = divsteps31Init a b := by
    unfold divsteps31Init
    rw [e_a3_6, e_b3_6, hia3₅, hib3₅, e_a0, e_b0]
  have happ : (a3_6, b3_6) = semolinaApprox a.toNat b.toNat :=
    hinit.trans (divsteps31Init_spec a b ha hb)
  let abstract0 := ApproxState.initial (semolinaApprox a.toNat b.toNat).1
    (semolinaApprox a.toNat b.toNat).2
  have hrow0 : PackedRowRep fg0 identityMatrix.row0 := by
    rw [e_fg0]
    norm_num [PackedRowRep, packedRowValue, packedRowBias, packedLaneBias, identityMatrix, WordRep]
  have hrow1 : PackedRowRep fg1 identityMatrix.row1 := by
    rw [e_fg1]
    norm_num [PackedRowRep, packedRowValue, packedRowBias, packedLaneBias, identityMatrix, WordRep]
  have hbias : bias = packedRowBias := by
    rw [e_bias]
    norm_num [packedRowBias, packedLaneBias]
  have hmatch0 : (⟨a3_6, cnt, b3_6, fg1, fg0⟩ : Divsteps31State).Matches abstract0 := by
    refine ⟨⟨b_a3_6, b_cnt, b_b3_6, b_fg1, b_fg0⟩, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [abstract0, ApproxState.initial] using congrArg Prod.fst happ
    · simpa only [abstract0, ApproxState.initial] using congrArg Prod.snd happ
    · simpa only [abstract0, ApproxState.initial] using hrow0
    · simpa only [abstract0, ApproxState.initial] using hrow1
    · change Odd b3_6
      have happSnd : b3_6 = (semolinaApprox a.toNat b.toNat).2 := by
        simpa only using congrArg Prod.snd happ
      simpa only [happSnd] using semolinaApprox_snd_odd hodd
  -- END divsteps31 initial invariant
  -- round1: loop iteration 1
  extract_lets -merge +onlyGivenNames round1 at hr
  have e_round1 : round1 = divsteps31Round bias ⟨a3_6, cnt, b3_6, fg1, fg0⟩ := rfl
  clear_value round1
  -- a3_7: loop iteration 1 output
  extract_lets -merge +onlyGivenNames a3_7 at hr
  have e_a3_7 : a3_7 = round1.a3 := rfl
  clear_value a3_7
  -- cnt_1: loop iteration 1 output
  extract_lets -merge +onlyGivenNames cnt_1 at hr
  have e_cnt_1 : cnt_1 = round1.cnt := rfl
  clear_value cnt_1
  -- b3_7: loop iteration 1 output
  extract_lets -merge +onlyGivenNames b3_7 at hr
  have e_b3_7 : b3_7 = round1.b3 := rfl
  clear_value b3_7
  -- fg1_1: loop iteration 1 output
  extract_lets -merge +onlyGivenNames fg1_1 at hr
  have e_fg1_1 : fg1_1 = round1.fg1 := rfl
  clear_value fg1_1
  -- fg0_1: loop iteration 1 output
  extract_lets -merge +onlyGivenNames fg0_1 at hr
  have e_fg0_1 : fg0_1 = round1.fg0 := rfl
  clear_value fg0_1
  -- round2: loop iteration 2
  extract_lets -merge +onlyGivenNames round2 at hr
  have e_round2 : round2 = divsteps31Round bias ⟨a3_7, cnt_1, b3_7, fg1_1, fg0_1⟩ := rfl
  clear_value round2
  -- a3_8: loop iteration 2 output
  extract_lets -merge +onlyGivenNames a3_8 at hr
  have e_a3_8 : a3_8 = round2.a3 := rfl
  clear_value a3_8
  -- cnt_2: loop iteration 2 output
  extract_lets -merge +onlyGivenNames cnt_2 at hr
  have e_cnt_2 : cnt_2 = round2.cnt := rfl
  clear_value cnt_2
  -- b3_8: loop iteration 2 output
  extract_lets -merge +onlyGivenNames b3_8 at hr
  have e_b3_8 : b3_8 = round2.b3 := rfl
  clear_value b3_8
  -- fg1_2: loop iteration 2 output
  extract_lets -merge +onlyGivenNames fg1_2 at hr
  have e_fg1_2 : fg1_2 = round2.fg1 := rfl
  clear_value fg1_2
  -- fg0_2: loop iteration 2 output
  extract_lets -merge +onlyGivenNames fg0_2 at hr
  have e_fg0_2 : fg0_2 = round2.fg0 := rfl
  clear_value fg0_2
  -- round3: loop iteration 3
  extract_lets -merge +onlyGivenNames round3 at hr
  have e_round3 : round3 = divsteps31Round bias ⟨a3_8, cnt_2, b3_8, fg1_2, fg0_2⟩ := rfl
  clear_value round3
  -- a3_9: loop iteration 3 output
  extract_lets -merge +onlyGivenNames a3_9 at hr
  have e_a3_9 : a3_9 = round3.a3 := rfl
  clear_value a3_9
  -- cnt_3: loop iteration 3 output
  extract_lets -merge +onlyGivenNames cnt_3 at hr
  have e_cnt_3 : cnt_3 = round3.cnt := rfl
  clear_value cnt_3
  -- b3_9: loop iteration 3 output
  extract_lets -merge +onlyGivenNames b3_9 at hr
  have e_b3_9 : b3_9 = round3.b3 := rfl
  clear_value b3_9
  -- fg1_3: loop iteration 3 output
  extract_lets -merge +onlyGivenNames fg1_3 at hr
  have e_fg1_3 : fg1_3 = round3.fg1 := rfl
  clear_value fg1_3
  -- fg0_3: loop iteration 3 output
  extract_lets -merge +onlyGivenNames fg0_3 at hr
  have e_fg0_3 : fg0_3 = round3.fg0 := rfl
  clear_value fg0_3
  -- round4: loop iteration 4
  extract_lets -merge +onlyGivenNames round4 at hr
  have e_round4 : round4 = divsteps31Round bias ⟨a3_9, cnt_3, b3_9, fg1_3, fg0_3⟩ := rfl
  clear_value round4
  -- a3_10: loop iteration 4 output
  extract_lets -merge +onlyGivenNames a3_10 at hr
  have e_a3_10 : a3_10 = round4.a3 := rfl
  clear_value a3_10
  -- cnt_4: loop iteration 4 output
  extract_lets -merge +onlyGivenNames cnt_4 at hr
  have e_cnt_4 : cnt_4 = round4.cnt := rfl
  clear_value cnt_4
  -- b3_10: loop iteration 4 output
  extract_lets -merge +onlyGivenNames b3_10 at hr
  have e_b3_10 : b3_10 = round4.b3 := rfl
  clear_value b3_10
  -- fg1_4: loop iteration 4 output
  extract_lets -merge +onlyGivenNames fg1_4 at hr
  have e_fg1_4 : fg1_4 = round4.fg1 := rfl
  clear_value fg1_4
  -- fg0_4: loop iteration 4 output
  extract_lets -merge +onlyGivenNames fg0_4 at hr
  have e_fg0_4 : fg0_4 = round4.fg0 := rfl
  clear_value fg0_4
  -- round5: loop iteration 5
  extract_lets -merge +onlyGivenNames round5 at hr
  have e_round5 : round5 = divsteps31Round bias ⟨a3_10, cnt_4, b3_10, fg1_4, fg0_4⟩ := rfl
  clear_value round5
  -- a3_11: loop iteration 5 output
  extract_lets -merge +onlyGivenNames a3_11 at hr
  have e_a3_11 : a3_11 = round5.a3 := rfl
  clear_value a3_11
  -- cnt_5: loop iteration 5 output
  extract_lets -merge +onlyGivenNames cnt_5 at hr
  have e_cnt_5 : cnt_5 = round5.cnt := rfl
  clear_value cnt_5
  -- b3_11: loop iteration 5 output
  extract_lets -merge +onlyGivenNames b3_11 at hr
  have e_b3_11 : b3_11 = round5.b3 := rfl
  clear_value b3_11
  -- fg1_5: loop iteration 5 output
  extract_lets -merge +onlyGivenNames fg1_5 at hr
  have e_fg1_5 : fg1_5 = round5.fg1 := rfl
  clear_value fg1_5
  -- fg0_5: loop iteration 5 output
  extract_lets -merge +onlyGivenNames fg0_5 at hr
  have e_fg0_5 : fg0_5 = round5.fg0 := rfl
  clear_value fg0_5
  -- round6: loop iteration 6
  extract_lets -merge +onlyGivenNames round6 at hr
  have e_round6 : round6 = divsteps31Round bias ⟨a3_11, cnt_5, b3_11, fg1_5, fg0_5⟩ := rfl
  clear_value round6
  -- a3_12: loop iteration 6 output
  extract_lets -merge +onlyGivenNames a3_12 at hr
  have e_a3_12 : a3_12 = round6.a3 := rfl
  clear_value a3_12
  -- cnt_6: loop iteration 6 output
  extract_lets -merge +onlyGivenNames cnt_6 at hr
  have e_cnt_6 : cnt_6 = round6.cnt := rfl
  clear_value cnt_6
  -- b3_12: loop iteration 6 output
  extract_lets -merge +onlyGivenNames b3_12 at hr
  have e_b3_12 : b3_12 = round6.b3 := rfl
  clear_value b3_12
  -- fg1_6: loop iteration 6 output
  extract_lets -merge +onlyGivenNames fg1_6 at hr
  have e_fg1_6 : fg1_6 = round6.fg1 := rfl
  clear_value fg1_6
  -- fg0_6: loop iteration 6 output
  extract_lets -merge +onlyGivenNames fg0_6 at hr
  have e_fg0_6 : fg0_6 = round6.fg0 := rfl
  clear_value fg0_6
  -- round7: loop iteration 7
  extract_lets -merge +onlyGivenNames round7 at hr
  have e_round7 : round7 = divsteps31Round bias ⟨a3_12, cnt_6, b3_12, fg1_6, fg0_6⟩ := rfl
  clear_value round7
  -- a3_13: loop iteration 7 output
  extract_lets -merge +onlyGivenNames a3_13 at hr
  have e_a3_13 : a3_13 = round7.a3 := rfl
  clear_value a3_13
  -- cnt_7: loop iteration 7 output
  extract_lets -merge +onlyGivenNames cnt_7 at hr
  have e_cnt_7 : cnt_7 = round7.cnt := rfl
  clear_value cnt_7
  -- b3_13: loop iteration 7 output
  extract_lets -merge +onlyGivenNames b3_13 at hr
  have e_b3_13 : b3_13 = round7.b3 := rfl
  clear_value b3_13
  -- fg1_7: loop iteration 7 output
  extract_lets -merge +onlyGivenNames fg1_7 at hr
  have e_fg1_7 : fg1_7 = round7.fg1 := rfl
  clear_value fg1_7
  -- fg0_7: loop iteration 7 output
  extract_lets -merge +onlyGivenNames fg0_7 at hr
  have e_fg0_7 : fg0_7 = round7.fg0 := rfl
  clear_value fg0_7
  -- round8: loop iteration 8
  extract_lets -merge +onlyGivenNames round8 at hr
  have e_round8 : round8 = divsteps31Round bias ⟨a3_13, cnt_7, b3_13, fg1_7, fg0_7⟩ := rfl
  clear_value round8
  -- a3_14: loop iteration 8 output
  extract_lets -merge +onlyGivenNames a3_14 at hr
  have e_a3_14 : a3_14 = round8.a3 := rfl
  clear_value a3_14
  -- cnt_8: loop iteration 8 output
  extract_lets -merge +onlyGivenNames cnt_8 at hr
  have e_cnt_8 : cnt_8 = round8.cnt := rfl
  clear_value cnt_8
  -- b3_14: loop iteration 8 output
  extract_lets -merge +onlyGivenNames b3_14 at hr
  have e_b3_14 : b3_14 = round8.b3 := rfl
  clear_value b3_14
  -- fg1_8: loop iteration 8 output
  extract_lets -merge +onlyGivenNames fg1_8 at hr
  have e_fg1_8 : fg1_8 = round8.fg1 := rfl
  clear_value fg1_8
  -- fg0_8: loop iteration 8 output
  extract_lets -merge +onlyGivenNames fg0_8 at hr
  have e_fg0_8 : fg0_8 = round8.fg0 := rfl
  clear_value fg0_8
  -- round9: loop iteration 9
  extract_lets -merge +onlyGivenNames round9 at hr
  have e_round9 : round9 = divsteps31Round bias ⟨a3_14, cnt_8, b3_14, fg1_8, fg0_8⟩ := rfl
  clear_value round9
  -- a3_15: loop iteration 9 output
  extract_lets -merge +onlyGivenNames a3_15 at hr
  have e_a3_15 : a3_15 = round9.a3 := rfl
  clear_value a3_15
  -- cnt_9: loop iteration 9 output
  extract_lets -merge +onlyGivenNames cnt_9 at hr
  have e_cnt_9 : cnt_9 = round9.cnt := rfl
  clear_value cnt_9
  -- b3_15: loop iteration 9 output
  extract_lets -merge +onlyGivenNames b3_15 at hr
  have e_b3_15 : b3_15 = round9.b3 := rfl
  clear_value b3_15
  -- fg1_9: loop iteration 9 output
  extract_lets -merge +onlyGivenNames fg1_9 at hr
  have e_fg1_9 : fg1_9 = round9.fg1 := rfl
  clear_value fg1_9
  -- fg0_9: loop iteration 9 output
  extract_lets -merge +onlyGivenNames fg0_9 at hr
  have e_fg0_9 : fg0_9 = round9.fg0 := rfl
  clear_value fg0_9
  -- round10: loop iteration 10
  extract_lets -merge +onlyGivenNames round10 at hr
  have e_round10 : round10 = divsteps31Round bias ⟨a3_15, cnt_9, b3_15, fg1_9, fg0_9⟩ := rfl
  clear_value round10
  -- a3_16: loop iteration 10 output
  extract_lets -merge +onlyGivenNames a3_16 at hr
  have e_a3_16 : a3_16 = round10.a3 := rfl
  clear_value a3_16
  -- cnt_10: loop iteration 10 output
  extract_lets -merge +onlyGivenNames cnt_10 at hr
  have e_cnt_10 : cnt_10 = round10.cnt := rfl
  clear_value cnt_10
  -- b3_16: loop iteration 10 output
  extract_lets -merge +onlyGivenNames b3_16 at hr
  have e_b3_16 : b3_16 = round10.b3 := rfl
  clear_value b3_16
  -- fg1_10: loop iteration 10 output
  extract_lets -merge +onlyGivenNames fg1_10 at hr
  have e_fg1_10 : fg1_10 = round10.fg1 := rfl
  clear_value fg1_10
  -- fg0_10: loop iteration 10 output
  extract_lets -merge +onlyGivenNames fg0_10 at hr
  have e_fg0_10 : fg0_10 = round10.fg0 := rfl
  clear_value fg0_10
  -- round11: loop iteration 11
  extract_lets -merge +onlyGivenNames round11 at hr
  have e_round11 : round11 = divsteps31Round bias ⟨a3_16, cnt_10, b3_16, fg1_10, fg0_10⟩ := rfl
  clear_value round11
  -- a3_17: loop iteration 11 output
  extract_lets -merge +onlyGivenNames a3_17 at hr
  have e_a3_17 : a3_17 = round11.a3 := rfl
  clear_value a3_17
  -- cnt_11: loop iteration 11 output
  extract_lets -merge +onlyGivenNames cnt_11 at hr
  have e_cnt_11 : cnt_11 = round11.cnt := rfl
  clear_value cnt_11
  -- b3_17: loop iteration 11 output
  extract_lets -merge +onlyGivenNames b3_17 at hr
  have e_b3_17 : b3_17 = round11.b3 := rfl
  clear_value b3_17
  -- fg1_11: loop iteration 11 output
  extract_lets -merge +onlyGivenNames fg1_11 at hr
  have e_fg1_11 : fg1_11 = round11.fg1 := rfl
  clear_value fg1_11
  -- fg0_11: loop iteration 11 output
  extract_lets -merge +onlyGivenNames fg0_11 at hr
  have e_fg0_11 : fg0_11 = round11.fg0 := rfl
  clear_value fg0_11
  -- round12: loop iteration 12
  extract_lets -merge +onlyGivenNames round12 at hr
  have e_round12 : round12 = divsteps31Round bias ⟨a3_17, cnt_11, b3_17, fg1_11, fg0_11⟩ := rfl
  clear_value round12
  -- a3_18: loop iteration 12 output
  extract_lets -merge +onlyGivenNames a3_18 at hr
  have e_a3_18 : a3_18 = round12.a3 := rfl
  clear_value a3_18
  -- cnt_12: loop iteration 12 output
  extract_lets -merge +onlyGivenNames cnt_12 at hr
  have e_cnt_12 : cnt_12 = round12.cnt := rfl
  clear_value cnt_12
  -- b3_18: loop iteration 12 output
  extract_lets -merge +onlyGivenNames b3_18 at hr
  have e_b3_18 : b3_18 = round12.b3 := rfl
  clear_value b3_18
  -- fg1_12: loop iteration 12 output
  extract_lets -merge +onlyGivenNames fg1_12 at hr
  have e_fg1_12 : fg1_12 = round12.fg1 := rfl
  clear_value fg1_12
  -- fg0_12: loop iteration 12 output
  extract_lets -merge +onlyGivenNames fg0_12 at hr
  have e_fg0_12 : fg0_12 = round12.fg0 := rfl
  clear_value fg0_12
  -- round13: loop iteration 13
  extract_lets -merge +onlyGivenNames round13 at hr
  have e_round13 : round13 = divsteps31Round bias ⟨a3_18, cnt_12, b3_18, fg1_12, fg0_12⟩ := rfl
  clear_value round13
  -- a3_19: loop iteration 13 output
  extract_lets -merge +onlyGivenNames a3_19 at hr
  have e_a3_19 : a3_19 = round13.a3 := rfl
  clear_value a3_19
  -- cnt_13: loop iteration 13 output
  extract_lets -merge +onlyGivenNames cnt_13 at hr
  have e_cnt_13 : cnt_13 = round13.cnt := rfl
  clear_value cnt_13
  -- b3_19: loop iteration 13 output
  extract_lets -merge +onlyGivenNames b3_19 at hr
  have e_b3_19 : b3_19 = round13.b3 := rfl
  clear_value b3_19
  -- fg1_13: loop iteration 13 output
  extract_lets -merge +onlyGivenNames fg1_13 at hr
  have e_fg1_13 : fg1_13 = round13.fg1 := rfl
  clear_value fg1_13
  -- fg0_13: loop iteration 13 output
  extract_lets -merge +onlyGivenNames fg0_13 at hr
  have e_fg0_13 : fg0_13 = round13.fg0 := rfl
  clear_value fg0_13
  -- round14: loop iteration 14
  extract_lets -merge +onlyGivenNames round14 at hr
  have e_round14 : round14 = divsteps31Round bias ⟨a3_19, cnt_13, b3_19, fg1_13, fg0_13⟩ := rfl
  clear_value round14
  -- a3_20: loop iteration 14 output
  extract_lets -merge +onlyGivenNames a3_20 at hr
  have e_a3_20 : a3_20 = round14.a3 := rfl
  clear_value a3_20
  -- cnt_14: loop iteration 14 output
  extract_lets -merge +onlyGivenNames cnt_14 at hr
  have e_cnt_14 : cnt_14 = round14.cnt := rfl
  clear_value cnt_14
  -- b3_20: loop iteration 14 output
  extract_lets -merge +onlyGivenNames b3_20 at hr
  have e_b3_20 : b3_20 = round14.b3 := rfl
  clear_value b3_20
  -- fg1_14: loop iteration 14 output
  extract_lets -merge +onlyGivenNames fg1_14 at hr
  have e_fg1_14 : fg1_14 = round14.fg1 := rfl
  clear_value fg1_14
  -- fg0_14: loop iteration 14 output
  extract_lets -merge +onlyGivenNames fg0_14 at hr
  have e_fg0_14 : fg0_14 = round14.fg0 := rfl
  clear_value fg0_14
  -- round15: loop iteration 15
  extract_lets -merge +onlyGivenNames round15 at hr
  have e_round15 : round15 = divsteps31Round bias ⟨a3_20, cnt_14, b3_20, fg1_14, fg0_14⟩ := rfl
  clear_value round15
  -- a3_21: loop iteration 15 output
  extract_lets -merge +onlyGivenNames a3_21 at hr
  have e_a3_21 : a3_21 = round15.a3 := rfl
  clear_value a3_21
  -- cnt_15: loop iteration 15 output
  extract_lets -merge +onlyGivenNames cnt_15 at hr
  have e_cnt_15 : cnt_15 = round15.cnt := rfl
  clear_value cnt_15
  -- b3_21: loop iteration 15 output
  extract_lets -merge +onlyGivenNames b3_21 at hr
  have e_b3_21 : b3_21 = round15.b3 := rfl
  clear_value b3_21
  -- fg1_15: loop iteration 15 output
  extract_lets -merge +onlyGivenNames fg1_15 at hr
  have e_fg1_15 : fg1_15 = round15.fg1 := rfl
  clear_value fg1_15
  -- fg0_15: loop iteration 15 output
  extract_lets -merge +onlyGivenNames fg0_15 at hr
  have e_fg0_15 : fg0_15 = round15.fg0 := rfl
  clear_value fg0_15
  -- round16: loop iteration 16
  extract_lets -merge +onlyGivenNames round16 at hr
  have e_round16 : round16 = divsteps31Round bias ⟨a3_21, cnt_15, b3_21, fg1_15, fg0_15⟩ := rfl
  clear_value round16
  -- a3_22: loop iteration 16 output
  extract_lets -merge +onlyGivenNames a3_22 at hr
  have e_a3_22 : a3_22 = round16.a3 := rfl
  clear_value a3_22
  -- cnt_16: loop iteration 16 output
  extract_lets -merge +onlyGivenNames cnt_16 at hr
  have e_cnt_16 : cnt_16 = round16.cnt := rfl
  clear_value cnt_16
  -- b3_22: loop iteration 16 output
  extract_lets -merge +onlyGivenNames b3_22 at hr
  have e_b3_22 : b3_22 = round16.b3 := rfl
  clear_value b3_22
  -- fg1_16: loop iteration 16 output
  extract_lets -merge +onlyGivenNames fg1_16 at hr
  have e_fg1_16 : fg1_16 = round16.fg1 := rfl
  clear_value fg1_16
  -- fg0_16: loop iteration 16 output
  extract_lets -merge +onlyGivenNames fg0_16 at hr
  have e_fg0_16 : fg0_16 = round16.fg0 := rfl
  clear_value fg0_16
  -- round17: loop iteration 17
  extract_lets -merge +onlyGivenNames round17 at hr
  have e_round17 : round17 = divsteps31Round bias ⟨a3_22, cnt_16, b3_22, fg1_16, fg0_16⟩ := rfl
  clear_value round17
  -- a3_23: loop iteration 17 output
  extract_lets -merge +onlyGivenNames a3_23 at hr
  have e_a3_23 : a3_23 = round17.a3 := rfl
  clear_value a3_23
  -- cnt_17: loop iteration 17 output
  extract_lets -merge +onlyGivenNames cnt_17 at hr
  have e_cnt_17 : cnt_17 = round17.cnt := rfl
  clear_value cnt_17
  -- b3_23: loop iteration 17 output
  extract_lets -merge +onlyGivenNames b3_23 at hr
  have e_b3_23 : b3_23 = round17.b3 := rfl
  clear_value b3_23
  -- fg1_17: loop iteration 17 output
  extract_lets -merge +onlyGivenNames fg1_17 at hr
  have e_fg1_17 : fg1_17 = round17.fg1 := rfl
  clear_value fg1_17
  -- fg0_17: loop iteration 17 output
  extract_lets -merge +onlyGivenNames fg0_17 at hr
  have e_fg0_17 : fg0_17 = round17.fg0 := rfl
  clear_value fg0_17
  -- round18: loop iteration 18
  extract_lets -merge +onlyGivenNames round18 at hr
  have e_round18 : round18 = divsteps31Round bias ⟨a3_23, cnt_17, b3_23, fg1_17, fg0_17⟩ := rfl
  clear_value round18
  -- a3_24: loop iteration 18 output
  extract_lets -merge +onlyGivenNames a3_24 at hr
  have e_a3_24 : a3_24 = round18.a3 := rfl
  clear_value a3_24
  -- cnt_18: loop iteration 18 output
  extract_lets -merge +onlyGivenNames cnt_18 at hr
  have e_cnt_18 : cnt_18 = round18.cnt := rfl
  clear_value cnt_18
  -- b3_24: loop iteration 18 output
  extract_lets -merge +onlyGivenNames b3_24 at hr
  have e_b3_24 : b3_24 = round18.b3 := rfl
  clear_value b3_24
  -- fg1_18: loop iteration 18 output
  extract_lets -merge +onlyGivenNames fg1_18 at hr
  have e_fg1_18 : fg1_18 = round18.fg1 := rfl
  clear_value fg1_18
  -- fg0_18: loop iteration 18 output
  extract_lets -merge +onlyGivenNames fg0_18 at hr
  have e_fg0_18 : fg0_18 = round18.fg0 := rfl
  clear_value fg0_18
  -- round19: loop iteration 19
  extract_lets -merge +onlyGivenNames round19 at hr
  have e_round19 : round19 = divsteps31Round bias ⟨a3_24, cnt_18, b3_24, fg1_18, fg0_18⟩ := rfl
  clear_value round19
  -- a3_25: loop iteration 19 output
  extract_lets -merge +onlyGivenNames a3_25 at hr
  have e_a3_25 : a3_25 = round19.a3 := rfl
  clear_value a3_25
  -- cnt_19: loop iteration 19 output
  extract_lets -merge +onlyGivenNames cnt_19 at hr
  have e_cnt_19 : cnt_19 = round19.cnt := rfl
  clear_value cnt_19
  -- b3_25: loop iteration 19 output
  extract_lets -merge +onlyGivenNames b3_25 at hr
  have e_b3_25 : b3_25 = round19.b3 := rfl
  clear_value b3_25
  -- fg1_19: loop iteration 19 output
  extract_lets -merge +onlyGivenNames fg1_19 at hr
  have e_fg1_19 : fg1_19 = round19.fg1 := rfl
  clear_value fg1_19
  -- fg0_19: loop iteration 19 output
  extract_lets -merge +onlyGivenNames fg0_19 at hr
  have e_fg0_19 : fg0_19 = round19.fg0 := rfl
  clear_value fg0_19
  -- round20: loop iteration 20
  extract_lets -merge +onlyGivenNames round20 at hr
  have e_round20 : round20 = divsteps31Round bias ⟨a3_25, cnt_19, b3_25, fg1_19, fg0_19⟩ := rfl
  clear_value round20
  -- a3_26: loop iteration 20 output
  extract_lets -merge +onlyGivenNames a3_26 at hr
  have e_a3_26 : a3_26 = round20.a3 := rfl
  clear_value a3_26
  -- cnt_20: loop iteration 20 output
  extract_lets -merge +onlyGivenNames cnt_20 at hr
  have e_cnt_20 : cnt_20 = round20.cnt := rfl
  clear_value cnt_20
  -- b3_26: loop iteration 20 output
  extract_lets -merge +onlyGivenNames b3_26 at hr
  have e_b3_26 : b3_26 = round20.b3 := rfl
  clear_value b3_26
  -- fg1_20: loop iteration 20 output
  extract_lets -merge +onlyGivenNames fg1_20 at hr
  have e_fg1_20 : fg1_20 = round20.fg1 := rfl
  clear_value fg1_20
  -- fg0_20: loop iteration 20 output
  extract_lets -merge +onlyGivenNames fg0_20 at hr
  have e_fg0_20 : fg0_20 = round20.fg0 := rfl
  clear_value fg0_20
  -- round21: loop iteration 21
  extract_lets -merge +onlyGivenNames round21 at hr
  have e_round21 : round21 = divsteps31Round bias ⟨a3_26, cnt_20, b3_26, fg1_20, fg0_20⟩ := rfl
  clear_value round21
  -- a3_27: loop iteration 21 output
  extract_lets -merge +onlyGivenNames a3_27 at hr
  have e_a3_27 : a3_27 = round21.a3 := rfl
  clear_value a3_27
  -- cnt_21: loop iteration 21 output
  extract_lets -merge +onlyGivenNames cnt_21 at hr
  have e_cnt_21 : cnt_21 = round21.cnt := rfl
  clear_value cnt_21
  -- b3_27: loop iteration 21 output
  extract_lets -merge +onlyGivenNames b3_27 at hr
  have e_b3_27 : b3_27 = round21.b3 := rfl
  clear_value b3_27
  -- fg1_21: loop iteration 21 output
  extract_lets -merge +onlyGivenNames fg1_21 at hr
  have e_fg1_21 : fg1_21 = round21.fg1 := rfl
  clear_value fg1_21
  -- fg0_21: loop iteration 21 output
  extract_lets -merge +onlyGivenNames fg0_21 at hr
  have e_fg0_21 : fg0_21 = round21.fg0 := rfl
  clear_value fg0_21
  -- round22: loop iteration 22
  extract_lets -merge +onlyGivenNames round22 at hr
  have e_round22 : round22 = divsteps31Round bias ⟨a3_27, cnt_21, b3_27, fg1_21, fg0_21⟩ := rfl
  clear_value round22
  -- a3_28: loop iteration 22 output
  extract_lets -merge +onlyGivenNames a3_28 at hr
  have e_a3_28 : a3_28 = round22.a3 := rfl
  clear_value a3_28
  -- cnt_22: loop iteration 22 output
  extract_lets -merge +onlyGivenNames cnt_22 at hr
  have e_cnt_22 : cnt_22 = round22.cnt := rfl
  clear_value cnt_22
  -- b3_28: loop iteration 22 output
  extract_lets -merge +onlyGivenNames b3_28 at hr
  have e_b3_28 : b3_28 = round22.b3 := rfl
  clear_value b3_28
  -- fg1_22: loop iteration 22 output
  extract_lets -merge +onlyGivenNames fg1_22 at hr
  have e_fg1_22 : fg1_22 = round22.fg1 := rfl
  clear_value fg1_22
  -- fg0_22: loop iteration 22 output
  extract_lets -merge +onlyGivenNames fg0_22 at hr
  have e_fg0_22 : fg0_22 = round22.fg0 := rfl
  clear_value fg0_22
  -- round23: loop iteration 23
  extract_lets -merge +onlyGivenNames round23 at hr
  have e_round23 : round23 = divsteps31Round bias ⟨a3_28, cnt_22, b3_28, fg1_22, fg0_22⟩ := rfl
  clear_value round23
  -- a3_29: loop iteration 23 output
  extract_lets -merge +onlyGivenNames a3_29 at hr
  have e_a3_29 : a3_29 = round23.a3 := rfl
  clear_value a3_29
  -- cnt_23: loop iteration 23 output
  extract_lets -merge +onlyGivenNames cnt_23 at hr
  have e_cnt_23 : cnt_23 = round23.cnt := rfl
  clear_value cnt_23
  -- b3_29: loop iteration 23 output
  extract_lets -merge +onlyGivenNames b3_29 at hr
  have e_b3_29 : b3_29 = round23.b3 := rfl
  clear_value b3_29
  -- fg1_23: loop iteration 23 output
  extract_lets -merge +onlyGivenNames fg1_23 at hr
  have e_fg1_23 : fg1_23 = round23.fg1 := rfl
  clear_value fg1_23
  -- fg0_23: loop iteration 23 output
  extract_lets -merge +onlyGivenNames fg0_23 at hr
  have e_fg0_23 : fg0_23 = round23.fg0 := rfl
  clear_value fg0_23
  -- round24: loop iteration 24
  extract_lets -merge +onlyGivenNames round24 at hr
  have e_round24 : round24 = divsteps31Round bias ⟨a3_29, cnt_23, b3_29, fg1_23, fg0_23⟩ := rfl
  clear_value round24
  -- a3_30: loop iteration 24 output
  extract_lets -merge +onlyGivenNames a3_30 at hr
  have e_a3_30 : a3_30 = round24.a3 := rfl
  clear_value a3_30
  -- cnt_24: loop iteration 24 output
  extract_lets -merge +onlyGivenNames cnt_24 at hr
  have e_cnt_24 : cnt_24 = round24.cnt := rfl
  clear_value cnt_24
  -- b3_30: loop iteration 24 output
  extract_lets -merge +onlyGivenNames b3_30 at hr
  have e_b3_30 : b3_30 = round24.b3 := rfl
  clear_value b3_30
  -- fg1_24: loop iteration 24 output
  extract_lets -merge +onlyGivenNames fg1_24 at hr
  have e_fg1_24 : fg1_24 = round24.fg1 := rfl
  clear_value fg1_24
  -- fg0_24: loop iteration 24 output
  extract_lets -merge +onlyGivenNames fg0_24 at hr
  have e_fg0_24 : fg0_24 = round24.fg0 := rfl
  clear_value fg0_24
  -- round25: loop iteration 25
  extract_lets -merge +onlyGivenNames round25 at hr
  have e_round25 : round25 = divsteps31Round bias ⟨a3_30, cnt_24, b3_30, fg1_24, fg0_24⟩ := rfl
  clear_value round25
  -- a3_31: loop iteration 25 output
  extract_lets -merge +onlyGivenNames a3_31 at hr
  have e_a3_31 : a3_31 = round25.a3 := rfl
  clear_value a3_31
  -- cnt_25: loop iteration 25 output
  extract_lets -merge +onlyGivenNames cnt_25 at hr
  have e_cnt_25 : cnt_25 = round25.cnt := rfl
  clear_value cnt_25
  -- b3_31: loop iteration 25 output
  extract_lets -merge +onlyGivenNames b3_31 at hr
  have e_b3_31 : b3_31 = round25.b3 := rfl
  clear_value b3_31
  -- fg1_25: loop iteration 25 output
  extract_lets -merge +onlyGivenNames fg1_25 at hr
  have e_fg1_25 : fg1_25 = round25.fg1 := rfl
  clear_value fg1_25
  -- fg0_25: loop iteration 25 output
  extract_lets -merge +onlyGivenNames fg0_25 at hr
  have e_fg0_25 : fg0_25 = round25.fg0 := rfl
  clear_value fg0_25
  -- round26: loop iteration 26
  extract_lets -merge +onlyGivenNames round26 at hr
  have e_round26 : round26 = divsteps31Round bias ⟨a3_31, cnt_25, b3_31, fg1_25, fg0_25⟩ := rfl
  clear_value round26
  -- a3_32: loop iteration 26 output
  extract_lets -merge +onlyGivenNames a3_32 at hr
  have e_a3_32 : a3_32 = round26.a3 := rfl
  clear_value a3_32
  -- cnt_26: loop iteration 26 output
  extract_lets -merge +onlyGivenNames cnt_26 at hr
  have e_cnt_26 : cnt_26 = round26.cnt := rfl
  clear_value cnt_26
  -- b3_32: loop iteration 26 output
  extract_lets -merge +onlyGivenNames b3_32 at hr
  have e_b3_32 : b3_32 = round26.b3 := rfl
  clear_value b3_32
  -- fg1_26: loop iteration 26 output
  extract_lets -merge +onlyGivenNames fg1_26 at hr
  have e_fg1_26 : fg1_26 = round26.fg1 := rfl
  clear_value fg1_26
  -- fg0_26: loop iteration 26 output
  extract_lets -merge +onlyGivenNames fg0_26 at hr
  have e_fg0_26 : fg0_26 = round26.fg0 := rfl
  clear_value fg0_26
  -- round27: loop iteration 27
  extract_lets -merge +onlyGivenNames round27 at hr
  have e_round27 : round27 = divsteps31Round bias ⟨a3_32, cnt_26, b3_32, fg1_26, fg0_26⟩ := rfl
  clear_value round27
  -- a3_33: loop iteration 27 output
  extract_lets -merge +onlyGivenNames a3_33 at hr
  have e_a3_33 : a3_33 = round27.a3 := rfl
  clear_value a3_33
  -- cnt_27: loop iteration 27 output
  extract_lets -merge +onlyGivenNames cnt_27 at hr
  have e_cnt_27 : cnt_27 = round27.cnt := rfl
  clear_value cnt_27
  -- b3_33: loop iteration 27 output
  extract_lets -merge +onlyGivenNames b3_33 at hr
  have e_b3_33 : b3_33 = round27.b3 := rfl
  clear_value b3_33
  -- fg1_27: loop iteration 27 output
  extract_lets -merge +onlyGivenNames fg1_27 at hr
  have e_fg1_27 : fg1_27 = round27.fg1 := rfl
  clear_value fg1_27
  -- fg0_27: loop iteration 27 output
  extract_lets -merge +onlyGivenNames fg0_27 at hr
  have e_fg0_27 : fg0_27 = round27.fg0 := rfl
  clear_value fg0_27
  -- round28: loop iteration 28
  extract_lets -merge +onlyGivenNames round28 at hr
  have e_round28 : round28 = divsteps31Round bias ⟨a3_33, cnt_27, b3_33, fg1_27, fg0_27⟩ := rfl
  clear_value round28
  -- a3_34: loop iteration 28 output
  extract_lets -merge +onlyGivenNames a3_34 at hr
  have e_a3_34 : a3_34 = round28.a3 := rfl
  clear_value a3_34
  -- cnt_28: loop iteration 28 output
  extract_lets -merge +onlyGivenNames cnt_28 at hr
  have e_cnt_28 : cnt_28 = round28.cnt := rfl
  clear_value cnt_28
  -- b3_34: loop iteration 28 output
  extract_lets -merge +onlyGivenNames b3_34 at hr
  have e_b3_34 : b3_34 = round28.b3 := rfl
  clear_value b3_34
  -- fg1_28: loop iteration 28 output
  extract_lets -merge +onlyGivenNames fg1_28 at hr
  have e_fg1_28 : fg1_28 = round28.fg1 := rfl
  clear_value fg1_28
  -- fg0_28: loop iteration 28 output
  extract_lets -merge +onlyGivenNames fg0_28 at hr
  have e_fg0_28 : fg0_28 = round28.fg0 := rfl
  clear_value fg0_28
  -- round29: loop iteration 29
  extract_lets -merge +onlyGivenNames round29 at hr
  have e_round29 : round29 = divsteps31Round bias ⟨a3_34, cnt_28, b3_34, fg1_28, fg0_28⟩ := rfl
  clear_value round29
  -- a3_35: loop iteration 29 output
  extract_lets -merge +onlyGivenNames a3_35 at hr
  have e_a3_35 : a3_35 = round29.a3 := rfl
  clear_value a3_35
  -- cnt_29: loop iteration 29 output
  extract_lets -merge +onlyGivenNames cnt_29 at hr
  have e_cnt_29 : cnt_29 = round29.cnt := rfl
  clear_value cnt_29
  -- b3_35: loop iteration 29 output
  extract_lets -merge +onlyGivenNames b3_35 at hr
  have e_b3_35 : b3_35 = round29.b3 := rfl
  clear_value b3_35
  -- fg1_29: loop iteration 29 output
  extract_lets -merge +onlyGivenNames fg1_29 at hr
  have e_fg1_29 : fg1_29 = round29.fg1 := rfl
  clear_value fg1_29
  -- fg0_29: loop iteration 29 output
  extract_lets -merge +onlyGivenNames fg0_29 at hr
  have e_fg0_29 : fg0_29 = round29.fg0 := rfl
  clear_value fg0_29
  -- round30: loop iteration 30
  extract_lets -merge +onlyGivenNames round30 at hr
  have e_round30 : round30 = divsteps31Round bias ⟨a3_35, cnt_29, b3_35, fg1_29, fg0_29⟩ := rfl
  clear_value round30
  -- a3_36: loop iteration 30 output
  extract_lets -merge +onlyGivenNames a3_36 at hr
  have e_a3_36 : a3_36 = round30.a3 := rfl
  clear_value a3_36
  -- cnt_30: loop iteration 30 output
  extract_lets -merge +onlyGivenNames cnt_30 at hr
  have e_cnt_30 : cnt_30 = round30.cnt := rfl
  clear_value cnt_30
  -- b3_36: loop iteration 30 output
  extract_lets -merge +onlyGivenNames b3_36 at hr
  have e_b3_36 : b3_36 = round30.b3 := rfl
  clear_value b3_36
  -- fg1_30: loop iteration 30 output
  extract_lets -merge +onlyGivenNames fg1_30 at hr
  have e_fg1_30 : fg1_30 = round30.fg1 := rfl
  clear_value fg1_30
  -- fg0_30: loop iteration 30 output
  extract_lets -merge +onlyGivenNames fg0_30 at hr
  have e_fg0_30 : fg0_30 = round30.fg0 := rfl
  clear_value fg0_30
  -- round31: loop iteration 31
  extract_lets -merge +onlyGivenNames round31 at hr
  have e_round31 : round31 = divsteps31Round bias ⟨a3_36, cnt_30, b3_36, fg1_30, fg0_30⟩ := rfl
  clear_value round31
  -- fg1_31: loop iteration 31 output
  extract_lets -merge +onlyGivenNames fg1_31 at hr
  have e_fg1_31 : fg1_31 = round31.fg1 := rfl
  clear_value fg1_31
  -- fg0_31: loop iteration 31 output
  extract_lets -merge +onlyGivenNames fg0_31 at hr
  have e_fg0_31 : fg0_31 = round31.fg0 := rfl
  clear_value fg0_31
  -- bias_1: ubfx bias,bias,#0,#32
  extract_lets -merge +onlyGivenNames bias_1 at hr
  have e_bias_1 : bias_1 = ubfx bias 0 32 := rfl
  clear_value bias_1
  have b_bias_1 : bias_1 < 2^64 := by rw [e_bias_1]; exact ubfx_lt _ _ _
  -- f0: ubfx f0,fg0,#0,#32
  extract_lets -merge +onlyGivenNames f0 at hr
  have e_f0 : f0 = ubfx fg0_31 0 32 := rfl
  clear_value f0
  have b_f0 : f0 < 2^64 := by rw [e_f0]; exact ubfx_lt _ _ _
  -- g0: ubfx g0,fg0,#32,#32
  extract_lets -merge +onlyGivenNames g0 at hr
  have e_g0 : g0 = ubfx fg0_31 32 32 := rfl
  clear_value g0
  have b_g0 : g0 < 2^64 := by rw [e_g0]; exact ubfx_lt _ _ _
  -- f1: ubfx f1,fg1,#0,#32
  extract_lets -merge +onlyGivenNames f1 at hr
  have e_f1 : f1 = ubfx fg1_31 0 32 := rfl
  clear_value f1
  have b_f1 : f1 < 2^64 := by rw [e_f1]; exact ubfx_lt _ _ _
  -- g1: ubfx g1,fg1,#32,#32
  extract_lets -merge +onlyGivenNames g1 at hr
  have e_g1 : g1 = ubfx fg1_31 32 32 := rfl
  clear_value g1
  have b_g1 : g1 < 2^64 := by rw [e_g1]; exact ubfx_lt _ _ _
  -- f0_1: sub f0,f0,bias
  extract_lets -merge +onlyGivenNames f0_1 at hr
  have e_f0_1 : f0_1 = sub f0 bias_1 := rfl
  clear_value f0_1
  have b_f0_1 : f0_1 < 2^64 := by rw [e_f0_1]; exact sub_lt _ _
  -- g0_1: sub g0,g0,bias
  extract_lets -merge +onlyGivenNames g0_1 at hr
  have e_g0_1 : g0_1 = sub g0 bias_1 := rfl
  clear_value g0_1
  have b_g0_1 : g0_1 < 2^64 := by rw [e_g0_1]; exact sub_lt _ _
  -- f1_1: sub f1,f1,bias
  extract_lets -merge +onlyGivenNames f1_1 at hr
  have e_f1_1 : f1_1 = sub f1 bias_1 := rfl
  clear_value f1_1
  have b_f1_1 : f1_1 < 2^64 := by rw [e_f1_1]; exact sub_lt _ _
  -- g1_1: sub g1,g1,bias
  extract_lets -merge +onlyGivenNames g1_1 at hr
  have e_g1_1 : g1_1 = sub g1 bias_1 := rfl
  clear_value g1_1
  have b_g1_1 : g1_1 < 2^64 := by rw [e_g1_1]; exact sub_lt _ _
  subst hr
  -- BEGIN divsteps31 conclusion
  have hmatch1 : round1.Matches (forwardSteps 1 abstract0) := by
    rw [e_round1, hbias, forwardSteps]
    exact hmatch0.next
  clear hmatch0
  have hmatch2 : round2.Matches (forwardSteps 2 abstract0) := by
    rw [e_round2, hbias, forwardSteps]
    simpa only [e_a3_7, e_cnt_1, e_b3_7, e_fg1_1, e_fg0_1] using hmatch1.next
  clear hmatch1
  have hmatch3 : round3.Matches (forwardSteps 3 abstract0) := by
    rw [e_round3, hbias, forwardSteps]
    simpa only [e_a3_8, e_cnt_2, e_b3_8, e_fg1_2, e_fg0_2] using hmatch2.next
  clear hmatch2
  have hmatch4 : round4.Matches (forwardSteps 4 abstract0) := by
    rw [e_round4, hbias, forwardSteps]
    simpa only [e_a3_9, e_cnt_3, e_b3_9, e_fg1_3, e_fg0_3] using hmatch3.next
  clear hmatch3
  have hmatch5 : round5.Matches (forwardSteps 5 abstract0) := by
    rw [e_round5, hbias, forwardSteps]
    simpa only [e_a3_10, e_cnt_4, e_b3_10, e_fg1_4, e_fg0_4] using hmatch4.next
  clear hmatch4
  have hmatch6 : round6.Matches (forwardSteps 6 abstract0) := by
    rw [e_round6, hbias, forwardSteps]
    simpa only [e_a3_11, e_cnt_5, e_b3_11, e_fg1_5, e_fg0_5] using hmatch5.next
  clear hmatch5
  have hmatch7 : round7.Matches (forwardSteps 7 abstract0) := by
    rw [e_round7, hbias, forwardSteps]
    simpa only [e_a3_12, e_cnt_6, e_b3_12, e_fg1_6, e_fg0_6] using hmatch6.next
  clear hmatch6
  have hmatch8 : round8.Matches (forwardSteps 8 abstract0) := by
    rw [e_round8, hbias, forwardSteps]
    simpa only [e_a3_13, e_cnt_7, e_b3_13, e_fg1_7, e_fg0_7] using hmatch7.next
  clear hmatch7
  have hmatch9 : round9.Matches (forwardSteps 9 abstract0) := by
    rw [e_round9, hbias, forwardSteps]
    simpa only [e_a3_14, e_cnt_8, e_b3_14, e_fg1_8, e_fg0_8] using hmatch8.next
  clear hmatch8
  have hmatch10 : round10.Matches (forwardSteps 10 abstract0) := by
    rw [e_round10, hbias, forwardSteps]
    simpa only [e_a3_15, e_cnt_9, e_b3_15, e_fg1_9, e_fg0_9] using hmatch9.next
  clear hmatch9
  have hmatch11 : round11.Matches (forwardSteps 11 abstract0) := by
    rw [e_round11, hbias, forwardSteps]
    simpa only [e_a3_16, e_cnt_10, e_b3_16, e_fg1_10, e_fg0_10] using hmatch10.next
  clear hmatch10
  have hmatch12 : round12.Matches (forwardSteps 12 abstract0) := by
    rw [e_round12, hbias, forwardSteps]
    simpa only [e_a3_17, e_cnt_11, e_b3_17, e_fg1_11, e_fg0_11] using hmatch11.next
  clear hmatch11
  have hmatch13 : round13.Matches (forwardSteps 13 abstract0) := by
    rw [e_round13, hbias, forwardSteps]
    simpa only [e_a3_18, e_cnt_12, e_b3_18, e_fg1_12, e_fg0_12] using hmatch12.next
  clear hmatch12
  have hmatch14 : round14.Matches (forwardSteps 14 abstract0) := by
    rw [e_round14, hbias, forwardSteps]
    simpa only [e_a3_19, e_cnt_13, e_b3_19, e_fg1_13, e_fg0_13] using hmatch13.next
  clear hmatch13
  have hmatch15 : round15.Matches (forwardSteps 15 abstract0) := by
    rw [e_round15, hbias, forwardSteps]
    simpa only [e_a3_20, e_cnt_14, e_b3_20, e_fg1_14, e_fg0_14] using hmatch14.next
  clear hmatch14
  have hmatch16 : round16.Matches (forwardSteps 16 abstract0) := by
    rw [e_round16, hbias, forwardSteps]
    simpa only [e_a3_21, e_cnt_15, e_b3_21, e_fg1_15, e_fg0_15] using hmatch15.next
  clear hmatch15
  have hmatch17 : round17.Matches (forwardSteps 17 abstract0) := by
    rw [e_round17, hbias, forwardSteps]
    simpa only [e_a3_22, e_cnt_16, e_b3_22, e_fg1_16, e_fg0_16] using hmatch16.next
  clear hmatch16
  have hmatch18 : round18.Matches (forwardSteps 18 abstract0) := by
    rw [e_round18, hbias, forwardSteps]
    simpa only [e_a3_23, e_cnt_17, e_b3_23, e_fg1_17, e_fg0_17] using hmatch17.next
  clear hmatch17
  have hmatch19 : round19.Matches (forwardSteps 19 abstract0) := by
    rw [e_round19, hbias, forwardSteps]
    simpa only [e_a3_24, e_cnt_18, e_b3_24, e_fg1_18, e_fg0_18] using hmatch18.next
  clear hmatch18
  have hmatch20 : round20.Matches (forwardSteps 20 abstract0) := by
    rw [e_round20, hbias, forwardSteps]
    simpa only [e_a3_25, e_cnt_19, e_b3_25, e_fg1_19, e_fg0_19] using hmatch19.next
  clear hmatch19
  have hmatch21 : round21.Matches (forwardSteps 21 abstract0) := by
    rw [e_round21, hbias, forwardSteps]
    simpa only [e_a3_26, e_cnt_20, e_b3_26, e_fg1_20, e_fg0_20] using hmatch20.next
  clear hmatch20
  have hmatch22 : round22.Matches (forwardSteps 22 abstract0) := by
    rw [e_round22, hbias, forwardSteps]
    simpa only [e_a3_27, e_cnt_21, e_b3_27, e_fg1_21, e_fg0_21] using hmatch21.next
  clear hmatch21
  have hmatch23 : round23.Matches (forwardSteps 23 abstract0) := by
    rw [e_round23, hbias, forwardSteps]
    simpa only [e_a3_28, e_cnt_22, e_b3_28, e_fg1_22, e_fg0_22] using hmatch22.next
  clear hmatch22
  have hmatch24 : round24.Matches (forwardSteps 24 abstract0) := by
    rw [e_round24, hbias, forwardSteps]
    simpa only [e_a3_29, e_cnt_23, e_b3_29, e_fg1_23, e_fg0_23] using hmatch23.next
  clear hmatch23
  have hmatch25 : round25.Matches (forwardSteps 25 abstract0) := by
    rw [e_round25, hbias, forwardSteps]
    simpa only [e_a3_30, e_cnt_24, e_b3_30, e_fg1_24, e_fg0_24] using hmatch24.next
  clear hmatch24
  have hmatch26 : round26.Matches (forwardSteps 26 abstract0) := by
    rw [e_round26, hbias, forwardSteps]
    simpa only [e_a3_31, e_cnt_25, e_b3_31, e_fg1_25, e_fg0_25] using hmatch25.next
  clear hmatch25
  have hmatch27 : round27.Matches (forwardSteps 27 abstract0) := by
    rw [e_round27, hbias, forwardSteps]
    simpa only [e_a3_32, e_cnt_26, e_b3_32, e_fg1_26, e_fg0_26] using hmatch26.next
  clear hmatch26
  have hmatch28 : round28.Matches (forwardSteps 28 abstract0) := by
    rw [e_round28, hbias, forwardSteps]
    simpa only [e_a3_33, e_cnt_27, e_b3_33, e_fg1_27, e_fg0_27] using hmatch27.next
  clear hmatch27
  have hmatch29 : round29.Matches (forwardSteps 29 abstract0) := by
    rw [e_round29, hbias, forwardSteps]
    simpa only [e_a3_34, e_cnt_28, e_b3_34, e_fg1_28, e_fg0_28] using hmatch28.next
  clear hmatch28
  have hmatch30 : round30.Matches (forwardSteps 30 abstract0) := by
    rw [e_round30, hbias, forwardSteps]
    simpa only [e_a3_35, e_cnt_29, e_b3_35, e_fg1_29, e_fg0_29] using hmatch29.next
  clear hmatch29
  have hmatch31 : round31.Matches (forwardSteps 31 abstract0) := by
    rw [e_round31, hbias, forwardSteps]
    simpa only [e_a3_36, e_cnt_30, e_b3_36, e_fg1_30, e_fg0_30] using hmatch30.next
  clear hmatch30
  rw [forwardSteps_eq_approxSteps] at hmatch31
  have hfinal : round31.Matches (semolinaShort a.toNat b.toNat) := by
    simpa only [semolinaShort, abstract0] using hmatch31
  rcases hfinal with ⟨hbounded, _, _, hrow0Final, hrow1Final, _⟩
  have hbiasLane : bias_1 = packedLaneBias := by
    rw [e_bias_1, hbias]
    norm_num [ubfx, lsr, PastaAsm.word, packedRowBias, packedLaneBias]
  have hrowBounds := semolinaShort_biasBounded a.toNat b.toNat
  have hdecode0 := packedRowRep_decode hrow0Final hrowBounds.1 hbounded.2.2.2.2
  have hdecode1 := packedRowRep_decode hrow1Final hrowBounds.2 hbounded.2.2.2.1
  refine ⟨?_, semolinaShort_matrix_bounded a.toNat b.toNat⟩
  simpa only [InvertMatrixRep, e_f0_1, e_g0_1, e_f1_1, e_g1_1, e_f0, e_g0,
    e_f1, e_g1, e_fg0_31, e_fg1_31, hbiasLane] using
    And.intro hdecode0.1 (And.intro hdecode0.2 (And.intro hdecode1.1 hdecode1.2))
  -- END divsteps31 conclusion

end PastaAsm.AArch64
