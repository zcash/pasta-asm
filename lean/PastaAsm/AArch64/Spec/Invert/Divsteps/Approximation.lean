/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.AArch64.Spec.Invert.Divsteps.Packed

/-!
# Approximation initialization for AArch64 inversion divsteps

Arithmetic and bit-window lemmas connecting the checked AArch64 wrapper prelude to
`semolinaApprox`.
-/

namespace PastaAsm.AArch64

open PastaAsm.InversionConvergence

private theorem size_or (x y : Nat) :
    Nat.size (x ||| y) = max (Nat.size x) (Nat.size y) := by
  apply le_antisymm
  · rw [Nat.size_le]
    apply Nat.bitwise_lt_two_pow
    · exact (Nat.lt_size_self x).trans_le
        (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
    · exact (Nat.lt_size_self y).trans_le
        (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))
  · apply max_le
    · apply Nat.size_le_size
      apply Nat.le_of_testBit
      intro i hi
      simp [Nat.testBit_or, hi]
    · apply Nat.size_le_size
      apply Nat.le_of_testBit
      intro i hi
      simp [Nat.testBit_or, hi]

private theorem size_eq_log2_add_one {x : Nat} (hx : x ≠ 0) :
    Nat.size x = Nat.log2 x + 1 := by
  apply le_antisymm
  · exact Nat.size_le.mpr (Nat.lt_log2_self (n := x))
  · have hlt : Nat.log2 x < Nat.size x :=
      Nat.lt_size.mpr (Nat.log2_self_le hx)
    omega

private theorem or_eq_zero_iff (x y : Nat) : x ||| y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have hs := size_or x y
    rw [h, Nat.size_zero] at hs
    exact ⟨Nat.size_eq_zero.mp (by omega), Nat.size_eq_zero.mp (by omega)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem pred_mul_add_pred {a b : Nat} (ha : 0 < a) (hb : 0 < b) :
    (a - 1) * b + (b - 1) = a * b - 1 := by
  calc
    (a - 1) * b + (b - 1) = ((a - 1) * b + b) - 1 :=
      (Nat.add_sub_assoc hb _).symm
    _ = a * b - 1 := by
      congr 1
      calc
        (a - 1) * b + b = ((a - 1) + 1) * b := by ring
        _ = a * b := by rw [Nat.sub_add_cancel ha]

private theorem size_add_pow_mul {low hi shift : Nat} (hlow : low < 2^shift)
    (hhi : hi ≠ 0) : Nat.size (low + 2^shift * hi) = shift + Nat.size hi := by
  have hspos : 0 < Nat.size hi := Nat.size_pos.mpr (Nat.pos_of_ne_zero hhi)
  apply le_antisymm
  · rw [Nat.size_le]
    have hlowLe : low ≤ 2^shift - 1 := Nat.le_sub_one_of_lt hlow
    have hhiLe : hi ≤ 2^(Nat.size hi) - 1 :=
      Nat.le_sub_one_of_lt (Nat.lt_size_self hi)
    calc
      low + 2^shift * hi ≤ (2^shift - 1) + 2^shift * (2^(Nat.size hi) - 1) :=
        Nat.add_le_add hlowLe (Nat.mul_le_mul_left _ hhiLe)
      _ = 2^(shift + Nat.size hi) - 1 := by
        rw [pow_add]
        simpa [Nat.mul_comm, Nat.add_comm] using
          (pred_mul_add_pred (a := 2^(Nat.size hi)) (b := 2^shift)
            (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide)))
      _ < 2^(shift + Nat.size hi) := Nat.sub_lt (by positivity) (by decide)
  · have hpowHi : 2^(Nat.size hi - 1) ≤ hi := by
      exact Nat.lt_size.mp (by omega)
    have hexp : shift + Nat.size hi - 1 = shift + (Nat.size hi - 1) := by omega
    have hlower : 2^(shift + Nat.size hi - 1) ≤ low + 2^shift * hi := by
      rw [hexp, pow_add]
      exact (Nat.mul_le_mul_left _ hpowHi).trans (Nat.le_add_left _ _)
    have hsize := Nat.lt_size.mpr hlower
    omega

private theorem max_size_add_pow_mul {lowA lowB hiA hiB shift : Nat}
    (hlowA : lowA < 2^shift) (hlowB : lowB < 2^shift) (hnz : hiA ||| hiB ≠ 0) :
    max (Nat.size (lowA + 2^shift * hiA)) (Nat.size (lowB + 2^shift * hiB)) =
      shift + Nat.size (hiA ||| hiB) := by
  rw [size_or]
  by_cases ha : hiA = 0
  · subst hiA
    have hb : hiB ≠ 0 := by simpa using hnz
    rw [size_add_pow_mul hlowB hb]
    simp only [Nat.mul_zero, Nat.add_zero, Nat.size_zero]
    have hlowSize : Nat.size lowA ≤ shift := Nat.size_le.mpr hlowA
    calc
      max (Nat.size lowA) (shift + Nat.size hiB) = shift + Nat.size hiB :=
        max_eq_right (by omega)
      _ = shift + max 0 (Nat.size hiB) := by simp
  · by_cases hb : hiB = 0
    · subst hiB
      rw [size_add_pow_mul hlowA ha]
      simp only [Nat.mul_zero, Nat.add_zero, Nat.size_zero]
      have hlowSize : Nat.size lowB ≤ shift := Nat.size_le.mpr hlowB
      calc
        max (shift + Nat.size hiA) (Nat.size lowB) = shift + Nat.size hiA :=
          max_eq_left (by omega)
        _ = shift + max (Nat.size hiA) 0 := by simp
    · rw [size_add_pow_mul hlowA ha, size_add_pow_mul hlowB hb]
      omega

/-- With bounded words, AArch64 OR is ordinary bitwise OR. -/
theorem orr_eq_or {x y : Nat} (hx : x < 2^64) (hy : y < 2^64) : orr x y = x ||| y := by
  unfold orr PastaAsm.word
  exact Nat.mod_eq_of_lt (Nat.bitwise_lt_two_pow hx hy)

private theorem cmp_zero_z_eq_zero_iff {x : Nat} (hx : x < 2^64) :
    (cmp x 0).z = 0 ↔ x ≠ 0 := by
  have hxmod : x % 18446744073709551616 = x := by
    exact Nat.mod_eq_of_lt (by simpa only [Nat.reducePow] using hx)
  have haddmod : (x + 18446744073709551616) % 18446744073709551616 = x := by omega
  unfold cmp subc
  norm_num only [Nat.reduceSubDiff, Nat.sub_zero]
  rw [haddmod, zeroFlag_eq_zero_iff]
  unfold PastaAsm.word PastaAsm.regMod
  rw [hxmod]

private theorem cmp_zero_z_eq_one_iff {x : Nat} (hx : x < 2^64) :
    (cmp x 0).z = 1 ↔ x = 0 := by
  have hxmod : x % 18446744073709551616 = x := by
    exact Nat.mod_eq_of_lt (by simpa only [Nat.reducePow] using hx)
  have haddmod : (x + 18446744073709551616) % 18446744073709551616 = x := by omega
  unfold cmp subc
  norm_num only [Nat.reduceSubDiff, Nat.sub_zero]
  rw [haddmod, zeroFlag_eq_one_iff]
  unfold PastaAsm.word PastaAsm.regMod
  rw [hxmod]

private theorem clz_eq_sub_size {x : Nat} (hx : x < 2^64) (hnz : x ≠ 0) :
    clz x = 64 - Nat.size x := by
  simp only [clz, if_neg hnz]
  have hs := size_eq_log2_add_one hnz
  have hsle : Nat.size x ≤ 64 := Nat.size_le.mpr hx
  omega

/-- The selected top two limbs after the wrapper's two conditional shifts encode
`value / 2^128`, except that values below `2^128` are selected exactly. -/
theorem select_top_pair
    {x0 x1 x2 x3 y0 y1 y2 y3 : Nat}
    (hx2 : x2 < 2^64) (hx3 : x3 < 2^64)
    (hy2 : y2 < 2^64) (hy3 : y3 < 2^64) :
    let z0 := (cmp (orr x3 y3) 0).z
    let sx3 := cselNe z0 x3 x2
    let sy3 := cselNe z0 y3 y2
    let sx2 := cselNe z0 x2 x1
    let sy2 := cselNe z0 y2 y1
    let z1 := (cmp (orr sx3 sy3) 0).z
    let tx3 := cselNe z1 sx3 sx2
    let ty3 := cselNe z1 sy3 sy2
    let tx2 := cselNe z1 sx2 x0
    let ty2 := cselNe z1 sy2 y0
    (tx2 + 2^64 * tx3, ty2 + 2^64 * ty3) =
      if x3 ≠ 0 ∨ y3 ≠ 0 then
        (x2 + 2^64 * x3, y2 + 2^64 * y3)
      else if x2 ≠ 0 ∨ y2 ≠ 0 then
        (x1 + 2^64 * x2, y1 + 2^64 * y2)
      else (x0 + 2^64 * x1, y0 + 2^64 * y1) := by
  dsimp [cselNe]
  have hor3 : orr x3 y3 < 2^64 := orr_lt _ _
  have hor2 : orr x2 y2 < 2^64 := orr_lt _ _
  by_cases h3 : x3 ≠ 0 ∨ y3 ≠ 0
  · have hz0 : (cmp (orr x3 y3) 0).z = 0 := by
      apply (cmp_zero_z_eq_zero_iff hor3).2
      rw [orr_eq_or hx3 hy3]
      intro hzero
      rw [or_eq_zero_iff] at hzero
      exact h3.elim (fun hx => hx hzero.1) (fun hy => hy hzero.2)
    simp [hz0, h3]
  · push Not at h3
    rcases h3 with ⟨rfl, rfl⟩
    have hz0 : (cmp (orr 0 0) 0).z = 1 := by decide
    by_cases h2 : x2 ≠ 0 ∨ y2 ≠ 0
    · have hz1 : (cmp (orr x2 y2) 0).z = 0 := by
        apply (cmp_zero_z_eq_zero_iff hor2).2
        rw [orr_eq_or hx2 hy2]
        intro hzero
        rw [or_eq_zero_iff] at hzero
        exact h2.elim (fun hx => hx hzero.1) (fun hy => hy hzero.2)
      simp [hz0, hz1, h2]
    · push Not at h2
      rcases h2 with ⟨rfl, rfl⟩
      simp [hz0]

private theorem cmp_64_z_eq_zero {x : Nat} (hx : x < 64) : (cmp x 64).z = 0 := by
  have hval : x + 2^64 - 64 < 2^64 := by omega
  have hpos : 0 < x + 2^64 - 64 := by omega
  have hmod : (x + 18446744073709551616 - 64) % 18446744073709551616 =
      x + 18446744073709551616 - 64 := by
    exact Nat.mod_eq_of_lt (by simpa only [Nat.reducePow] using hval)
  unfold cmp subc
  norm_num only [Nat.reduceSubDiff]
  rw [show x + 18446744073709551616 - 64 - 0 =
    x + 18446744073709551616 - 64 by omega]
  rw [hmod, zeroFlag_eq_zero_iff]
  unfold PastaAsm.word PastaAsm.regMod
  rw [Nat.mod_eq_of_lt (by simpa only [Nat.reducePow] using hval)]
  exact Nat.ne_of_gt (by simpa only [Nat.reducePow] using hpos)

private theorem neg_eq_sub {x : Nat} (hx : 0 < x) (hle : x ≤ 64) :
    neg x = 2^64 - x := by
  unfold neg sub subc
  norm_num only [Nat.reduceSubDiff, Nat.zero_add]
  change (2^64 - x) % 2^64 = 2^64 - x
  rw [Nat.mod_eq_of_lt]
  omega

private theorem asr_neg_small {x : Nat} (hx : 0 < x) (hle : x < 64) :
    asr (neg x) 6 = 2^64 - 1 := by
  rw [neg_eq_sub hx hle.le]
  unfold asr PastaAsm.word PastaAsm.regMod
  rw [Nat.mod_eq_of_lt (by omega : 2^64 - x < 2^64)]
  rw [if_neg (by omega : ¬ 2^64 - x < 2^63)]
  rw [show (2^64 - x) / 2^6 = 2^58 - 1 by omega]
  norm_num

private theorem bitAnd_max {x : Nat} (hx : x < 2^64) : bitAnd x (2^64 - 1) = x :=
  and_allOnes x hx

/-- One component of the final shared CLZ-controlled AArch64 window stage. -/
def finishWindow (high low fallback otherHigh : Nat) : Nat :=
  let topOr := orr high otherHigh
  let count := clz topOr
  let z := (cmp count 64).z
  let count := cselNe z count 0
  let negCount := neg count
  let upper := lslv (cselNe z high fallback) count
  let lower := bitAnd (lsrv low negCount) (asr negCount 6)
  orr upper lower

private theorem finishWindow_zero {high low fallback otherHigh : Nat}
    (hfallback : fallback < 2^64) (hh : high = 0) (ho : otherHigh = 0) :
    finishWindow high low fallback otherHigh = fallback := by
  subst high
  subst otherHigh
  have horr : orr 0 0 = 0 := by decide
  have hclz : clz 0 = 64 := by decide
  have hcmp : (cmp 64 64).z = 1 := by decide
  have hneg : neg 0 = 0 := by decide
  unfold finishWindow
  dsimp only
  rw [horr, hclz, hcmp]
  simp only [cselNe, one_ne_zero, ↓reduceIte, hneg]
  have hupper : lslv fallback 0 = fallback := by
    unfold lslv lsl PastaAsm.regMod
    norm_num only [Nat.zero_mod, pow_zero, Nat.mul_one]
    exact Nat.mod_eq_of_lt hfallback
  have hlower : bitAnd (lsrv low 0) (asr 0 6) = 0 := by
    rw [show asr 0 6 = 0 by decide, and_zero]
  rw [hupper, hlower]
  unfold orr PastaAsm.word
  simpa only [Nat.or_zero] using Nat.mod_eq_of_lt hfallback

private theorem finishWindow_div {high low fallback otherHigh : Nat}
    (hhigh : high < 2^64) (hlow : low < 2^64) (_hfallback : fallback < 2^64)
    (hother : otherHigh < 2^64) (hnz : high ||| otherHigh ≠ 0) :
    finishWindow high low fallback otherHigh / 2^31 =
      (low + 2^64 * high) / 2^(Nat.size (high ||| otherHigh) + 31) := by
  have horLt : high ||| otherHigh < 2^64 := Nat.bitwise_lt_two_pow hhigh hother
  have horr : orr high otherHigh = high ||| otherHigh := by
    unfold orr PastaAsm.word
    exact Nat.mod_eq_of_lt horLt
  have hspos : 0 < Nat.size (high ||| otherHigh) :=
    Nat.size_pos.mpr (Nat.pos_of_ne_zero hnz)
  have hsle : Nat.size (high ||| otherHigh) ≤ 64 := Nat.size_le.mpr horLt
  have hclz : clz (orr high otherHigh) = 64 - Nat.size (high ||| otherHigh) := by
    rw [horr]
    exact clz_eq_sub_size horLt hnz
  by_cases hs64 : Nat.size (high ||| otherHigh) = 64
  · have hcount : clz (orr high otherHigh) = 0 := by omega
    have hz : (cmp 0 64).z = 0 := cmp_64_z_eq_zero (by omega)
    have hfinish : finishWindow high low fallback otherHigh = high := by
      simp only [finishWindow, hcount, hz, cselNe, if_pos]
      norm_num [neg, sub, subc, lslv, lsl, lsrv, lsr, asr, bitAnd, orr,
        PastaAsm.word, PastaAsm.regMod]
      exact hhigh
    have hinner : (low + 2^64 * high) / 2^64 = high := by
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlow, Nat.zero_add]
    rw [hfinish, hs64, pow_add, ← Nat.div_div_eq_div_mul, hinner]
  · have hslt : Nat.size (high ||| otherHigh) < 64 := by omega
    have hcountPos : 0 < 64 - Nat.size (high ||| otherHigh) := by omega
    have hcountLt : 64 - Nat.size (high ||| otherHigh) < 64 := by omega
    have hz : (cmp (clz (orr high otherHigh)) 64).z = 0 := by
      apply cmp_64_z_eq_zero
      omega
    have hneg : neg (64 - Nat.size (high ||| otherHigh)) =
        2^64 - (64 - Nat.size (high ||| otherHigh)) :=
      neg_eq_sub hcountPos hcountLt.le
    have hmod : (2^64 - (64 - Nat.size (high ||| otherHigh))) % 64 =
        Nat.size (high ||| otherHigh) := by omega
    have hmask : asr (neg (64 - Nat.size (high ||| otherHigh))) 6 = 2^64 - 1 :=
      asr_neg_small hcountPos hcountLt
    have hsplit : Nat.size (high ||| otherHigh) +
        (64 - Nat.size (high ||| otherHigh)) = 64 := Nat.add_sub_of_le hsle
    have hhighSize : Nat.size high ≤ Nat.size (high ||| otherHigh) := by
      rw [size_or]
      exact Nat.le_max_left _ _
    have hhighPow : high < 2^(Nat.size (high ||| otherHigh)) :=
      (Nat.lt_size_self high).trans_le (Nat.pow_le_pow_right (by decide) hhighSize)
    have hupperLt : high * 2^(64 - Nat.size (high ||| otherHigh)) < 2^64 := by
      calc
        high * 2^(64 - Nat.size (high ||| otherHigh)) <
            2^(Nat.size (high ||| otherHigh)) *
              2^(64 - Nat.size (high ||| otherHigh)) :=
          Nat.mul_lt_mul_of_pos_right hhighPow (by positivity)
        _ = 2^64 := by rw [← pow_add, hsplit]
    have hsplit' : (64 - Nat.size (high ||| otherHigh)) +
        Nat.size (high ||| otherHigh) = 64 := by omega
    have hlowerLt : low / 2^(Nat.size (high ||| otherHigh)) <
        2^(64 - Nat.size (high ||| otherHigh)) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, hsplit']
      exact hlow
    have hsumLt : high * 2^(64 - Nat.size (high ||| otherHigh)) +
        low / 2^(Nat.size (high ||| otherHigh)) < 2^64 := by
      have hmulLe : high * 2^(64 - Nat.size (high ||| otherHigh)) ≤
          (2^(Nat.size (high ||| otherHigh)) - 1) *
            2^(64 - Nat.size (high ||| otherHigh)) :=
        Nat.mul_le_mul_right _ (Nat.le_sub_one_of_lt hhighPow)
      have hdivLe : low / 2^(Nat.size (high ||| otherHigh)) ≤
          2^(64 - Nat.size (high ||| otherHigh)) - 1 :=
        Nat.le_sub_one_of_lt hlowerLt
      have hp : 2^(Nat.size (high ||| otherHigh)) *
          2^(64 - Nat.size (high ||| otherHigh)) = 2^64 := by
        rw [← pow_add, hsplit]
      calc
        high * 2^(64 - Nat.size (high ||| otherHigh)) +
            low / 2^(Nat.size (high ||| otherHigh)) ≤
            (2^(Nat.size (high ||| otherHigh)) - 1) *
              2^(64 - Nat.size (high ||| otherHigh)) +
              (2^(64 - Nat.size (high ||| otherHigh)) - 1) :=
          Nat.add_le_add hmulLe hdivLe
        _ = 2^64 - 1 := by
          rw [← hp]
          exact pred_mul_add_pred (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
        _ < 2^64 := Nat.sub_lt (by positivity) (by decide)
    have hz' : (cmp (64 - Nat.size (high ||| otherHigh)) 64).z = 0 := by
      rw [← hclz]
      exact hz
    have hupper : lslv high (64 - Nat.size (high ||| otherHigh)) =
        high * 2^(64 - Nat.size (high ||| otherHigh)) := by
      unfold lslv lsl PastaAsm.regMod
      rw [Nat.mod_eq_of_lt hcountLt, Nat.mod_eq_of_lt hupperLt]
    have hlower : bitAnd
          (lsrv low (neg (64 - Nat.size (high ||| otherHigh))))
          (asr (neg (64 - Nat.size (high ||| otherHigh))) 6) =
        low / 2^(Nat.size (high ||| otherHigh)) := by
      rw [hmask, hneg]
      unfold lsrv lsr PastaAsm.word PastaAsm.regMod
      rw [hmod, Nat.mod_eq_of_lt hlow, bitAnd_max]
      exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hlow
    have hor : high * 2^(64 - Nat.size (high ||| otherHigh)) |||
        low / 2^(Nat.size (high ||| otherHigh)) =
        high * 2^(64 - Nat.size (high ||| otherHigh)) +
          low / 2^(Nat.size (high ||| otherHigh)) := by
      simpa [Nat.mul_comm] using
        (Nat.two_pow_add_eq_or_of_lt hlowerLt high).symm
    have hfinish : finishWindow high low fallback otherHigh =
        high * 2^(64 - Nat.size (high ||| otherHigh)) +
          low / 2^(Nat.size (high ||| otherHigh)) := by
      simp only [finishWindow, hclz, hz', cselNe, if_pos]
      rw [hupper, hlower]
      unfold orr PastaAsm.word PastaAsm.regMod
      rw [hor, Nat.mod_eq_of_lt hsumLt]
    have hpow : 2^64 = 2^(Nat.size (high ||| otherHigh)) *
        2^(64 - Nat.size (high ||| otherHigh)) := by
      rw [← pow_add, hsplit]
    have hinner : (low + 2^64 * high) / 2^(Nat.size (high ||| otherHigh)) =
        high * 2^(64 - Nat.size (high ||| otherHigh)) +
          low / 2^(Nat.size (high ||| otherHigh)) := by
      rw [hpow]
      rw [show (2^(Nat.size (high ||| otherHigh)) *
          2^(64 - Nat.size (high ||| otherHigh))) * high =
          2^(Nat.size (high ||| otherHigh)) *
            (high * 2^(64 - Nat.size (high ||| otherHigh))) by ring]
      rw [Nat.add_mul_div_left _ _ (by positivity)]
      omega
    rw [hfinish, show 2^(Nat.size (high ||| otherHigh) + 31) =
      2^(Nat.size (high ||| otherHigh)) * 2^31 by rw [pow_add],
      ← Nat.div_div_eq_div_mul, hinner]

private theorem bfxil_prefix {window low : Nat} (hwindow : window < 2^64) :
    bfxil window low 0 31 = low % 2^31 + 2^31 * (window / 2^31) := by
  unfold bfxil ubfx lsr PastaAsm.word PastaAsm.regMod
  rw [Nat.div_one]
  have hlowPart : low % 2^31 < 2^31 := Nat.mod_lt _ (by positivity)
  rw [Nat.mod_eq_of_lt (hlowPart.trans (by norm_num : 2^31 < 2^64))]
  have hwindowDiv : window / 2^31 < 2^(64 - 31) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    simpa using hwindow
  have hsum : window / 2^31 * 2^31 + low % 2^31 < 2^64 := by
    calc
      window / 2^31 * 2^31 + low % 2^31 <
          2^(64 - 31) * 2^31 := by
        have hdivLe := Nat.le_sub_one_of_lt hwindowDiv
        calc
          window / 2^31 * 2^31 + low % 2^31 ≤
              (2^(64 - 31) - 1) * 2^31 + (2^31 - 1) :=
            Nat.add_le_add (Nat.mul_le_mul_right _ hdivLe)
              (Nat.le_sub_one_of_lt hlowPart)
          _ < 2^(64 - 31) * 2^31 := by
            have hp : 0 < 2^(64 - 31) := by positivity
            have hq : 0 < 2^31 := by positivity
            rw [pred_mul_add_pred hp hq]
            exact Nat.sub_lt (Nat.mul_pos hp hq) (by decide)
      _ = 2^64 := by rw [← pow_add]
  have hsumLiteral : window / 2^31 * 2^31 + low % 2^31 <
      18446744073709551616 := by simpa only [Nat.reducePow] using hsum
  rw [Nat.mod_eq_of_lt hsumLiteral]
  ring

/-- The pair assembled by the checked highest-limb selection, CLZ window, and low-bit splice. -/
def divsteps31Init (a b : Limbs) : Nat × Nat :=
  let z := (cmp (orr a.l3 b.l3) 0).z
  let a3 := cselNe z a.l3 a.l2
  let b3 := cselNe z b.l3 b.l2
  let a2 := cselNe z a.l2 a.l1
  let b2 := cselNe z b.l2 b.l1
  let z := (cmp (orr a3 b3) 0).z
  let a3 := cselNe z a3 a2
  let b3 := cselNe z b3 b2
  let a2 := cselNe z a2 a.l0
  let b2 := cselNe z b2 b.l0
  let aWindow := finishWindow a3 a2 a2 b3
  let bWindow := finishWindow b3 b2 b2 a3
  (bfxil aWindow a.l0 0 31, bfxil bWindow b.l0 0 31)

private theorem low_mod_add_pow_mul {low hi bits : Nat} (hbits : 31 ≤ bits) :
    (low + 2^bits * hi) % 2^31 = low % 2^31 := by
  have hdvd : 2^31 ∣ 2^bits * hi :=
    dvd_mul_of_dvd_left (pow_dvd_pow 2 hbits) hi
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvd, Nat.add_zero, Nat.mod_mod]

private theorem low_prefix_div {x low lowBits shift : Nat} (hlow : low < 2^lowBits) :
    (low + 2^lowBits * x) / 2^(lowBits + shift) = x / 2^shift := by
  rw [pow_add, ← Nat.div_div_eq_div_mul]
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlow, Nat.zero_add]

/-- The checked wrapper prelude computes the shared top-and-bottom approximation exactly. -/
theorem divsteps31Init_spec (a b : Limbs) (ha : a.Bounded) (hb : b.Bounded) :
    divsteps31Init a b = semolinaApprox a.toNat b.toNat := by
  rcases ha with ⟨ha0, ha1, ha2, ha3⟩
  rcases hb with ⟨hb0, hb1, hb2, hb3⟩
  unfold divsteps31Init
  simp only
  by_cases h3 : a.l3 = 0 ∧ b.l3 = 0
  · have hz3 : (cmp (orr a.l3 b.l3) 0).z = 1 := by
      apply (cmp_zero_z_eq_one_iff (orr_lt _ _)).2
      rw [orr_eq_or ha3 hb3, or_eq_zero_iff]
      exact h3
    simp only [hz3, cselNe, one_ne_zero, ↓reduceIte]
    by_cases h2 : a.l2 = 0 ∧ b.l2 = 0
    · have hz2 : (cmp (orr a.l2 b.l2) 0).z = 1 := by
        apply (cmp_zero_z_eq_one_iff (orr_lt _ _)).2
        rw [orr_eq_or ha2 hb2, or_eq_zero_iff]
        exact h2
      simp only [hz2, one_ne_zero, ↓reduceIte]
      by_cases h1 : a.l1 = 0 ∧ b.l1 = 0
      · rcases h3 with ⟨ha3z, hb3z⟩
        rcases h2 with ⟨ha2z, hb2z⟩
        rcases h1 with ⟨ha1z, hb1z⟩
        simp only [ha1z, hb1z]
        rw [finishWindow_zero ha0 rfl rfl, finishWindow_zero hb0 rfl rfl,
          bfxil_prefix ha0, bfxil_prefix hb0]
        simp only [Limbs.toNat, ha3z, hb3z, ha2z, hb2z, ha1z, hb1z,
          Nat.mul_zero, Nat.add_zero, semolinaApprox, approximate]
        rw [if_pos]
        · apply Prod.ext
          · simpa [Nat.mul_comm] using Nat.mod_add_div a.l0 (2^31)
          · simpa [Nat.mul_comm] using Nat.mod_add_div b.l0 (2^31)
        · exact max_le (Nat.size_le.mpr ha0) (Nat.size_le.mpr hb0)
      · have h1' : a.l1 ≠ 0 ∨ b.l1 ≠ 0 := not_and_or.mp h1
        have hz1 : (cmp (orr a.l1 b.l1) 0).z = 0 := by
          apply (cmp_zero_z_eq_zero_iff (orr_lt _ _)).2
          rw [orr_eq_or ha1 hb1]
          intro hzero
          rw [or_eq_zero_iff] at hzero
          exact h1'.elim (fun h => h hzero.1) (fun h => h hzero.2)
        rcases h3 with ⟨ha3z, hb3z⟩
        rcases h2 with ⟨ha2z, hb2z⟩
        have hnz : a.l1 ||| b.l1 ≠ 0 := by
          intro hzero
          rw [or_eq_zero_iff] at hzero
          exact h1'.elim (fun h => h hzero.1) (fun h => h hzero.2)
        have hsize : max (Nat.size (a.l0 + 2^64 * a.l1))
            (Nat.size (b.l0 + 2^64 * b.l1)) = 64 + Nat.size (a.l1 ||| b.l1) :=
          max_size_add_pow_mul ha0 hb0 hnz
        have hlarge : 64 < max (Nat.size (a.l0 + 2^64 * a.l1))
            (Nat.size (b.l0 + 2^64 * b.l1)) := by
          rw [hsize]
          exact Nat.lt_add_of_pos_right (Nat.size_pos.mpr (Nat.pos_of_ne_zero hnz))
        rw [bfxil_prefix (window := finishWindow a.l1 a.l0 a.l0 b.l1)
            (by unfold finishWindow; exact orr_lt _ _),
          bfxil_prefix (window := finishWindow b.l1 b.l0 b.l0 a.l1)
            (by unfold finishWindow; exact orr_lt _ _)]
        rw [finishWindow_div ha1 ha0 ha0 hb1 hnz]
        rw [finishWindow_div hb1 hb0 hb0 ha1 (by simpa [Nat.or_comm] using hnz)]
        simp only [Limbs.toNat, ha3z, hb3z, ha2z, hb2z, Nat.mul_zero,
          Nat.add_zero, semolinaApprox, approximate]
        rw [if_neg (Nat.not_le_of_gt hlarge)]
        rw [hsize]
        have hshift : 64 + Nat.size (a.l1 ||| b.l1) - 32 - 1 =
            Nat.size (a.l1 ||| b.l1) + 31 := by omega
        rw [hshift]
        apply Prod.ext
        · change a.l0 % 2^31 + 2^31 * _ =
            (a.l0 + 2^64 * a.l1) % 2^31 + 2^31 * _
          rw [low_mod_add_pow_mul (by omega)]
        · change b.l0 % 2^31 + 2^31 * _ =
            (b.l0 + 2^64 * b.l1) % 2^31 + 2^31 * _
          rw [low_mod_add_pow_mul (by omega)]
          simp [Nat.or_comm]
    · have h2' : a.l2 ≠ 0 ∨ b.l2 ≠ 0 := not_and_or.mp h2
      have hz2 : (cmp (orr a.l2 b.l2) 0).z = 0 := by
        apply (cmp_zero_z_eq_zero_iff (orr_lt _ _)).2
        rw [orr_eq_or ha2 hb2]
        intro hzero
        rw [or_eq_zero_iff] at hzero
        exact h2'.elim (fun h => h hzero.1) (fun h => h hzero.2)
      simp only [hz2, if_pos]
      rcases h3 with ⟨ha3z, hb3z⟩
      have hnz : a.l2 ||| b.l2 ≠ 0 := by
        intro hzero
        rw [or_eq_zero_iff] at hzero
        exact h2'.elim (fun h => h hzero.1) (fun h => h hzero.2)
      have haLow : a.l0 + 2^64 * a.l1 < 2^128 := by omega
      have hbLow : b.l0 + 2^64 * b.l1 < 2^128 := by omega
      have hsize : max (Nat.size (a.l0 + 2^64 * a.l1 + 2^128 * a.l2))
          (Nat.size (b.l0 + 2^64 * b.l1 + 2^128 * b.l2)) =
          128 + Nat.size (a.l2 ||| b.l2) :=
        max_size_add_pow_mul haLow hbLow hnz
      have hlarge : 64 < max (Nat.size (a.l0 + 2^64 * a.l1 + 2^128 * a.l2))
          (Nat.size (b.l0 + 2^64 * b.l1 + 2^128 * b.l2)) := by
        rw [hsize]
        omega
      rw [bfxil_prefix (window := finishWindow a.l2 a.l1 a.l1 b.l2)
          (by unfold finishWindow; exact orr_lt _ _),
        bfxil_prefix (window := finishWindow b.l2 b.l1 b.l1 a.l2)
          (by unfold finishWindow; exact orr_lt _ _)]
      rw [finishWindow_div ha2 ha1 ha1 hb2 hnz]
      rw [finishWindow_div hb2 hb1 hb1 ha2 (by simpa [Nat.or_comm] using hnz)]
      simp only [Limbs.toNat, ha3z, hb3z, Nat.mul_zero, Nat.add_zero,
        semolinaApprox, approximate]
      rw [if_neg (Nat.not_le_of_gt hlarge), hsize]
      have hshift : 128 + Nat.size (a.l2 ||| b.l2) - 32 - 1 =
          64 + (Nat.size (a.l2 ||| b.l2) + 31) := by omega
      rw [hshift]
      have haFull : a.l0 + 2^64 * a.l1 + 2^128 * a.l2 =
          a.l0 + 2^64 * (a.l1 + 2^64 * a.l2) := by ring
      have hbFull : b.l0 + 2^64 * b.l1 + 2^128 * b.l2 =
          b.l0 + 2^64 * (b.l1 + 2^64 * b.l2) := by ring
      rw [haFull, hbFull]
      rw [low_prefix_div ha0, low_prefix_div hb0]
      apply Prod.ext
      · change a.l0 % 2^31 + 2^31 * _ =
          (a.l0 + 2^64 * (a.l1 + 2^64 * a.l2)) % 2^31 + 2^31 * _
        rw [low_mod_add_pow_mul (by omega)]
      · change b.l0 % 2^31 + 2^31 * _ =
          (b.l0 + 2^64 * (b.l1 + 2^64 * b.l2)) % 2^31 + 2^31 * _
        rw [low_mod_add_pow_mul (by omega)]
        simp [Nat.or_comm]
  · have h3' : a.l3 ≠ 0 ∨ b.l3 ≠ 0 := not_and_or.mp h3
    have hz3 : (cmp (orr a.l3 b.l3) 0).z = 0 := by
      apply (cmp_zero_z_eq_zero_iff (orr_lt _ _)).2
      rw [orr_eq_or ha3 hb3]
      intro hzero
      rw [or_eq_zero_iff] at hzero
      exact h3'.elim (fun h => h hzero.1) (fun h => h hzero.2)
    simp only [hz3, cselNe, if_pos]
    have hnz : a.l3 ||| b.l3 ≠ 0 := by
      intro hzero
      rw [or_eq_zero_iff] at hzero
      exact h3'.elim (fun h => h hzero.1) (fun h => h hzero.2)
    have haPrefix : a.l0 + 2^64 * a.l1 < 2^128 := by omega
    have hbPrefix : b.l0 + 2^64 * b.l1 < 2^128 := by omega
    have haLow : a.l0 + 2^64 * a.l1 + 2^128 * a.l2 < 2^192 := by omega
    have hbLow : b.l0 + 2^64 * b.l1 + 2^128 * b.l2 < 2^192 := by omega
    have hsize : max (Nat.size a.toNat) (Nat.size b.toNat) =
        192 + Nat.size (a.l3 ||| b.l3) := by
      simp only [Limbs.toNat]
      exact max_size_add_pow_mul haLow hbLow hnz
    have hlarge : 64 < max (Nat.size a.toNat) (Nat.size b.toNat) := by
      rw [hsize]
      omega
    rw [bfxil_prefix (window := finishWindow a.l3 a.l2 a.l2 b.l3)
        (by unfold finishWindow; exact orr_lt _ _),
      bfxil_prefix (window := finishWindow b.l3 b.l2 b.l2 a.l3)
        (by unfold finishWindow; exact orr_lt _ _)]
    rw [finishWindow_div ha3 ha2 ha2 hb3 hnz]
    rw [finishWindow_div hb3 hb2 hb2 ha3 (by simpa [Nat.or_comm] using hnz)]
    simp only [semolinaApprox, approximate]
    rw [if_neg (Nat.not_le_of_gt hlarge), hsize]
    have hshift : 192 + Nat.size (a.l3 ||| b.l3) - 32 - 1 =
        128 + (Nat.size (a.l3 ||| b.l3) + 31) := by omega
    rw [hshift]
    have haFull : a.toNat =
        (a.l0 + 2^64 * a.l1) + 2^128 * (a.l2 + 2^64 * a.l3) := by
      simp only [Limbs.toNat]
      ring
    have hbFull : b.toNat =
        (b.l0 + 2^64 * b.l1) + 2^128 * (b.l2 + 2^64 * b.l3) := by
      simp only [Limbs.toNat]
      ring
    rw [haFull, hbFull]
    rw [low_prefix_div haPrefix, low_prefix_div hbPrefix]
    apply Prod.ext
    · change a.l0 % 2^31 + 2^31 * _ =
        (a.l0 + 2^64 * a.l1 + 2^128 * (a.l2 + 2^64 * a.l3)) % 2^31 + 2^31 * _
      have hmod : (a.l0 + 2^64 * a.l1 + 2^128 * (a.l2 + 2^64 * a.l3)) % 2^31 =
          a.l0 % 2^31 := by
        rw [low_mod_add_pow_mul (by omega), low_mod_add_pow_mul (by omega)]
      rw [hmod]
    · change b.l0 % 2^31 + 2^31 * _ =
        (b.l0 + 2^64 * b.l1 + 2^128 * (b.l2 + 2^64 * b.l3)) % 2^31 + 2^31 * _
      have hmod : (b.l0 + 2^64 * b.l1 + 2^128 * (b.l2 + 2^64 * b.l3)) % 2^31 =
          b.l0 % 2^31 := by
        rw [low_mod_add_pow_mul (by omega), low_mod_add_pow_mul (by omega)]
      rw [hmod]
      simp [Nat.or_comm]

end PastaAsm.AArch64
