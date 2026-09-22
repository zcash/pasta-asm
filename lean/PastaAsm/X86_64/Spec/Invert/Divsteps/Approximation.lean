/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.X86_64.Spec.Invert.Divsteps.Lemmas

/-!
# Approximation initialization for x86-64 inversion divsteps

Arithmetic and bit-mask lemmas connecting the checked wrapper prelude to `semolinaApprox`.
-/

namespace PastaAsm.X86_64
open InversionSpec InversionConvergence


theorem size_or (x y : Nat) :
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

theorem or_eq_zero_iff (x y : Nat) : x ||| y = 0 ↔ x = 0 ∧ y = 0 := by
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

theorem shld_aligned_div
    {hi otherHi lo : Nat} (hhi : hi < 2^64) (hother : otherHi < 2^64)
    (hlo : lo < 2^64) (hnz : hi ||| otherHi ≠ 0) :
    let r := Nat.size (hi ||| otherHi)
    shld hi lo (neg (lea ((bsr (bitOr hi otherHi)).getD 0) 1)).1 / 2^31 =
      (lo + 2^64 * hi) / 2^(r + 31) := by
  dsimp
  have horLt : hi ||| otherHi < 2^64 := Nat.bitwise_lt_two_pow hhi hother
  have hwordOr : bitOr hi otherHi = hi ||| otherHi := by
    simp only [bitOr, word, regMod, Nat.mod_eq_of_lt hhi, Nat.mod_eq_of_lt hother]
    rw [Nat.mod_eq_of_lt horLt]
  have hrpos : 0 < Nat.size (hi ||| otherHi) := Nat.size_pos.mpr (Nat.pos_of_ne_zero hnz)
  have hrle : Nat.size (hi ||| otherHi) ≤ 64 := Nat.size_le.mpr horLt
  have hlog : Nat.log2 (hi ||| otherHi) + 1 = Nat.size (hi ||| otherHi) :=
    (size_eq_log2_add_one hnz).symm
  rw [hwordOr]
  simp only [bsr, word, regMod, Nat.mod_eq_of_lt horLt, if_neg hnz, Option.getD_some]
  have hlea : lea (Nat.log2 (hi ||| otherHi)) 1 = Nat.size (hi ||| otherHi) := by
    simp only [lea, word, regMod]
    rw [Nat.mod_eq_of_lt]
    · exact hlog
    · omega
  rw [hlea]
  have hneg : (neg (Nat.size (hi ||| otherHi))).1 =
      2^64 - Nat.size (hi ||| otherHi) := by
    simp only [neg, sbb, regMod]
    rw [Nat.zero_add, Nat.sub_zero, Nat.mod_eq_of_lt]
    exact Nat.sub_lt (by positivity) hrpos
  rw [hneg]
  by_cases hr64 : Nat.size (hi ||| otherHi) = 64
  · rw [hr64]
    norm_num [shld, word, regMod]
    change (hi % 2^64) / 2^31 = (lo + 2^64 * hi) / 2^(64 + 31)
    rw [Nat.mod_eq_of_lt hhi]
    have hinner : (lo + 2^64 * hi) / 2^64 = hi := by
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlo, Nat.zero_add]
    rw [pow_add, ← Nat.div_div_eq_div_mul, hinner]
  · have hrlt : Nat.size (hi ||| otherHi) < 64 := by omega
    have hsub : 2^64 - Nat.size (hi ||| otherHi) =
        (2^64 - 64) + (64 - Nat.size (hi ||| otherHi)) := by omega
    have hsmall : 64 - Nat.size (hi ||| otherHi) < 64 := by omega
    have hcount : (2^64 - Nat.size (hi ||| otherHi)) % 64 =
        64 - Nat.size (hi ||| otherHi) := by
      calc
        (2^64 - Nat.size (hi ||| otherHi)) % 64 =
            ((2^64 - 64) + (64 - Nat.size (hi ||| otherHi))) % 64 := by rw [hsub]
        _ = (64 - Nat.size (hi ||| otherHi)) % 64 := by norm_num [Nat.add_mod]
        _ = 64 - Nat.size (hi ||| otherHi) := Nat.mod_eq_of_lt hsmall
    simp only [shld, hcount, if_neg (by omega : 64 - Nat.size (hi ||| otherHi) ≠ 0)]
    simp only [lsl, lsr, word, regMod, Nat.mod_eq_of_lt hhi, Nat.mod_eq_of_lt hlo]
    have hcancel : 64 - (64 - Nat.size (hi ||| otherHi)) = Nat.size (hi ||| otherHi) := by omega
    rw [hcancel]
    have hhiSize : Nat.size hi ≤ Nat.size (hi ||| otherHi) := by
      rw [size_or]
      exact Nat.le_max_left _ _
    have hhiPow : hi < 2^(Nat.size (hi ||| otherHi)) :=
      (Nat.lt_size_self hi).trans_le (Nat.pow_le_pow_right (by decide) hhiSize)
    have hloDivLt : lo / 2^(Nat.size (hi ||| otherHi)) <
        2^(64 - Nat.size (hi ||| otherHi)) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      rw [← pow_add]
      convert hlo using 2
      all_goals omega
    have hshiftPow : hi * 2^(64 - Nat.size (hi ||| otherHi)) < 2^64 := by
      calc
        hi * 2^(64 - Nat.size (hi ||| otherHi)) <
            2^(Nat.size (hi ||| otherHi)) * 2^(64 - Nat.size (hi ||| otherHi)) :=
          Nat.mul_lt_mul_of_pos_right hhiPow (by positivity)
        _ = 2^64 := by rw [← pow_add]; congr 1; omega
    rw [Nat.mod_eq_of_lt hshiftPow]
    have hsumLt : hi * 2^(64 - Nat.size (hi ||| otherHi)) +
        lo / 2^(Nat.size (hi ||| otherHi)) < 2^64 := by
      have hmulLe : hi * 2^(64 - Nat.size (hi ||| otherHi)) ≤
          (2^(Nat.size (hi ||| otherHi)) - 1) *
            2^(64 - Nat.size (hi ||| otherHi)) :=
        Nat.mul_le_mul_right _ (Nat.le_sub_one_of_lt hhiPow)
      have hdivLe : lo / 2^(Nat.size (hi ||| otherHi)) ≤
          2^(64 - Nat.size (hi ||| otherHi)) - 1 := Nat.le_sub_one_of_lt hloDivLt
      have hp : 2^(Nat.size (hi ||| otherHi)) *
          2^(64 - Nat.size (hi ||| otherHi)) = 2^64 := by
        rw [← pow_add]; congr 1; omega
      have hA : 1 ≤ 2^(Nat.size (hi ||| otherHi)) := Nat.one_le_two_pow
      calc
        hi * 2^(64 - Nat.size (hi ||| otherHi)) +
            lo / 2^(Nat.size (hi ||| otherHi)) ≤
            (2^(Nat.size (hi ||| otherHi)) - 1) *
              2^(64 - Nat.size (hi ||| otherHi)) +
              (2^(64 - Nat.size (hi ||| otherHi)) - 1) :=
          Nat.add_le_add hmulLe hdivLe
        _ = 2^64 - 1 := by
          rw [← hp]
          exact pred_mul_add_pred
            (a := 2^(Nat.size (hi ||| otherHi)))
            (b := 2^(64 - Nat.size (hi ||| otherHi)))
            (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
        _ < 2^64 := Nat.sub_lt (by positivity) (by decide)
    rw [Nat.mod_eq_of_lt hsumLt]
    rw [show 2^(Nat.size (hi ||| otherHi) + 31) =
      2^(Nat.size (hi ||| otherHi)) * 2^31 by rw [pow_add], ← Nat.div_div_eq_div_mul]
    have hpow : 2^64 = 2^(Nat.size (hi ||| otherHi)) *
        2^(64 - Nat.size (hi ||| otherHi)) := by
      rw [← pow_add]
      congr 1
      omega
    have hinner : (lo + 2^64 * hi) / 2^(Nat.size (hi ||| otherHi)) =
        hi * 2^(64 - Nat.size (hi ||| otherHi)) +
          lo / 2^(Nat.size (hi ||| otherHi)) := by
      rw [hpow]
      rw [show (2^(Nat.size (hi ||| otherHi)) *
          2^(64 - Nat.size (hi ||| otherHi))) * hi =
          2^(Nat.size (hi ||| otherHi)) *
            (hi * 2^(64 - Nat.size (hi ||| otherHi))) by ring]
      rw [Nat.add_mul_div_left _ _ (by positivity)]
      omega
    rw [← hinner]
    change (lo + 2^64 * hi) / 2^(Nat.size (hi ||| otherHi)) / 2^31 =
      (lo + 2^64 * hi) / 2^(Nat.size (hi ||| otherHi)) / 2^31
    rfl

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

theorem max_size_add_pow_mul {lowA lowB hiA hiB shift : Nat}
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

private theorem highMask_testBit (i : Nat) :
    (2^64 - 2^31).testBit i = decide (31 ≤ i ∧ i < 64) := by
  have hm := Nat.testBit_two_pow_sub_succ
    (n := 64) (x := 2^31 - 1) (by norm_num : 2^31 - 1 < 2^64) i
  have hm' : (2^64 - 2^31).testBit i =
      (decide (i < 64) && !(2^31 - 1).testBit i) := by
    convert hm using 1
  rw [hm', Nat.testBit_two_pow_sub_one]
  by_cases h31 : i < 31 <;> by_cases h64 : i < 64 <;> simp [h31, h64] ; omega

private theorem highMask (x : Nat) (hx : x < 2^64) :
    x &&& (2^64 - 2^31) = 2^31 * (x / 2^31) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.mul_comm (2^31), Nat.testBit_mul_two_pow]
  rw [highMask_testBit i]
  by_cases h31 : 31 ≤ i
  · rw [Nat.testBit_div_two_pow]
    by_cases h64 : i < 64
    · simp [h31, h64]
    · have hxi : x.testBit i = false := Nat.testBit_lt_two_pow
        (hx.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [h31, h64, hxi]
  · simp [h31]

theorem approximationMasks {low window : Nat} (hlow : low < 2^64)
    (hwindow : window < 2^64) :
    bitOr (bitAnd low (word32 (2^31 - 1)))
        (bitAnd window (bitNot (word32 (2^31 - 1)))) =
      low % 2^31 + 2^31 * (window / 2^31) := by
  have hmask : word32 (2^31 - 1) = 2^31 - 1 := by
    rw [word32, Nat.mod_eq_of_lt]
    norm_num
  have hnot : bitNot (word32 (2^31 - 1)) = 2^64 - 2^31 := by
    simp only [bitNot, hmask]
    rw [word_eq_of_lt (by norm_num : 2^31 - 1 < 2^64)]
    norm_num
  have hlowMask : bitAnd low (word32 (2^31 - 1)) = low % 2^31 := by
    simp only [bitAnd, hmask]
    rw [word_eq_of_lt hlow, word_eq_of_lt (by norm_num : 2^31 - 1 < 2^64)]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact word_eq_of_lt ((Nat.mod_lt _ (Nat.two_pow_pos 31)).trans (by norm_num))
  have hhighMask : bitAnd window (bitNot (word32 (2^31 - 1))) =
      2^31 * (window / 2^31) := by
    simp only [bitAnd, hnot]
    rw [word_eq_of_lt hwindow, word_eq_of_lt (by norm_num : 2^64 - 2^31 < 2^64)]
    rw [highMask window hwindow]
    rw [word_eq_of_lt]
    have hdiv : window / 2^31 < 2^(64 - 31) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
      simpa using hwindow
    calc
      2^31 * (window / 2^31) < 2^31 * 2^(64 - 31) :=
        Nat.mul_lt_mul_of_pos_left hdiv (by positivity)
      _ = 2^64 := by rw [← pow_add]
  rw [hlowMask, hhighMask]
  simp only [bitOr]
  have hlowOut : low % 2^31 < 2^64 :=
    (Nat.mod_lt _ (by positivity)).trans (by norm_num)
  have hdiv : window / 2^31 < 2^(64 - 31) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    simpa using hwindow
  have hhighOut : 2^31 * (window / 2^31) < 2^64 := by
    calc
      2^31 * (window / 2^31) < 2^31 * 2^(64 - 31) :=
        Nat.mul_lt_mul_of_pos_left hdiv (by positivity)
      _ = 2^64 := by rw [← pow_add]
  rw [word_eq_of_lt hlowOut, word_eq_of_lt hhighOut]
  have hor : 2^31 * (window / 2^31) + low % 2^31 =
      2^31 * (window / 2^31) ||| low % 2^31 :=
    Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (by positivity)) _
  have hor' : low % 2^31 ||| 2^31 * (window / 2^31) =
      low % 2^31 + 2^31 * (window / 2^31) := by
    simpa [Nat.add_comm, Nat.or_comm] using hor.symm
  rw [word_eq_of_lt]
  · exact hor'
  · exact Nat.bitwise_lt_two_pow hlowOut hhighOut


/-- The pair assembled by the checked highest-limb selection, shift, and mask prelude. -/
def divsteps31Init (a b : Limbs) : Nat × Nat :=
  let topOr := bitOr a.l3 b.l3
  let z3 := zeroFlag topOr
  let a3 := if z3 = 0 then a.l3 else a.l2
  let b3 := if z3 = 0 then b.l3 else b.l2
  let a2 := if z3 = 0 then a.l2 else a.l1
  let b2 := if z3 = 0 then b.l2 else b.l1
  let a1 := if z3 = 0 then a.l1 else a.l0
  let b1 := if z3 = 0 then b.l1 else b.l0
  let midOr := bitOr a3 b3
  let z2 := zeroFlag midOr
  let a3 := if z2 = 0 then a3 else a2
  let b3 := if z2 = 0 then b3 else b2
  let a2 := if z2 = 0 then a2 else a1
  let b2 := if z2 = 0 then b2 else b1
  let lowOr := bitOr a3 b3
  let z1 := zeroFlag lowOr
  let count := if z1 = 0 then lea ((bsr lowOr).getD 0) 1 else lowOr
  let a3 := if z1 = 0 then a3 else a.l0
  let b3 := if z1 = 0 then b3 else b.l0
  let shift := (neg count).1
  let aWindow := shld a3 a2 shift
  let bWindow := shld b3 b2 shift
  let mask := word32 (2^31 - 1)
  (bitOr (bitAnd a.l0 mask) (bitAnd aWindow (bitNot mask)),
   bitOr (bitAnd b.l0 mask) (bitAnd bWindow (bitNot mask)))

private theorem low_mod_add_pow_mul {low hi bits : Nat} (hbits : 31 ≤ bits) :
    (low + 2^bits * hi) % 2^31 = low % 2^31 := by
  have hdvd : 2^31 ∣ 2^bits * hi :=
    dvd_mul_of_dvd_left (pow_dvd_pow 2 hbits) hi
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvd, Nat.add_zero, Nat.mod_mod]

private theorem shld_aligned_div_right
    {hi otherHi lo : Nat} (hhi : hi < 2^64) (hother : otherHi < 2^64)
    (hlo : lo < 2^64) (hnz : otherHi ||| hi ≠ 0) :
    shld hi lo (neg (lea ((bsr (bitOr otherHi hi)).getD 0) 1)).1 / 2^31 =
      (lo + 2^64 * hi) / 2^(Nat.size (otherHi ||| hi) + 31) := by
  rw [show bitOr otherHi hi = bitOr hi otherHi by
    simp only [bitOr, Nat.or_comm]]
  rw [shld_aligned_div hhi hother hlo (by simpa [Nat.or_comm] using hnz)]
  simp [Nat.or_comm]

private theorem low_prefix_div {x low lowBits shift : Nat} (hlow : low < 2^lowBits) :
    (low + 2^lowBits * x) / 2^(lowBits + shift) = x / 2^shift := by
  rw [pow_add, ← Nat.div_div_eq_div_mul]
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlow, Nat.zero_add]

private theorem shld_aligned_div_with_low
    {hi otherHi lo low lowBits : Nat} (hhi : hi < 2^64) (hother : otherHi < 2^64)
    (hlo : lo < 2^64) (hnz : hi ||| otherHi ≠ 0) (hlow : low < 2^lowBits) :
    shld hi lo (neg (lea ((bsr (bitOr hi otherHi)).getD 0) 1)).1 / 2^31 =
      (low + 2^lowBits * (lo + 2^64 * hi)) /
        2^(lowBits + (Nat.size (hi ||| otherHi) + 31)) := by
  rw [shld_aligned_div hhi hother hlo hnz]
  exact (low_prefix_div hlow).symm

private theorem shld_aligned_div_right_with_low
    {hi otherHi lo low lowBits : Nat} (hhi : hi < 2^64) (hother : otherHi < 2^64)
    (hlo : lo < 2^64) (hnz : otherHi ||| hi ≠ 0) (hlow : low < 2^lowBits) :
    shld hi lo (neg (lea ((bsr (bitOr otherHi hi)).getD 0) 1)).1 / 2^31 =
      (low + 2^lowBits * (lo + 2^64 * hi)) /
        2^(lowBits + (Nat.size (otherHi ||| hi) + 31)) := by
  rw [shld_aligned_div_right hhi hother hlo hnz]
  exact (low_prefix_div hlow).symm

private theorem bitOr_eq_zero_iff_bounded {x y : Nat}
    (hx : x < 2^64) (hy : y < 2^64) : bitOr x y = 0 ↔ x = 0 ∧ y = 0 := by
  simp only [bitOr, word_eq_of_lt hx, word_eq_of_lt hy]
  have horLt : x ||| y < 2^64 := Nat.bitwise_lt_two_pow hx hy
  rw [word_eq_of_lt horLt]
  constructor
  · intro h
    have hs := size_or x y
    rw [h, Nat.size_zero] at hs
    exact ⟨Nat.size_eq_zero.mp (by omega), Nat.size_eq_zero.mp (by omega)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem zeroFlag_bitOr_eq_one_iff {x y : Nat}
    (hx : x < 2^64) (hy : y < 2^64) : zeroFlag (bitOr x y) = 1 ↔ x = 0 ∧ y = 0 := by
  rw [zeroFlag_eq_one_iff, word_eq_of_lt (bitOr_lt _ _), bitOr_eq_zero_iff_bounded hx hy]

private theorem zeroFlag_bitOr_eq_zero_iff {x y : Nat}
    (hx : x < 2^64) (hy : y < 2^64) : zeroFlag (bitOr x y) = 0 ↔ x ≠ 0 ∨ y ≠ 0 := by
  rw [zeroFlag_eq_zero_iff, word_eq_of_lt (bitOr_lt _ _)]
  exact (not_congr (bitOr_eq_zero_iff_bounded hx hy)).trans not_and_or

/-- The checked wrapper prelude computes the shared top-and-bottom approximation exactly. -/
theorem divsteps31Init_spec (a b : Limbs) (ha : a.Bounded) (hb : b.Bounded) :
    divsteps31Init a b = semolinaApprox a.toNat b.toNat := by
  rcases ha with ⟨ha0, ha1, ha2, ha3⟩
  rcases hb with ⟨hb0, hb1, hb2, hb3⟩
  unfold divsteps31Init
  simp only
  by_cases h3 : a.l3 = 0 ∧ b.l3 = 0
  · have hz3 : zeroFlag (bitOr a.l3 b.l3) = 1 :=
      (zeroFlag_bitOr_eq_one_iff ha3 hb3).2 h3
    simp only [hz3, one_ne_zero, ↓reduceIte]
    by_cases h2 : a.l2 = 0 ∧ b.l2 = 0
    · have hz2 : zeroFlag (bitOr a.l2 b.l2) = 1 :=
        (zeroFlag_bitOr_eq_one_iff ha2 hb2).2 h2
      simp only [hz2, one_ne_zero, ↓reduceIte]
      by_cases h1 : a.l1 = 0 ∧ b.l1 = 0
      · have hz1 : zeroFlag (bitOr a.l1 b.l1) = 1 :=
          (zeroFlag_bitOr_eq_one_iff ha1 hb1).2 h1
        rcases h3 with ⟨ha3z, hb3z⟩
        rcases h2 with ⟨ha2z, hb2z⟩
        rcases h1 with ⟨ha1z, hb1z⟩
        have hor0 : bitOr 0 0 = 0 := by decide
        have hz0 : zeroFlag (bitOr 0 0) = 1 := by decide
        simp only [Limbs.toNat, ha3z, hb3z, ha2z, hb2z, ha1z, hb1z, Nat.mul_zero,
          Nat.add_zero, hz0, one_ne_zero, ↓reduceIte]
        simp only [semolinaApprox, approximate]
        rw [if_pos]
        · rw [approximationMasks ha0 (shld_lt _ _ _),
            approximationMasks hb0 (shld_lt _ _ _)]
          rw [hor0]
          have hneg0 : (neg 0).1 = 0 := by decide
          simp only [hneg0, shld, Nat.zero_mod, word_eq_of_lt ha0, word_eq_of_lt hb0]
          apply Prod.ext
          · simpa [Nat.mul_comm] using Nat.mod_add_div a.l0 (2^31)
          · simpa [Nat.mul_comm] using Nat.mod_add_div b.l0 (2^31)
        · have hsizeA : Nat.size a.l0 ≤ 64 := Nat.size_le.mpr ha0
          have hsizeB : Nat.size b.l0 ≤ 64 := Nat.size_le.mpr hb0
          exact max_le hsizeA hsizeB
      · have hz1 : zeroFlag (bitOr a.l1 b.l1) = 0 :=
          (zeroFlag_bitOr_eq_zero_iff ha1 hb1).2 (not_and_or.mp h1)
        simp only [hz1, if_true]
        rcases h3 with ⟨ha3z, hb3z⟩
        rcases h2 with ⟨ha2z, hb2z⟩
        simp only [Limbs.toNat, ha3z, hb3z, ha2z, hb2z, Nat.mul_zero, Nat.add_zero]
        have hbitOrNe : bitOr a.l1 b.l1 ≠ 0 := by
          exact fun h => h1 ((bitOr_eq_zero_iff_bounded ha1 hb1).1 h)
        have horLt : a.l1 ||| b.l1 < 2^64 := Nat.bitwise_lt_two_pow ha1 hb1
        have hnz : a.l1 ||| b.l1 ≠ 0 := by
          simpa only [bitOr, word_eq_of_lt ha1, word_eq_of_lt hb1,
            word_eq_of_lt horLt] using hbitOrNe
        have hsize : max (Nat.size (a.l0 + 2^64 * a.l1))
            (Nat.size (b.l0 + 2^64 * b.l1)) = 64 + Nat.size (a.l1 ||| b.l1) :=
          max_size_add_pow_mul ha0 hb0 hnz
        have hlarge : 64 < max (Nat.size (a.l0 + 2^64 * a.l1))
            (Nat.size (b.l0 + 2^64 * b.l1)) := by
          rw [hsize]
          exact Nat.lt_add_of_pos_right (Nat.size_pos.mpr (Nat.pos_of_ne_zero hnz))
        simp only [semolinaApprox, approximate]
        rw [if_neg (Nat.not_le_of_gt hlarge)]
        have hshift : 64 + Nat.size (a.l1 ||| b.l1) - 32 - 1 =
            Nat.size (a.l1 ||| b.l1) + 31 := by omega
        rw [hsize, hshift]
        rw [approximationMasks ha0 (shld_lt _ _ _),
          approximationMasks hb0 (shld_lt _ _ _)]
        rw [shld_aligned_div ha1 hb1 ha0 hnz,
          shld_aligned_div_right hb1 ha1 hb0 hnz]
        apply Prod.ext
        · change a.l0 % 2^31 + 2^31 * _ =
            (a.l0 + 2^64 * a.l1) % 2^31 + 2^31 * _
          rw [low_mod_add_pow_mul (by omega)]
        · change b.l0 % 2^31 + 2^31 * _ =
            (b.l0 + 2^64 * b.l1) % 2^31 + 2^31 * _
          rw [low_mod_add_pow_mul (by omega)]
    · have hz2 : zeroFlag (bitOr a.l2 b.l2) = 0 :=
        (zeroFlag_bitOr_eq_zero_iff ha2 hb2).2 (not_and_or.mp h2)
      simp only [hz2, ↓reduceIte]
      rcases h3 with ⟨ha3z, hb3z⟩
      simp only [Limbs.toNat, ha3z, hb3z, Nat.mul_zero, Nat.add_zero]
      have hbitOrNe : bitOr a.l2 b.l2 ≠ 0 := by
        exact fun h => h2 ((bitOr_eq_zero_iff_bounded ha2 hb2).1 h)
      have horLt : a.l2 ||| b.l2 < 2^64 := Nat.bitwise_lt_two_pow ha2 hb2
      have hnz : a.l2 ||| b.l2 ≠ 0 := by
        simpa only [bitOr, word_eq_of_lt ha2, word_eq_of_lt hb2,
          word_eq_of_lt horLt] using hbitOrNe
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
      simp only [semolinaApprox, approximate]
      rw [if_neg (Nat.not_le_of_gt hlarge)]
      have hshift : 128 + Nat.size (a.l2 ||| b.l2) - 32 - 1 =
          64 + (Nat.size (a.l2 ||| b.l2) + 31) := by omega
      rw [hsize, hshift]
      rw [approximationMasks ha0 (shld_lt _ _ _),
        approximationMasks hb0 (shld_lt _ _ _)]
      have haFull : a.l0 + 2^64 * a.l1 + 2^128 * a.l2 =
          a.l0 + 2^64 * (a.l1 + 2^64 * a.l2) := by ring
      have hbFull : b.l0 + 2^64 * b.l1 + 2^128 * b.l2 =
          b.l0 + 2^64 * (b.l1 + 2^64 * b.l2) := by ring
      rw [haFull, hbFull]
      rw [shld_aligned_div_with_low ha2 hb2 ha1 hnz ha0,
        shld_aligned_div_right_with_low hb2 ha2 hb1 hnz hb0]
      apply Prod.ext
      · change a.l0 % 2^31 + 2^31 * _ =
          (a.l0 + 2^64 * (a.l1 + 2^64 * a.l2)) % 2^31 + 2^31 * _
        rw [low_mod_add_pow_mul (by omega)]
      · change b.l0 % 2^31 + 2^31 * _ =
          (b.l0 + 2^64 * (b.l1 + 2^64 * b.l2)) % 2^31 + 2^31 * _
        rw [low_mod_add_pow_mul (by omega)]
  · have hz3 : zeroFlag (bitOr a.l3 b.l3) = 0 :=
      (zeroFlag_bitOr_eq_zero_iff ha3 hb3).2 (not_and_or.mp h3)
    simp only [hz3, ↓reduceIte]
    have hbitOrNe : bitOr a.l3 b.l3 ≠ 0 := by
      exact fun h => h3 ((bitOr_eq_zero_iff_bounded ha3 hb3).1 h)
    have horLt : a.l3 ||| b.l3 < 2^64 := Nat.bitwise_lt_two_pow ha3 hb3
    have hnz : a.l3 ||| b.l3 ≠ 0 := by
      simpa only [bitOr, word_eq_of_lt ha3, word_eq_of_lt hb3,
        word_eq_of_lt horLt] using hbitOrNe
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
    simp only [semolinaApprox, approximate]
    rw [if_neg (Nat.not_le_of_gt hlarge)]
    have hshift : 192 + Nat.size (a.l3 ||| b.l3) - 32 - 1 =
        128 + (Nat.size (a.l3 ||| b.l3) + 31) := by omega
    rw [hsize, hshift]
    rw [approximationMasks ha0 (shld_lt _ _ _),
      approximationMasks hb0 (shld_lt _ _ _)]
    have haFull : a.toNat =
        (a.l0 + 2^64 * a.l1) + 2^128 * (a.l2 + 2^64 * a.l3) := by
      simp only [Limbs.toNat]
      ring
    have hbFull : b.toNat =
        (b.l0 + 2^64 * b.l1) + 2^128 * (b.l2 + 2^64 * b.l3) := by
      simp only [Limbs.toNat]
      ring
    rw [haFull, hbFull]
    rw [shld_aligned_div_with_low ha3 hb3 ha2 hnz haPrefix,
      shld_aligned_div_right_with_low hb3 ha3 hb2 hnz hbPrefix]
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


end PastaAsm.X86_64
