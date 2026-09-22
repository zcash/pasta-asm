/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.AArch64.Transcription
import PastaAsm.Spec.Invert.Arithmetic
import PastaAsm.Spec
import Mathlib.Tactic

namespace PastaAsm.AArch64

open Spec.Invert

/-- An integer represented by a 64-bit register bitpattern. -/
def WordRep (w : Nat) (z : Int) : Prop := (w : Int) ≡ z [ZMOD (2^64 : Nat)]

lemma sbfx_bit (a : Nat) :
    sbfx a 0 1 = if Even a then 0 else 2^64 - 1 := by
  unfold sbfx ubfx lsr word regMod
  norm_num
  have hcases : a % 2 = 0 ∨ a % 2 = 1 := Nat.mod_two_eq_zero_or_one a
  rcases hcases with h | h <;> rw [h] <;> norm_num
  · exact Nat.even_iff.mpr h
  · exact Nat.odd_iff.mpr h

lemma and_allOnes (a : Nat) (ha : a < 2^64) : bitAnd a (2^64 - 1) = a := by
  unfold bitAnd word regMod
  rw [Nat.and_two_pow_sub_one_eq_mod]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha]

@[simp] lemma and_zero (a : Nat) : bitAnd a 0 = 0 := by simp [bitAnd, word]

lemma wordRep_word (n : Nat) : WordRep (word n) n := by
  rw [WordRep, Int.natCast_modEq_iff]
  exact Nat.mod_modEq _ _

lemma wordRep_add {wa wb : Nat} {a b : Int}
    (ha : WordRep wa a) (hb : WordRep wb b) : WordRep (add wa wb) (a + b) := by
  rw [WordRep] at ha hb ⊢
  have hw : WordRep (word (wa + wb)) ((wa : Int) + (wb : Int)) := by
    simpa [WordRep] using wordRep_word (wa + wb)
  exact hw.trans (ha.add hb)

lemma wordRep_double {w : Nat} {a : Int} (ha : WordRep w a) : WordRep (add w w) (2 * a) := by
  convert wordRep_add ha ha using 1
  ring

lemma wordRep_sub {wa wb : Nat} {a b : Int} (hwa : wa < 2^64) (hwb : wb < 2^64)
    (ha : WordRep wa a) (hb : WordRep wb b) : WordRep (sub wa wb) (a - b) := by
  rw [WordRep] at ha hb ⊢
  have hnat : (sub wa wb : Int) ≡ (wa : Int) - (wb : Int) [ZMOD (2^64 : Nat)] := by
    rw [Int.modEq_iff_dvd]
    simp only [sub, subc, regMod]
    have harg : wa + 2^64 - wb - (1 - 1) = wa + 2^64 - wb := by omega
    rw [harg]
    by_cases hle : wb ≤ wa
    · refine ⟨0, ?_⟩
      have hlt : wa + 2^64 - wb < 2^64 + 2^64 := by omega
      have hge : 2^64 ≤ wa + 2^64 - wb := by omega
      rw [Nat.mod_eq_sub_mod hge]
      have hdiff : wa + 2^64 - wb - 2^64 = wa - wb := by omega
      rw [hdiff, Nat.mod_eq_of_lt (by omega : wa - wb < 2^64)]
      push_cast
      omega
    · refine ⟨-1, ?_⟩
      have hlt : wa + 2^64 - wb < 2^64 := by omega
      rw [Nat.mod_eq_of_lt hlt]
      push_cast
      omega
  exact hnat.trans (ha.sub hb)

lemma wordRep_zero : WordRep 0 0 := Int.ModEq.rfl
lemma wordRep_one : WordRep 1 1 := Int.ModEq.rfl

namespace Divsteps47State

def Bounded (s : Divsteps47State) : Prop :=
  s.a < 2^64 ∧ s.cnt < 2^64 ∧ s.b < 2^64 ∧ s.f0 < 2^64 ∧ s.g0 < 2^64 ∧
    s.f1 < 2^64 ∧ s.g1 < 2^64

def Represents (s : Divsteps47State) (m : SignedMatrix) : Prop :=
  WordRep s.f0 m.row0.left ∧ WordRep s.g0 m.row0.right ∧
    WordRep s.f1 m.row1.left ∧ WordRep s.g1 m.row1.right

def Corresponds (s : Divsteps47State) (m : SignedMatrix) : Prop :=
  s.Bounded ∧ s.Represents m

end Divsteps47State

end PastaAsm.AArch64
