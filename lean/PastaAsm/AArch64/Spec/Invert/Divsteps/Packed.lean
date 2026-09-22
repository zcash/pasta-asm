/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.AArch64.Spec.Invert.Divsteps.Round31

/-!
# Supporting lemmas for the AArch64 31-step inversion wrapper

Bounds for the biased packed coefficient lanes and their final decoding into
signed 64-bit coefficient words.
-/

namespace PastaAsm.AArch64

open PastaAsm.InversionSpec PastaAsm.InversionConvergence

/-- The asymmetric interval exactly supported by the biased 32-bit lane encoding. -/
def BiasBoundedRow (n : Nat) (row : SignedRow) : Prop :=
  -((2^n - 1 : Nat) : Int) ≤ row.left ∧ row.left ≤ (2^n : Nat) ∧
  -((2^n - 1 : Nat) : Int) ≤ row.right ∧ row.right ≤ (2^n : Nat)

/-- Both rows lie in the asymmetric interval supported by the packed encoding. -/
def BiasBoundedMatrix (n : Nat) (matrix : SignedMatrix) : Prop :=
  BiasBoundedRow n matrix.row0 ∧ BiasBoundedRow n matrix.row1

private theorem biasBounded_succ {n : Nat} {row : SignedRow} (h : BiasBoundedRow n row) :
    BiasBoundedRow (n + 1) row := by
  rcases h with ⟨hl0, hu0, hl1, hu1⟩
  simp only [BiasBoundedRow] at *
  have hp : 1 ≤ (2^n : Nat) := Nat.one_le_two_pow
  have hp' : 1 ≤ (2^(n + 1) : Nat) := Nat.one_le_two_pow
  rw [Int.ofNat_sub hp] at hl0 hl1
  rw [Int.ofNat_sub hp']
  norm_num [pow_succ] at *
  constructor <;> omega

private theorem biasBounded_double {n : Nat} {row : SignedRow} (h : BiasBoundedRow n row) :
    BiasBoundedRow (n + 1) row.double := by
  rcases h with ⟨hl0, hu0, hl1, hu1⟩
  simp only [BiasBoundedRow, SignedRow.double] at *
  have hp : 1 ≤ (2^n : Nat) := Nat.one_le_two_pow
  have hp' : 1 ≤ (2^(n + 1) : Nat) := Nat.one_le_two_pow
  rw [Int.ofNat_sub hp] at hl0 hl1
  rw [Int.ofNat_sub hp']
  norm_num [pow_succ] at *
  constructor <;> omega

private theorem biasBounded_sub {n : Nat} {row other : SignedRow}
    (hrow : BiasBoundedRow n row) (hother : BiasBoundedRow n other) :
    BiasBoundedRow (n + 1) (row.sub other) := by
  rcases hrow with ⟨hl0, hu0, hl1, hu1⟩
  rcases hother with ⟨hl0', hu0', hl1', hu1'⟩
  simp only [BiasBoundedRow, SignedRow.sub] at *
  have hp : 1 ≤ (2^n : Nat) := Nat.one_le_two_pow
  have hp' : 1 ≤ (2^(n + 1) : Nat) := Nat.one_le_two_pow
  rw [Int.ofNat_sub hp] at hl0 hl1 hl0' hl1'
  rw [Int.ofNat_sub hp']
  norm_num [pow_succ] at *
  constructor <;> omega

/-- One shared approximation operation advances the packed-coefficient interval. -/
theorem approxStep_biasBounded {n : Nat} {state : ApproxState}
    (h : BiasBoundedMatrix n state.matrix) :
    BiasBoundedMatrix (n + 1) (approxStep state).matrix := by
  rcases h with ⟨h0, h1⟩
  unfold approxStep BiasBoundedMatrix
  split_ifs
  · exact ⟨biasBounded_succ h0, biasBounded_double h1⟩
  · exact ⟨biasBounded_sub h0 h1, biasBounded_double h1⟩
  · exact ⟨biasBounded_sub h1 h0, biasBounded_double h0⟩

/-- Iteration advances the packed-coefficient interval once per operation. -/
theorem approxSteps_biasBounded {n : Nat} (steps : Nat) {state : ApproxState}
    (h : BiasBoundedMatrix n state.matrix) :
    BiasBoundedMatrix (n + steps) (approxSteps steps state).matrix := by
  induction steps generalizing n state with
  | zero => simpa [approxSteps] using h
  | succ steps ih =>
      rw [approxSteps]
      have hstep := approxStep_biasBounded h
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (state := approxStep state) hstep

/-- Identity rows start inside the zero-operation packed interval. -/
theorem identityMatrix_biasBounded : BiasBoundedMatrix 0 identityMatrix := by
  norm_num [BiasBoundedMatrix, BiasBoundedRow, identityMatrix]

/-- The matrix of the concrete short loop fits exactly in the two biased lanes. -/
theorem semolinaShort_biasBounded (a b : Nat) :
    BiasBoundedMatrix 31 (semolinaShort a b).matrix := by
  unfold semolinaShort
  simpa using approxSteps_biasBounded 31
    (state := ApproxState.initial (semolinaApprox a b).1 (semolinaApprox a b).2)
    (n := 0) (by
      simpa [ApproxState.initial] using identityMatrix_biasBounded)

/-- Decode a packed row whose coefficients fit the exact biased-lane interval. -/
theorem packedRowRep_decode {word : Nat} {row : SignedRow}
    (hrow : PackedRowRep word row) (hbound : BiasBoundedRow 31 row)
    (hword : word < 2^64) :
    WordRep (sub (ubfx word 0 32) packedLaneBias) row.left ∧
      WordRep (sub (ubfx word 32 32) packedLaneBias) row.right := by
  rw [PackedRowRep, WordRep, Int.modEq_iff_dvd] at hrow
  rcases hrow with ⟨k, hk⟩
  rcases hbound with ⟨hlower, hupper, hrlower, hrupper⟩
  have hbias : (packedRowBias : Int) = packedLaneBias + (2^32 : Int) * packedLaneBias := by
    rfl
  have hleftNonneg : 0 ≤ (packedLaneBias : Int) + row.left := by
    norm_num [packedLaneBias] at hlower ⊢
    omega
  have hleftLt : (packedLaneBias : Int) + row.left < 2^32 := by
    norm_num [packedLaneBias] at hupper ⊢
    omega
  have hrightNonneg : 0 ≤ (packedLaneBias : Int) + row.right := by
    norm_num [packedLaneBias] at hrlower ⊢
    omega
  have hrightLt : (packedLaneBias : Int) + row.right < 2^32 := by
    norm_num [packedLaneBias] at hrupper ⊢
    omega
  let leftNat := ((packedLaneBias : Int) + row.left).toNat
  let rightNat := ((packedLaneBias : Int) + row.right).toNat
  have hleftCast : (leftNat : Int) = (packedLaneBias : Int) + row.left :=
    Int.toNat_of_nonneg hleftNonneg
  have hrightCast : (rightNat : Int) = (packedLaneBias : Int) + row.right :=
    Int.toNat_of_nonneg hrightNonneg
  have hleftNatLt : leftNat < 2^32 := by
    change ((packedLaneBias : Int) + row.left).toNat < 2^32
    exact (Int.toNat_lt hleftNonneg).2 hleftLt
  have hrightNatLt : rightNat < 2^32 := by
    change ((packedLaneBias : Int) + row.right).toNat < 2^32
    exact (Int.toNat_lt hrightNonneg).2 hrightLt
  have hpackedCast : ((leftNat + 2^32 * rightNat : Nat) : Int) = packedRowValue row := by
    simp only [packedRowValue]
    push_cast
    rw [hleftCast, hrightCast, hbias]
    ring
  have hpackedLt : leftNat + 2^32 * rightNat < 2^64 := by omega
  have hwordEq : word = leftNat + 2^32 * rightNat := by
    have hk' : ((leftNat + 2^32 * rightNat : Nat) : Int) - (word : Int) =
        (2^64 : Int) * k := by
      rw [hpackedCast]
      simpa [mul_comm] using hk
    have hkzero : k = 0 := by
      have hwordNonneg : (0 : Int) ≤ word := by positivity
      have hwordLt' : (word : Int) < 2^64 := by exact_mod_cast hword
      have hpackedNonneg : (0 : Int) ≤ leftNat + 2^32 * rightNat := by positivity
      have hpackedLt' : (leftNat + 2^32 * rightNat : Int) < 2^64 := by
        exact_mod_cast hpackedLt
      omega
    have hwordInt : (word : Int) = (leftNat + 2^32 * rightNat : Nat) := by
      rw [hkzero, mul_zero] at hk'
      omega
    exact_mod_cast hwordInt
  have hleftNatLt64 : leftNat < 2^64 := hleftNatLt.trans (by norm_num)
  have hrightNatLt64 : rightNat < 2^64 := hrightNatLt.trans (by norm_num)
  have hlowEq : ubfx word 0 32 = leftNat := by
    rw [hwordEq]
    unfold ubfx lsr PastaAsm.word
    rw [Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hleftNatLt,
      Nat.mod_eq_of_lt hleftNatLt64]
  have hhighEq : ubfx word 32 32 = rightNat := by
    rw [hwordEq]
    unfold ubfx lsr PastaAsm.word
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hleftNatLt,
      Nat.zero_add, Nat.mod_eq_of_lt hrightNatLt, Nat.mod_eq_of_lt hrightNatLt64]
  have hlowRep : WordRep (ubfx word 0 32) ((packedLaneBias : Int) + row.left) := by
    rw [hlowEq, WordRep, hleftCast]
  have hhighRep : WordRep (ubfx word 32 32) ((packedLaneBias : Int) + row.right) := by
    rw [hhighEq, WordRep, hrightCast]
  have hbiasRep : WordRep packedLaneBias packedLaneBias := Int.ModEq.rfl
  constructor
  · have h := wordRep_sub (ubfx_lt word 0 32) (by decide : packedLaneBias < 2^64)
      hlowRep hbiasRep
    convert h using 1
    ring
  · have h := wordRep_sub (ubfx_lt word 32 32) (by decide : packedLaneBias < 2^64)
      hhighRep hbiasRep
    convert h using 1
    ring

end PastaAsm.AArch64
