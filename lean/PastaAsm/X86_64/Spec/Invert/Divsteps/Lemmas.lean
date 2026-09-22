/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.Spec.Invert.Convergence
import PastaAsm.X86_64.Transcription
import PastaAsm.X86_64.Spec.Arithmetic
import Mathlib.Tactic.NormNum

/-!
# Fixed-width lemmas for the x86-64 inversion divsteps

The generated x86-64 models expose signed coefficients as natural-number register
bitpatterns. This file supplies the representation-independent bridge used by the
checked instruction traces in `Invert/Divsteps.lean`.
-/

namespace PastaAsm.X86_64

open Spec.Invert Spec.Invert.Convergence

/-- A register word represents an integer modulo the 64-bit two's-complement modulus. -/
def SignedWordRep (word : Nat) (value : Int) : Prop :=
  word < 2^64 ∧ (2^64 : Int) ∣ (word : Int) - value

/-- The four returned words represent the rows of an integer transition matrix. -/
def InvertMatrixRep (words : InvertMatrix) (matrix : SignedMatrix) : Prop :=
  SignedWordRep words.f0 matrix.row0.left ∧
  SignedWordRep words.g0 matrix.row0.right ∧
  SignedWordRep words.f1 matrix.row1.left ∧
  SignedWordRep words.g1 matrix.row1.right

/-- Every live register in a final-tail round state is a 64-bit word. -/
def Divsteps47State.Bounded (s : Divsteps47State) : Prop :=
  s.a < 2^64 ∧ s.b < 2^64 ∧ s.f0 < 2^64 ∧ s.g0 < 2^64 ∧
  s.f1 < 2^64 ∧ s.g1 < 2^64 ∧ s.t0 < 2^64 ∧ s.t1 < 2^64 ∧ s.t2 < 2^64

/-- Every live register in an approximation round state is a 64-bit word. -/
def Divsteps31State.Bounded (s : Divsteps31State) : Prop :=
  s.a0 < 2^64 ∧ s.a1 < 2^64 ∧ s.a2 < 2^64 ∧ s.a3 < 2^64 ∧
  s.b0 < 2^64 ∧ s.b1 < 2^64 ∧ s.b2 < 2^64 ∧ s.b3 < 2^64 ∧ s.t < 2^64

@[simp] theorem signedWordRep_zero : SignedWordRep 0 0 := by
  constructor
  · decide
  · simp

@[simp] theorem signedWordRep_one : SignedWordRep 1 1 := by
  constructor
  · decide
  · simp

/-- A wrapped addition equation preserves the represented integer sum. -/
theorem signedWordRep_add {out xWord yWord carry : Nat} {x y : Int}
    (hout : out < 2^64) (hlin : out + 2^64 * carry = xWord + yWord)
    (hx : SignedWordRep xWord x) (hy : SignedWordRep yWord y) :
    SignedWordRep out (x + y) := by
  rcases hx.2 with ⟨kx, hkx⟩
  rcases hy.2 with ⟨ky, hky⟩
  refine ⟨hout, ⟨kx + ky - carry, ?_⟩⟩
  have hlin' : (out : Int) + 2^64 * carry = xWord + yWord := by
    exact_mod_cast hlin
  norm_num at hkx hky ⊢
  omega

/-- A wrapped doubling equation preserves twice the represented integer. -/
theorem signedWordRep_double {out xWord carry : Nat} {x : Int}
    (hout : out < 2^64) (hlin : out + 2^64 * carry = xWord + xWord)
    (hx : SignedWordRep xWord x) : SignedWordRep out (2 * x) := by
  have h := signedWordRep_add hout hlin hx hx
  simpa [two_mul] using h

/-- A wrapped subtraction equation preserves the represented integer difference. -/
theorem signedWordRep_sub {out xWord yWord borrow : Nat} {x y : Int}
    (hout : out < 2^64) (hlin : out + yWord = xWord + 2^64 * borrow)
    (hx : SignedWordRep xWord x) (hy : SignedWordRep yWord y) :
    SignedWordRep out (x - y) := by
  rcases hx.2 with ⟨kx, hkx⟩
  rcases hy.2 with ⟨ky, hky⟩
  refine ⟨hout, ⟨kx - ky + borrow, ?_⟩⟩
  have hlin' : (out : Int) + yWord = xWord + 2^64 * borrow := by
    exact_mod_cast hlin
  norm_num at hkx hky ⊢
  omega

/-- A final-tail round's abstract recurrence from its branch selectors and arithmetic equations.

This isolates the three-case reasoning from the generated instruction trace. -/
theorem divsteps47_round_conclusion
    (abstract : ApproxState)
    (a b : Nat)
    (a' b' f0' g0' f1' g1' : Nat)
    (ha : a = abstract.a) (hb : b = abstract.b)
    (hea : Even a →
      a' = a / 2 ∧ b' = b ∧
      SignedWordRep f0' abstract.matrix.row0.left ∧
      SignedWordRep g0' abstract.matrix.row0.right ∧
      SignedWordRep f1' (2 * abstract.matrix.row1.left) ∧
      SignedWordRep g1' (2 * abstract.matrix.row1.right))
    (hsub : ¬ Even a → b ≤ a →
      a' = (a - b) / 2 ∧ b' = b ∧
      SignedWordRep f0' (abstract.matrix.row0.left - abstract.matrix.row1.left) ∧
      SignedWordRep g0' (abstract.matrix.row0.right - abstract.matrix.row1.right) ∧
      SignedWordRep f1' (2 * abstract.matrix.row1.left) ∧
      SignedWordRep g1' (2 * abstract.matrix.row1.right))
    (hswap : ¬ Even a → a < b →
      a' = (b - a) / 2 ∧ b' = a ∧
      SignedWordRep f0' (abstract.matrix.row1.left - abstract.matrix.row0.left) ∧
      SignedWordRep g0' (abstract.matrix.row1.right - abstract.matrix.row0.right) ∧
      SignedWordRep f1' (2 * abstract.matrix.row0.left) ∧
      SignedWordRep g1' (2 * abstract.matrix.row0.right)) :
    a' = (approxStep abstract).a ∧ b' = (approxStep abstract).b ∧
      InvertMatrixRep ⟨f0', g0', f1', g1'⟩ (approxStep abstract).matrix := by
  unfold approxStep
  split_ifs with he hle
  · have he' : Even a := by rwa [ha]
    rcases hea he' with ⟨haa, hbb, hf0, hg0, hf1, hg1⟩
    refine ⟨?_, ?_, hf0, hg0, ?_, ?_⟩
    · simpa [ha] using haa
    · simpa [hb] using hbb
    · simpa [SignedRow.double] using hf1
    · simpa [SignedRow.double] using hg1
  · have hne : ¬ Even a := by rwa [ha]
    have hle' : b ≤ a := by simpa [ha, hb] using hle
    rcases hsub hne hle' with ⟨haa, hbb, hf0, hg0, hf1, hg1⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [ha, hb] using haa
    · simpa [hb] using hbb
    · simpa [SignedRow.sub] using hf0
    · simpa [SignedRow.sub] using hg0
    · simpa [SignedRow.double] using hf1
    · simpa [SignedRow.double] using hg1
  · have hne : ¬ Even a := by rwa [ha]
    have hlt' : a < b := by simpa [ha, hb] using Nat.lt_of_not_ge hle
    rcases hswap hne hlt' with ⟨haa, hbb, hf0, hg0, hf1, hg1⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [ha, hb] using haa
    · simpa [ha] using hbb
    · simpa [SignedRow.sub] using hf0
    · simpa [SignedRow.sub] using hg0
    · simpa [SignedRow.double] using hf1
    · simpa [SignedRow.double] using hg1

/-- Iterating the concrete final-round helper follows the shared approximation recurrence while
preserving register bounds and the signed coefficient bitpattern representation. -/
theorem divsteps47_iterate_spec (n : Nat) (s : Divsteps47State) (abstract : ApproxState)
    (hs : s.Bounded) (hstate : s.a = abstract.a ∧ s.b = abstract.b)
    (hmatrix : InvertMatrixRep ⟨s.f0, s.g0, s.f1, s.g1⟩ abstract.matrix)
    (hround : ∀ (s : Divsteps47State) (abstract : ApproxState),
      s.Bounded → s.a = abstract.a ∧ s.b = abstract.b →
      InvertMatrixRep ⟨s.f0, s.g0, s.f1, s.g1⟩ abstract.matrix →
      let s' := divsteps47Round s
      s'.Bounded ∧ s'.a = (approxStep abstract).a ∧ s'.b = (approxStep abstract).b ∧
        InvertMatrixRep ⟨s'.f0, s'.g0, s'.f1, s'.g1⟩ (approxStep abstract).matrix) :
    let s' := iterate divsteps47Round n s
    let abstract' := approxSteps n abstract
    s'.Bounded ∧ s'.a = abstract'.a ∧ s'.b = abstract'.b ∧
      InvertMatrixRep ⟨s'.f0, s'.g0, s'.f1, s'.g1⟩ abstract'.matrix := by
  induction n generalizing s abstract with
  | zero => exact ⟨hs, hstate.1, hstate.2, hmatrix⟩
  | succ n ih =>
      rw [iterate, approxSteps]
      rcases hround s abstract hs hstate hmatrix with ⟨hs', ha', hb', hm'⟩
      exact ih (divsteps47Round s) (approxStep abstract) hs' ⟨ha', hb'⟩ hm'

/-- For a bounded natural, testing the low bit with `and 1` computes its remainder modulo two. -/
theorem bitAnd_one {x : Nat} (hx : x < 2^64) : bitAnd x 1 = x % 2 := by
  have hmod : x % 2 < regMod := (Nat.mod_lt x (by decide)).trans (by decide)
  unfold bitAnd
  rw [word_eq_of_lt hx, word_eq_of_lt (by decide : 1 < regMod)]
  rw [Nat.and_comm, Nat.one_and_eq_mod_two, word_eq_of_lt hmod]

/-- The generated zero flag following `test x, 1` detects evenness. -/
theorem zeroFlag_bitAnd_one_eq_one_iff {x : Nat} (hx : x < 2^64) :
    zeroFlag (bitAnd x 1) = 1 ↔ Even x := by
  have hmod : x % 2 < 2^64 := (Nat.mod_lt x (by decide)).trans (by decide)
  rw [zeroFlag_eq_one_iff, bitAnd_one hx, word_eq_of_lt hmod]
  constructor
  · intro hzero
    exact even_iff_two_dvd.mpr (Nat.dvd_iff_mod_eq_zero.mpr hzero)
  · intro heven
    exact Nat.dvd_iff_mod_eq_zero.mp (even_iff_two_dvd.mp heven)

/-- The complementary generated branch condition detects oddness. -/
theorem zeroFlag_bitAnd_one_eq_zero_iff {x : Nat} (hx : x < 2^64) :
    zeroFlag (bitAnd x 1) = 0 ↔ ¬ Even x := by
  have hmod : x % 2 < 2^64 := (Nat.mod_lt x (by decide)).trans (by decide)
  rw [zeroFlag_eq_zero_iff, bitAnd_one hx, word_eq_of_lt hmod]
  constructor
  · intro hne heven
    exact hne (Nat.dvd_iff_mod_eq_zero.mp (even_iff_two_dvd.mp heven))
  · intro hne hzero
    exact hne (even_iff_two_dvd.mpr (Nat.dvd_iff_mod_eq_zero.mpr hzero))

/-- Finish a final-tail trace from the compact equations that remain after dead SSA facts are
cleared from the generated proof. Keeping the branch reasoning here prevents automation from
copying the complete instruction context into every branch. -/
theorem divsteps47_trace_conclusion
    (abstract : ApproxState)
    {a b a1 a2 a3 b1 t0 t01 t11 cf2 cf3 zf1 zf4 : Nat}
    {f0 g0 f1 g1 f01 g01 f11 g11 t04 t14 f02 g02 f12 g12 : Nat}
    {cf7 cf8 cf9 cf10 : Nat}
    (ha : a = abstract.a) (hb : b = abstract.b)
    (hf0 : SignedWordRep f0 abstract.matrix.row0.left)
    (hg0 : SignedWordRep g0 abstract.matrix.row0.right)
    (hf1 : SignedWordRep f1 abstract.matrix.row1.left)
    (hg1 : SignedWordRep g1 abstract.matrix.row1.right)
    (ht0 : t0 = 0) (ba : a < 2^64)
    (hzf1 : zf1 = zeroFlag (bitAnd a 1))
    (hzf4 : zf4 = zeroFlag (bitAnd a 1))
    (et01 : t01 = if zf1 = 0 then b else t0)
    (la1 : a1 + t01 + 0 = a + 2^64 * cf3)
    (ba1 : a1 < 2^64) (bcf3 : cf3 ≤ 1)
    (lt11 : t11 + a + 0 = b + 2^64 * cf2)
    (bt11 : t11 < 2^64) (bcf2 : cf2 ≤ 1)
    (ea2 : a2 = if cf3 = 0 then a1 else t11)
    (eb1 : b1 = if cf3 = 0 then b else a)
    (ef01 : f01 = if cf3 = 0 then f0 else f1)
    (eg01 : g01 = if cf3 = 0 then g0 else g1)
    (ef11 : f11 = if cf3 = 0 then f1 else f0)
    (eg11 : g11 = if cf3 = 0 then g1 else g0)
    (ea3 : a3 = a2 / 2^1)
    (et04 : t04 = if zf4 = 0 then f11 else t0)
    (et14 : t14 = if zf4 = 0 then g11 else t0)
    (lf02 : f02 + t04 + 0 = f01 + 2^64 * cf9) (bf02 : f02 < 2^64)
    (lg02 : g02 + t14 + 0 = g01 + 2^64 * cf10) (bg02 : g02 < 2^64)
    (lf12 : f12 + 2^64 * cf7 = f11 + f11 + 0) (bf12 : f12 < 2^64)
    (lg12 : g12 + 2^64 * cf8 = g11 + g11 + 0) (bg12 : g12 < 2^64) :
    a3 = (approxStep abstract).a ∧ b1 = (approxStep abstract).b ∧
      InvertMatrixRep ⟨f02, g02, f12, g12⟩ (approxStep abstract).matrix := by
  refine divsteps47_round_conclusion abstract a b a3 b1 f02 g02 f12 g12 ha hb ?_ ?_ ?_
  · intro hea
    have hz1 : zf1 = 1 := by
      rw [hzf1]
      exact (zeroFlag_bitAnd_one_eq_one_iff ba).2 hea
    have hz4 : zf4 = 1 := by
      rw [hzf4]
      exact (zeroFlag_bitAnd_one_eq_one_iff ba).2 hea
    have ht01 : t01 = 0 := by simp [et01, hz1, ht0]
    have hc3 : cf3 = 0 := by clear * - la1 ht01 ba1 bcf3; omega
    have ha1 : a1 = a := by clear * - la1 ht01 hc3; omega
    have ha2 : a2 = a := by simp [ea2, hc3, ha1]
    have hb1' : b1 = b := by simp [eb1, hc3]
    have hf01 : SignedWordRep f01 abstract.matrix.row0.left := by
      simpa [ef01, hc3] using hf0
    have hg01 : SignedWordRep g01 abstract.matrix.row0.right := by
      simpa [eg01, hc3] using hg0
    have hf11 : SignedWordRep f11 abstract.matrix.row1.left := by
      simpa [ef11, hc3] using hf1
    have hg11 : SignedWordRep g11 abstract.matrix.row1.right := by
      simpa [eg11, hc3] using hg1
    refine ⟨by rw [ea3, ha2]; norm_num, hb1', ?_, ?_,
      signedWordRep_double bf12 (by omega) hf11,
      signedWordRep_double bg12 (by omega) hg11⟩
    · have hzero : SignedWordRep t04 (0 : Int) := by simp [et04, hz4, ht0]
      simpa using signedWordRep_sub bf02 (by omega) hf01 hzero
    · have hzero : SignedWordRep t14 (0 : Int) := by simp [et14, hz4, ht0]
      simpa using signedWordRep_sub bg02 (by omega) hg01 hzero
  · intro hne hba
    have hz1 : zf1 = 0 := by
      rw [hzf1]
      exact (zeroFlag_bitAnd_one_eq_zero_iff ba).2 hne
    have hz4 : zf4 = 0 := by
      rw [hzf4]
      exact (zeroFlag_bitAnd_one_eq_zero_iff ba).2 hne
    have ht01 : t01 = b := by simp [et01, hz1]
    have hc3 : cf3 = 0 := by clear * - la1 ht01 hba ba1 bcf3; omega
    have ha1 : a1 = a - b := by clear * - la1 ht01 hc3 hba; omega
    have ha2 : a2 = a - b := by simp [ea2, hc3, ha1]
    have hb1' : b1 = b := by simp [eb1, hc3]
    have hf01 : SignedWordRep f01 abstract.matrix.row0.left := by
      simpa [ef01, hc3] using hf0
    have hg01 : SignedWordRep g01 abstract.matrix.row0.right := by
      simpa [eg01, hc3] using hg0
    have hf11 : SignedWordRep f11 abstract.matrix.row1.left := by
      simpa [ef11, hc3] using hf1
    have hg11 : SignedWordRep g11 abstract.matrix.row1.right := by
      simpa [eg11, hc3] using hg1
    refine ⟨by rw [ea3, ha2]; norm_num, hb1',
      signedWordRep_sub bf02 (by omega) hf01 ?_,
      signedWordRep_sub bg02 (by omega) hg01 ?_,
      signedWordRep_double bf12 (by omega) hf11,
      signedWordRep_double bg12 (by omega) hg11⟩
    · simpa [et04, hz4] using hf11
    · simpa [et14, hz4] using hg11
  · intro hne hab
    have hz1 : zf1 = 0 := by
      rw [hzf1]
      exact (zeroFlag_bitAnd_one_eq_zero_iff ba).2 hne
    have hz4 : zf4 = 0 := by
      rw [hzf4]
      exact (zeroFlag_bitAnd_one_eq_zero_iff ba).2 hne
    have ht01 : t01 = b := by simp [et01, hz1]
    have hc3 : cf3 = 1 := by clear * - la1 ht01 hab bcf3; omega
    have ht11 : t11 = b - a := by clear * - lt11 bt11 bcf2 hab; omega
    have ha2 : a2 = b - a := by simp [ea2, hc3, ht11]
    have hb1' : b1 = a := by simp [eb1, hc3]
    have hf01 : SignedWordRep f01 abstract.matrix.row1.left := by
      simpa [ef01, hc3] using hf1
    have hg01 : SignedWordRep g01 abstract.matrix.row1.right := by
      simpa [eg01, hc3] using hg1
    have hf11 : SignedWordRep f11 abstract.matrix.row0.left := by
      simpa [ef11, hc3] using hf0
    have hg11 : SignedWordRep g11 abstract.matrix.row0.right := by
      simpa [eg11, hc3] using hg0
    refine ⟨by rw [ea3, ha2]; norm_num, hb1',
      signedWordRep_sub bf02 (by omega) hf01 ?_,
      signedWordRep_sub bg02 (by omega) hg01 ?_,
      signedWordRep_double bf12 (by omega) hf11,
      signedWordRep_double bg12 (by omega) hg11⟩
    · simpa [et04, hz4] using hf11
    · simpa [et14, hz4] using hg11

/-! ## Packed 32-bit rows used by the 31-operation helper -/

/-- The per-lane bias used by Semolina's packed coefficient recurrence. -/
abbrev packedBias : Nat := 2^31 - 1

/-- The two-lane word bias `packedBias + 2^32 * packedBias`. -/
abbrev packedRowBias : Nat := packedBias + 2^32 * packedBias

/-- A packed register represents two signed row entries around `packedBias`, modulo one word. -/
def PackedRowRep (word : Nat) (row : SignedRow) : Prop :=
  SignedWordRep word ((packedRowBias : Int) + row.left + (2^32 : Int) * row.right)

/-- The asymmetric interval exactly supported by the bias encoding after `n` operations. -/
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
  have hp : 1 ≤ (2^n : Nat) := by exact Nat.one_le_two_pow
  have hp' : 1 ≤ (2^(n + 1) : Nat) := by exact Nat.one_le_two_pow
  rw [Int.ofNat_sub hp] at hl0 hl1
  rw [Int.ofNat_sub hp']
  norm_num [pow_succ] at *
  constructor <;> omega

private theorem biasBounded_double {n : Nat} {row : SignedRow} (h : BiasBoundedRow n row) :
    BiasBoundedRow (n + 1) row.double := by
  rcases h with ⟨hl0, hu0, hl1, hu1⟩
  simp only [BiasBoundedRow, SignedRow.double] at *
  have hp : 1 ≤ (2^n : Nat) := by exact Nat.one_le_two_pow
  have hp' : 1 ≤ (2^(n + 1) : Nat) := by exact Nat.one_le_two_pow
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
  have hp : 1 ≤ (2^n : Nat) := by exact Nat.one_le_two_pow
  have hp' : 1 ≤ (2^(n + 1) : Nat) := by exact Nat.one_le_two_pow
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

/-- The first packed wrapper constant represents the first identity row. -/
theorem packedRowRep_identity_row0 :
    PackedRowRep 9223372034707292160 identityMatrix.row0 := by
  norm_num [PackedRowRep, SignedWordRep, packedRowBias, packedBias, identityMatrix]

/-- The second packed wrapper constant represents the second identity row. -/
theorem packedRowRep_identity_row1 :
    PackedRowRep 9223372039002259455 identityMatrix.row1 := by
  norm_num [PackedRowRep, SignedWordRep, packedRowBias, packedBias, identityMatrix]

/-- The wrapper's subtraction constant is the packed two-lane bias. -/
theorem packedRowBias_eq : packedRowBias = 9223372034707292159 := by
  norm_num [packedRowBias, packedBias]

/-- Identity rows start inside the zero-operation packed interval. -/
theorem identityMatrix_biasBounded : BiasBoundedMatrix 0 identityMatrix := by
  norm_num [BiasBoundedMatrix, BiasBoundedRow, identityMatrix]

/-- The matrix of the concrete short loop fits exactly in the two biased 32-bit lanes. -/
theorem semolinaShort_biasBounded (a b : Nat) :
    BiasBoundedMatrix 31 (semolinaShort a b).matrix := by
  unfold semolinaShort
  simpa using approxSteps_biasBounded 31 (state := ApproxState.initial (semolinaApprox a b).1
    (semolinaApprox a b).2) (n := 0) (by
      simpa [ApproxState.initial] using identityMatrix_biasBounded)

/-- Packed representation of a row subtraction, using the shared bias word. -/
theorem packedRowRep_sub {out difference biasWord : Nat} {left right : SignedRow}
    (hdifference : SignedWordRep difference
      (left.left - right.left + (2^32 : Int) * (left.right - right.right)))
    (hbias : SignedWordRep biasWord packedRowBias)
    (hout : out < 2^64)
    (hlin : out + 2^64 * (0:Nat) = difference + biasWord) :
    PackedRowRep out (left.sub right) := by
  have hadd := signedWordRep_add hout hlin hdifference hbias
  have heq :
      left.left - right.left + (2^32 : Int) * (left.right - right.right) + packedRowBias =
        (packedRowBias : Int) + (left.left - right.left) +
          (2^32 : Int) * (left.right - right.right) := by ring
  simpa only [PackedRowRep, SignedRow.sub, heq] using hadd

/-- Packed representation of a doubled row, after removing one copy of the bias. -/
theorem packedRowRep_double {out doubled biasWord borrow : Nat} {row : SignedRow}
    (hdoubled : SignedWordRep doubled
      (2 * ((packedRowBias : Int) + row.left + (2^32 : Int) * row.right)))
    (hbias : SignedWordRep biasWord packedRowBias)
    (hout : out < 2^64) (hlin : out + biasWord = doubled + 2^64 * borrow) :
    PackedRowRep out row.double := by
  have hsub := signedWordRep_sub hout hlin hdoubled hbias
  have heq :
      2 * ((packedRowBias : Int) + row.left + (2^32 : Int) * row.right) - packedRowBias =
        (packedRowBias : Int) + 2 * row.left + (2^32 : Int) * (2 * row.right) := by ring
  simpa only [PackedRowRep, SignedRow.double, heq] using hsub

/-- Decode the two output lanes of a fully bounded packed row after subtracting the lane bias. -/
theorem packedRowRep_decode {word low high lowOut highOut lowBorrow highBorrow : Nat}
    {row : SignedRow} (hrow : PackedRowRep word row) (hbound : BiasBoundedRow 31 row)
    (hlow : low = word32 word) (hhigh : high = word / 2^32)
    (hlowSub : lowOut + packedBias + 0 = low + 2^64 * lowBorrow)
    (hhighSub : highOut + packedBias + 0 = high + 2^64 * highBorrow)
    (blowOut : lowOut < 2^64) (bhighOut : highOut < 2^64) :
    SignedWordRep lowOut row.left ∧ SignedWordRep highOut row.right := by
  rcases hrow with ⟨bword, ⟨k, hk⟩⟩
  rcases hbound with ⟨hlower, hupper, hrlower, hrupper⟩
  have hbias : (packedRowBias : Int) = packedBias + (2^32 : Int) * packedBias := by rfl
  have hleftNonneg : 0 ≤ (packedBias : Int) + row.left := by
    norm_num [packedBias] at hlower ⊢
    omega
  have hleftLt : (packedBias : Int) + row.left < 2^32 := by
    norm_num [packedBias] at hupper ⊢
    omega
  have hrightNonneg : 0 ≤ (packedBias : Int) + row.right := by
    norm_num [packedBias] at hrlower ⊢
    omega
  have hrightLt : (packedBias : Int) + row.right < 2^32 := by
    norm_num [packedBias] at hrupper ⊢
    omega
  let leftNat := ((packedBias : Int) + row.left).toNat
  let rightNat := ((packedBias : Int) + row.right).toNat
  have hleftCast : (leftNat : Int) = (packedBias : Int) + row.left := by
    exact Int.toNat_of_nonneg hleftNonneg
  have hrightCast : (rightNat : Int) = (packedBias : Int) + row.right := by
    exact Int.toNat_of_nonneg hrightNonneg
  have hleftNatLt : leftNat < 2^32 := by
    change ((packedBias : Int) + row.left).toNat < 2^32
    exact (Int.toNat_lt hleftNonneg).2 hleftLt
  have hrightNatLt : rightNat < 2^32 := by
    change ((packedBias : Int) + row.right).toNat < 2^32
    exact (Int.toNat_lt hrightNonneg).2 hrightLt
  have hpackedCast : ((leftNat + 2^32 * rightNat : Nat) : Int) =
      (packedRowBias : Int) + row.left + (2^32 : Int) * row.right := by
    push_cast
    rw [hleftCast, hrightCast]
    norm_num [packedBias, packedRowBias]
    ring
  have hpackedLt : leftNat + 2^32 * rightNat < 2^64 := by omega
  have hword : word = leftNat + 2^32 * rightNat := by
    have hk' : (word : Int) - ((leftNat + 2^32 * rightNat : Nat) : Int) = (2^64 : Int) * k := by
      rw [hpackedCast]
      simpa [mul_comm] using hk
    have hkzero : k = 0 := by
      have hwordNonneg : (0 : Int) ≤ word := by positivity
      have hwordLt : (word : Int) < 2^64 := by exact_mod_cast bword
      have hpackedNonneg : (0 : Int) ≤ leftNat + 2^32 * rightNat := by positivity
      have hpackedLt' : (leftNat + 2^32 * rightNat : Int) < 2^64 := by exact_mod_cast hpackedLt
      omega
    have hwordInt : (word : Int) = (leftNat + 2^32 * rightNat : Nat) := by
      rw [hkzero, mul_zero] at hk'
      omega
    exact_mod_cast hwordInt
  have hlowEq : low = leftNat := by
    rw [hlow, hword]
    simp only [word32, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hleftNatLt]
  have hhighEq : high = rightNat := by
    rw [hhigh, hword, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hleftNatLt,
      Nat.zero_add]
  have hlowRep : SignedWordRep low ((packedBias : Int) + row.left) := by
    refine ⟨hlowEq.trans_lt hleftNatLt |>.trans (by norm_num), ?_⟩
    rw [hlowEq, hleftCast]
    simp
  have hhighRep : SignedWordRep high ((packedBias : Int) + row.right) := by
    refine ⟨hhighEq.trans_lt hrightNatLt |>.trans (by norm_num), ?_⟩
    rw [hhighEq, hrightCast]
    simp
  have hbiasRep : SignedWordRep packedBias packedBias := by
    refine ⟨by norm_num [packedBias], ?_⟩
    simp
  constructor
  · have h := signedWordRep_sub blowOut (by omega) hlowRep hbiasRep
    convert h using 1
    all_goals ring
  · have h := signedWordRep_sub bhighOut (by omega) hhighRep hbiasRep
    convert h using 1
    all_goals ring

/-- Iterating the concrete packed helper follows the shared recurrence. -/
theorem divsteps31_iterate_spec (n : Nat) (s : Divsteps31State) (abstract : ApproxState)
    (hs : s.Bounded) (hstate : s.a0 = abstract.a ∧ s.b0 = abstract.b)
    (hrows : PackedRowRep s.a1 abstract.matrix.row0 ∧
      PackedRowRep s.a2 abstract.matrix.row1)
    (hbias : s.a3 = packedRowBias) (hodd : Odd abstract.b)
    (hround : ∀ (s : Divsteps31State) (abstract : ApproxState),
      s.Bounded → s.a0 = abstract.a ∧ s.b0 = abstract.b →
      PackedRowRep s.a1 abstract.matrix.row0 ∧ PackedRowRep s.a2 abstract.matrix.row1 →
      s.a3 = packedRowBias → Odd abstract.b →
      let s' := divsteps31Round s
      s'.Bounded ∧ s'.a0 = (approxStep abstract).a ∧
        s'.b0 = (approxStep abstract).b ∧
        PackedRowRep s'.a1 (approxStep abstract).matrix.row0 ∧
        PackedRowRep s'.a2 (approxStep abstract).matrix.row1 ∧
        s'.a3 = packedRowBias ∧ Odd (approxStep abstract).b) :
    let s' := iterate divsteps31Round n s
    let abstract' := approxSteps n abstract
    s'.Bounded ∧ s'.a0 = abstract'.a ∧ s'.b0 = abstract'.b ∧
      PackedRowRep s'.a1 abstract'.matrix.row0 ∧
      PackedRowRep s'.a2 abstract'.matrix.row1 ∧ s'.a3 = packedRowBias := by
  induction n generalizing s abstract with
  | zero => exact ⟨hs, hstate.1, hstate.2, hrows.1, hrows.2, hbias⟩
  | succ n ih =>
      rw [iterate, approxSteps]
      rcases hround s abstract hs hstate hrows hbias hodd with
        ⟨hs', ha', hb', hrow0', hrow1', hbias', hodd'⟩
      exact ih (divsteps31Round s) (approxStep abstract) hs' ⟨ha', hb'⟩
        ⟨hrow0', hrow1'⟩ hbias' hodd'

end PastaAsm.X86_64
