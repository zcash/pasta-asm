/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.InversionSpec
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Shared arithmetic for final inversion-coefficient normalization

Both inversion backends hold the final signed coefficient in nine 64-bit words.
They leave its low four words unchanged and add an aligned `2 * p` to the high
four words when the coefficient is negative.  The remaining ninth word then
selects one more addition or subtraction of the same aligned value.

This file isolates the integer arithmetic needed to justify that scheme.  The
schedule's general `2^512` absolute-value bound is deliberately not promoted to
the stronger positive bound needed by normalization: for a Pasta-sized `p`,
`2 * p * 2^256` is strictly smaller than `2^512`.
-/

namespace PastaAsm
namespace InversionNormalization

/-- Radix separating the low and high four-word halves. -/
abbrev splitRadix : Nat := 2^256

/-- Radix separating the first eight words from the signed excess word. -/
abbrev coefficientRadix : Nat := 2^512

/-- The doubled modulus aligned above the unchanged low half. -/
def alignedModulus (p : Nat) : Nat := 2 * p * splitRadix

/-- The numerical hypotheses common to the two Pasta moduli.  Oddness is part
of the field hypothesis, although normalization itself only uses the bounds. -/
def PastaSizedOdd (p : Nat) : Prop := Odd p ∧ 2^254 ≤ p ∧ p < 2^255

/-- The first normalization stage conditionally adds the aligned doubled
modulus to a negative coefficient. -/
def firstAdjustment (p : Nat) (c : Int) : Int :=
  if c < 0 then c + alignedModulus p else c

/-- The signed value represented by the ninth word after the first stage, on
the range used by the implementation. -/
def signedExcess (value : Int) : Int :=
  if value < 0 then -1 else if value < coefficientRadix then 0 else 1

/-- The second stage adds, does nothing, or subtracts the aligned modulus when
`excess` is respectively `-1`, `0`, or `1`. -/
def secondAdjustment (p : Nat) (first excess : Int) : Int :=
  first - excess * alignedModulus p

/-- The complete two-stage arithmetic implemented by both backends. -/
def normalize (p : Nat) (c : Int) : Int :=
  let first := firstAdjustment p c
  secondAdjustment p first (signedExcess first)

/-- `excess` is the signed ninth word above an eight-word residue `low`.
This relation is the arithmetic interface for either ISA's carry chain. -/
def RepresentsExcess (value excess : Int) : Prop :=
  ∃ low : Nat, low < coefficientRadix ∧
    value = (low : Int) + (coefficientRadix : Int) * excess

/-- The aligned doubled modulus is positive. -/
theorem alignedModulus_pos {p : Nat} (hp : PastaSizedOdd p) :
    0 < alignedModulus p := by
  unfold PastaSizedOdd alignedModulus at *
  have : 0 < p := by omega
  positivity

/-- The Pasta lower bound makes one aligned modulus at least half of the
unsigned eight-word range. -/
theorem half_coefficientRadix_le_alignedModulus {p : Nat} (hp : PastaSizedOdd p) :
    2^511 ≤ alignedModulus p := by
  unfold PastaSizedOdd alignedModulus at *
  have hpow : 2^511 = 2 * 2^254 * 2^256 := by
    rw [show 511 = 255 + 256 by omega, pow_add,
      show 255 = 254 + 1 by omega, pow_succ]
    ring
  rw [hpow]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hp.2.1)

/-- The Pasta upper bound makes one aligned modulus strictly smaller than the
unsigned eight-word range. -/
theorem alignedModulus_lt_coefficientRadix {p : Nat} (hp : PastaSizedOdd p) :
    alignedModulus p < coefficientRadix := by
  unfold PastaSizedOdd alignedModulus coefficientRadix at *
  have hleft : 2 * p < 2 * 2^255 := by omega
  have hlt : 2 * p * 2^256 < 2 * 2^255 * 2^256 :=
    Nat.mul_lt_mul_of_pos_right hleft (Nat.two_pow_pos 256)
  have hpow : 2 * 2^255 * 2^256 = 2^512 := by
    rw [show 512 = 256 + 256 by omega, pow_add,
      show 256 = 255 + 1 by omega, pow_succ]
    ring
  exact hlt.trans_eq hpow

/-- The schedule bound and the Pasta lower bound ensure that two aligned
moduli cover the whole signed negative half of the coefficient range. -/
theorem coefficientRadix_le_two_alignedModulus {p : Nat} (hp : PastaSizedOdd p) :
    coefficientRadix ≤ 2 * alignedModulus p := by
  have h := half_coefficientRadix_le_alignedModulus hp
  unfold coefficientRadix at *
  omega

/-- Under the schedule's signed bound, the first-stage value really decomposes
into an eight-word residue and a ninth word equal to `-1`, `0`, or `1`. -/
theorem firstAdjustment_represents_signedExcess {p : Nat} {c : Int}
    (hp : PastaSizedOdd p)
    (hlower : -(coefficientRadix : Int) ≤ c)
    (hupper : c ≤ coefficientRadix) :
    RepresentsExcess (firstAdjustment p c)
      (signedExcess (firstAdjustment p c)) := by
  have hMpos : (0 : Int) < alignedModulus p := by
    exact_mod_cast alignedModulus_pos hp
  have hMlt : (alignedModulus p : Int) < coefficientRadix := by
    exact_mod_cast alignedModulus_lt_coefficientRadix hp
  unfold firstAdjustment
  by_cases hc : c < 0
  · rw [if_pos hc]
    have hfirstLower : -(coefficientRadix : Int) < c + alignedModulus p := by omega
    have hfirstUpper : c + alignedModulus p < coefficientRadix := by omega
    unfold signedExcess
    by_cases hnegative : c + alignedModulus p < 0
    · rw [if_pos hnegative]
      let low := Int.toNat (c + alignedModulus p + coefficientRadix)
      refine ⟨low, ?_, ?_⟩
      · have hnonneg : 0 ≤ c + alignedModulus p + coefficientRadix := by omega
        have hlt : c + alignedModulus p + coefficientRadix < coefficientRadix := by omega
        rw [Int.toNat_lt hnonneg]
        exact_mod_cast hlt
      · have hnonneg : 0 ≤ c + alignedModulus p + coefficientRadix := by omega
        rw [show (low : Int) = c + alignedModulus p + coefficientRadix by
          simp only [low, Int.toNat_of_nonneg hnonneg]]
        ring
    · rw [if_neg hnegative, if_pos hfirstUpper]
      let low := Int.toNat (c + alignedModulus p)
      refine ⟨low, ?_, ?_⟩
      · have hnonneg : 0 ≤ c + alignedModulus p := by omega
        rw [Int.toNat_lt hnonneg]
        exact_mod_cast hfirstUpper
      · have hnonneg : 0 ≤ c + alignedModulus p := by omega
        rw [show (low : Int) = c + alignedModulus p by
          simp only [low, Int.toNat_of_nonneg hnonneg]]
        ring
  · rw [if_neg hc]
    have hc0 : 0 ≤ c := by omega
    unfold signedExcess
    rw [if_neg hc]
    by_cases hbelow : c < coefficientRadix
    · rw [if_pos hbelow]
      let low := Int.toNat c
      refine ⟨low, ?_, ?_⟩
      · rw [Int.toNat_lt hc0]
        exact_mod_cast hbelow
      · rw [show (low : Int) = c by simp only [low, Int.toNat_of_nonneg hc0]]
        ring
    · rw [if_neg hbelow]
      have hcW : c = coefficientRadix := by omega
      refine ⟨0, by simp, ?_⟩
      rw [hcW]
      ring

/-- The numeric ninth-word interpretation used by `excess | -excess` is valid
on the schedule range: only `-1`, `0`, and `1` can occur. -/
theorem signedExcess_eq_neg_one_or_zero_or_one (value : Int) :
    signedExcess value = -1 ∨ signedExcess value = 0 ∨ signedExcess value = 1 := by
  unfold signedExcess
  split_ifs <;> simp

/-- Exact arithmetic specification for successful normalization.  The lower
bound is supplied by the schedule's absolute-value estimate; the additional
strict positive bound is the condition not supplied by that estimate.

The multiplier records that only aligned doubled moduli were added.  It makes
both preservation modulo `p` and preservation of the low `2^256` residue
immediate for downstream instruction proofs. -/
theorem normalize_spec {p : Nat} {c : Int}
    (hp : PastaSizedOdd p)
    (hlower : -(coefficientRadix : Int) ≤ c)
    (hpositive : c < alignedModulus p) :
    0 ≤ normalize p c ∧ normalize p c < alignedModulus p ∧
      ∃ k : Int, normalize p c = c + k * alignedModulus p := by
  have hMpos : (0 : Int) < alignedModulus p := by
    exact_mod_cast alignedModulus_pos hp
  have hMlt : (alignedModulus p : Int) < coefficientRadix := by
    exact_mod_cast alignedModulus_lt_coefficientRadix hp
  have hcoverNat := coefficientRadix_le_two_alignedModulus hp
  have hcover : (coefficientRadix : Int) ≤ 2 * alignedModulus p := by
    exact_mod_cast hcoverNat
  by_cases hc : c < 0
  · have hfirstUpper : c + alignedModulus p < coefficientRadix := by omega
    by_cases hnegative : c + alignedModulus p < 0
    · simp only [normalize, firstAdjustment, if_pos hc, secondAdjustment,
        signedExcess, if_pos hnegative]
      refine ⟨by omega, by omega, ⟨2, by ring⟩⟩
    · simp only [normalize, firstAdjustment, if_pos hc, secondAdjustment,
        signedExcess, if_neg hnegative, if_pos hfirstUpper]
      refine ⟨by omega, by omega, ⟨1, by ring⟩⟩
  · have hc0 : 0 ≤ c := by omega
    have hcW : c < coefficientRadix := hpositive.trans hMlt
    simp only [normalize, firstAdjustment, if_neg hc, secondAdjustment,
      signedExcess, if_pos hcW]
    refine ⟨by omega, by omega, ⟨0, by ring⟩⟩

/-- Successful normalization preserves the coefficient modulo the field
modulus. -/
theorem normalize_sub_dvd_modulus {p : Nat} {c : Int}
    (hp : PastaSizedOdd p)
    (hlower : -(coefficientRadix : Int) ≤ c)
    (hpositive : c < alignedModulus p) :
    (p : Int) ∣ normalize p c - c := by
  obtain ⟨_, _, k, hk⟩ := normalize_spec hp hlower hpositive
  refine ⟨k * (2 * splitRadix), ?_⟩
  rw [hk]
  unfold alignedModulus
  push_cast
  ring

/-- Successful normalization preserves the coefficient's integer remainder
modulo the field modulus. -/
theorem normalize_emod_modulus_eq {p : Nat} {c : Int}
    (hp : PastaSizedOdd p)
    (hlower : -(coefficientRadix : Int) ≤ c)
    (hpositive : c < alignedModulus p) :
    normalize p c % p = c % p := by
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
  obtain ⟨k, hk⟩ := normalize_sub_dvd_modulus hp hlower hpositive
  rw [hk]
  simp

/-- Because every adjustment is aligned at bit 256, the low half is unchanged. -/
theorem normalize_sub_dvd_splitRadix {p : Nat} {c : Int}
    (hp : PastaSizedOdd p)
    (hlower : -(coefficientRadix : Int) ≤ c)
    (hpositive : c < alignedModulus p) :
    (splitRadix : Int) ∣ normalize p c - c := by
  obtain ⟨_, _, k, hk⟩ := normalize_spec hp hlower hpositive
  refine ⟨k * (2 * p), ?_⟩
  rw [hk]
  unfold alignedModulus
  push_cast
  ring

/-- Remainder equality is the direct arithmetic statement that the low 256
bits are unchanged by the aligned adjustments. -/
theorem normalize_emod_splitRadix_eq {p : Nat} {c : Int}
    (hp : PastaSizedOdd p)
    (hlower : -(coefficientRadix : Int) ≤ c)
    (hpositive : c < alignedModulus p) :
    normalize p c % splitRadix = c % splitRadix := by
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
  obtain ⟨k, hk⟩ := normalize_sub_dvd_splitRadix hp hlower hpositive
  rw [hk]
  simp

/-- Splitting any selected representative at bit 256 produces a high half
strictly below `2p`, justifying the following single conditional subtraction. -/
theorem split_high_lt_two_mul_modulus {p normalized : Nat}
    (hnormalized : normalized < alignedModulus p) :
    normalized / splitRadix < 2 * p := by
  apply Nat.div_lt_of_lt_mul
  simpa [alignedModulus, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hnormalized

/-- The shared `2^512` coefficient bound does not imply the extra positive
normalization bound.  The aligned modulus itself is a counterexample: it obeys
the schedule bound, has ninth word zero, and is therefore left unchanged even
though it is not in the required half-open interval. -/
theorem schedule_bound_insufficient {p : Nat} (hp : PastaSizedOdd p) :
    ∃ c : Int, c.natAbs ≤ coefficientRadix ∧
      ¬ c < alignedModulus p ∧ normalize p c = c := by
  have hMpos := alignedModulus_pos hp
  have hMlt := alignedModulus_lt_coefficientRadix hp
  refine ⟨alignedModulus p, ?_, ?_, ?_⟩
  · simpa using Nat.le_of_lt hMlt
  · simp
  · have hMposInt : (0 : Int) < alignedModulus p := by exact_mod_cast hMpos
    have hMltInt : (alignedModulus p : Int) < coefficientRadix := by exact_mod_cast hMlt
    have hnotneg : ¬ (alignedModulus p : Int) < 0 := not_lt.mpr hMposInt.le
    simp only [normalize, firstAdjustment, if_neg hnotneg, secondAdjustment,
      signedExcess, if_pos hMltInt]
    ring

end InversionNormalization
end PastaAsm
