/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.InversionSpec
import Mathlib.Data.Nat.ModEq
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

/-- Exact arithmetic specification on the schedule's complete signed range.
The normalizer selects a nonnegative eight-word representative, but unlike
`normalize_spec` it does not necessarily select one below the aligned doubled
modulus.  The positive endpoint `coefficientRadix` is reduced once, while
smaller nonnegative inputs are unchanged; negative inputs receive one or two
aligned moduli.

The multiplier records that the field residue and low `2^256` bits are
preserved. -/
theorem normalize_schedule_spec {p : Nat} {c : Int}
    (hp : PastaSizedOdd p)
    (hlower : -(coefficientRadix : Int) ≤ c)
    (hupper : c ≤ coefficientRadix) :
    0 ≤ normalize p c ∧ normalize p c < coefficientRadix ∧
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
    by_cases hcW : c < coefficientRadix
    · simp only [normalize, firstAdjustment, if_neg hc, secondAdjustment,
        signedExcess, if_pos hcW]
      refine ⟨by omega, by omega, ⟨0, by ring⟩⟩
    · have hcEq : c = coefficientRadix := by omega
      simp only [normalize, firstAdjustment, if_neg hc, secondAdjustment,
        signedExcess, if_neg hcW]
      refine ⟨by omega, by omega, ⟨-1, by ring⟩⟩

/-- On the complete schedule range, normalization preserves the coefficient
modulo the field modulus. -/
theorem normalize_schedule_sub_dvd_modulus {p : Nat} {c : Int}
    (hp : PastaSizedOdd p)
    (hlower : -(coefficientRadix : Int) ≤ c)
    (hupper : c ≤ coefficientRadix) :
    (p : Int) ∣ normalize p c - c := by
  obtain ⟨_, _, k, hk⟩ := normalize_schedule_spec hp hlower hupper
  refine ⟨k * (2 * splitRadix), ?_⟩
  rw [hk]
  unfold alignedModulus
  push_cast
  ring

/-- On the complete schedule range, normalization preserves the coefficient's
integer remainder modulo the field modulus. -/
theorem normalize_schedule_emod_modulus_eq {p : Nat} {c : Int}
    (hp : PastaSizedOdd p)
    (hlower : -(coefficientRadix : Int) ≤ c)
    (hupper : c ≤ coefficientRadix) :
    normalize p c % p = c % p := by
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
  obtain ⟨k, hk⟩ := normalize_schedule_sub_dvd_modulus hp hlower hupper
  rw [hk]
  simp

/-- On the complete schedule range, the adjustments leave the low 256 bits
unchanged. -/
theorem normalize_schedule_sub_dvd_splitRadix {p : Nat} {c : Int}
    (hp : PastaSizedOdd p)
    (hlower : -(coefficientRadix : Int) ≤ c)
    (hupper : c ≤ coefficientRadix) :
    (splitRadix : Int) ∣ normalize p c - c := by
  obtain ⟨_, _, k, hk⟩ := normalize_schedule_spec hp hlower hupper
  refine ⟨k * (2 * p), ?_⟩
  rw [hk]
  unfold alignedModulus
  push_cast
  ring

/-- Remainder equality states directly that normalization on the complete
schedule range leaves the low 256 bits unchanged. -/
theorem normalize_schedule_emod_splitRadix_eq {p : Nat} {c : Int}
    (hp : PastaSizedOdd p)
    (hlower : -(coefficientRadix : Int) ≤ c)
    (hupper : c ≤ coefficientRadix) :
    normalize p c % splitRadix = c % splitRadix := by
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
  obtain ⟨k, hk⟩ := normalize_schedule_sub_dvd_splitRadix hp hlower hupper
  rw [hk]
  simp

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

/-- Splitting any eight-word representative at bit 256 produces a high half
strictly below the four-word radix. -/
theorem split_high_lt_splitRadix {normalized : Nat}
    (hnormalized : normalized < coefficientRadix) :
    normalized / splitRadix < splitRadix := by
  apply Nat.div_lt_of_lt_mul
  calc
    normalized < coefficientRadix := hnormalized
    _ = splitRadix * splitRadix := by
      change 2^512 = 2^256 * 2^256
      rw [show 512 = 256 + 256 by omega, pow_add]

/-- On the complete schedule range, the high half of the normalized
representative fits in four words. -/
theorem normalize_schedule_high_lt_splitRadix {p : Nat} {c : Int}
    (hp : PastaSizedOdd p)
    (hlower : -(coefficientRadix : Int) ≤ c)
    (hupper : c ≤ coefficientRadix) :
    (normalize p c).toNat / splitRadix < splitRadix := by
  obtain ⟨hnonneg, hlt, _⟩ := normalize_schedule_spec hp hlower hupper
  apply split_high_lt_splitRadix
  rw [Int.toNat_lt hnonneg]
  exact hlt

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

/-!
# Shared arithmetic for full-width Montgomery reduction

The inversion backends use different instruction schedules for reducing a
512-bit coefficient, but their final arithmetic is the same.  Four Montgomery
cancellation rounds produce a low-half quotient `y`; the original high half is
then added to `y`, including the carry above the four-word radix.  A single
subtraction of `p` is selected by comparing this full candidate with `p`.

The selected result is a bounded four-word value, but is intentionally not
claimed to be canonical.  The following multiplication by canonical `R²`
performs the final canonical reduction.
-/
namespace REDC

/-- The shared mathematical effect of the carry-aware final subtraction.
The comparison is against the full candidate, before truncation at `R`. -/
def carryCorrect (candidate p : Nat) : Nat :=
  if candidate < p then candidate else candidate - p

/-- A full candidate below `R + p` becomes a bounded `R`-word value after the
carry-aware subtraction, while retaining the same residue modulo `p`.

There is deliberately no conclusion that the result is below `p`: when the
candidate is at least `R`, subtracting `p` need not produce a canonical
representative. -/
theorem carryCorrect_spec {R p candidate : Nat}
    (hpR : p < R) (hcandidate : candidate < R + p) :
    carryCorrect candidate p < R ∧
      carryCorrect candidate p ≡ candidate [MOD p] := by
  unfold carryCorrect
  by_cases hlt : candidate < p
  · rw [if_pos hlt]
    exact ⟨hlt.trans hpR, Nat.ModEq.rfl⟩
  · rw [if_neg hlt]
    have hple : p ≤ candidate := by omega
    refine ⟨by omega, ?_⟩
    unfold Nat.ModEq
    rw [← Nat.add_mul_mod_self_right (candidate - p) 1 p]
    simp only [one_mul, Nat.sub_add_cancel hple]

/-- The high half of a value `T = lo + R * hi < R²` is below `R`, so adding a
low-half reduction bounded by `p` gives a candidate below `R + p`. -/
theorem full512_candidate_lt {R p T lo hi y : Nat}
    (hp : 0 < p) (hpR : p < R)
    (hT : T = lo + R * hi) (hTlt : T < R * R) (hy : y ≤ p) :
    hi + y < R + p := by
  have hRpos : 0 < R := hp.trans hpR
  have hRhi : R * hi < R * R := by
    calc
      R * hi ≤ lo + R * hi := Nat.le_add_left _ _
      _ = T := hT.symm
      _ < R * R := hTlt
  have hhi : hi < R := (Nat.mul_lt_mul_left hRpos).mp hRhi
  omega

/-- Shared full-width REDC arithmetic.  If `T` is split at radix `R`, and the
low-half Montgomery cancellation satisfies `y * R = lo + m * p`, then the
carry-aware correction of `hi + y` is bounded by `R` and represents `T / R`
modulo `p`.

The bounds `m < R` and `y ≤ p` are the natural contracts exposed by the four
cancellation rounds.  The result is only a lazy residue below `R`, not
necessarily a canonical residue below `p`. -/
theorem full512_spec {R p T lo hi m y : Nat}
    (hp : 0 < p) (hpR : p < R)
    (hT : T = lo + R * hi) (hTlt : T < R * R)
    (hcancellation : y * R = lo + m * p) (_hm : m < R) (hy : y ≤ p) :
    carryCorrect (hi + y) p < R ∧
      R * carryCorrect (hi + y) p ≡ T [MOD p] := by
  have hcandidate := full512_candidate_lt hp hpR hT hTlt hy
  obtain ⟨hbound, hcorrect⟩ := carryCorrect_spec hpR hcandidate
  refine ⟨hbound, (Nat.ModEq.mul_left R hcorrect).trans ?_⟩
  have heq : R * (hi + y) = T + m * p := by
    calc
      R * (hi + y) = R * hi + y * R := by ring
      _ = R * hi + (lo + m * p) := by rw [hcancellation]
      _ = (lo + R * hi) + m * p := by ring
      _ = T + m * p := by rw [hT]
  unfold Nat.ModEq
  rw [heq, Nat.add_mul_mod_self_right]

/-- Multiplication by a representative of `R²` removes the Montgomery factor
from a REDC result.  Cancellation of `R` is explicit: it requires `R` to be
coprime to `p`, as it is for a power of two and either odd Pasta modulus. -/
theorem final_mul_rr_modEq {R p T reduced rr out : Nat}
    (hcoprime : R.Coprime p)
    (hreduced : R * reduced ≡ T [MOD p])
    (hrr : rr ≡ R^2 [MOD p])
    (hmul : R * out ≡ reduced * rr [MOD p]) :
    out ≡ T [MOD p] := by
  have hscaled : R * out ≡ R * T [MOD p] := by
    calc
      R * out ≡ reduced * rr [MOD p] := hmul
      _ ≡ reduced * R^2 [MOD p] := Nat.ModEq.mul_left reduced hrr
      _ = R * (R * reduced) := by ring
      _ ≡ R * T [MOD p] := Nat.ModEq.mul_left R hreduced
  exact Nat.ModEq.cancel_left_of_coprime hcoprime.symm.gcd_eq_one hscaled

/-- Convenience composition of full-width REDC with the final canonical
multiplication by `R²`.  The multiplication block supplies `out < p`; this
lemma supplies the resulting residue `out ≡ T (mod p)`. -/
theorem full512_final_mul_rr_spec {R p T lo hi m y rr out : Nat}
    (hp : 0 < p) (hpR : p < R) (hcoprime : R.Coprime p)
    (hT : T = lo + R * hi) (hTlt : T < R * R)
    (hcancellation : y * R = lo + m * p) (hm : m < R) (hy : y ≤ p)
    (hrr : rr ≡ R^2 [MOD p]) (hout : out < p)
    (hmul : R * out ≡ carryCorrect (hi + y) p * rr [MOD p]) :
    out < p ∧ out ≡ T [MOD p] := by
  obtain ⟨_, hreduced⟩ := full512_spec hp hpR hT hTlt hcancellation hm hy
  exact ⟨hout, final_mul_rr_modEq hcoprime hreduced hrr hmul⟩

end REDC
end PastaAsm
