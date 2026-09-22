/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.Inversion
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Arithmetic facts shared by the inversion proofs

This file deliberately separates facts about the coefficient recurrences from
facts about an exact binary-GCD step.  In particular, it does **not** identify a
31-step high/low approximation batch with 31 exact steps on the full-width
state.  The approximation used by the assembly is allowed to choose a different
control path.  An instruction-level proof can instead use:

* `CoeffStep` and `CoeffSteps` for the three row operations performed by either
  inner loop, independently of which approximation chose them;
* `ScaledTransition.preserves_invariant` once the full-width update block has
  established its two integer row equations; and
* `exactSteps_product_eq_zero` for the final exact low-limb tail, after a
  separate proof has shown that the remaining state fits and has product below
  the required power of two.

The coefficient bounds account for the actual schedule: fifteen 31-operation
matrices followed by one 47-operation row have `ℓ₁` growth at most
`2^(15*31+47) = 2^512`.  They do not assume that the first fifteen control paths
are exact full-width binary-GCD paths.
-/

namespace PastaAsm
namespace InversionSpec

/-- A signed row of a batched transition matrix. -/
structure SignedRow where
  left : Int
  right : Int
  deriving DecidableEq, Repr

namespace SignedRow

/-- Apply a matrix row to a pair. -/
def apply (r : SignedRow) (x y : Int) : Int := r.left * x + r.right * y

/-- The row's `ℓ₁` norm. -/
def norm (r : SignedRow) : Nat := r.left.natAbs + r.right.natAbs

/-- Double every entry of a row. -/
def double (r : SignedRow) : SignedRow := ⟨2 * r.left, 2 * r.right⟩

/-- Subtract two rows entrywise. -/
def sub (r s : SignedRow) : SignedRow := ⟨r.left - s.left, r.right - s.right⟩

@[simp] theorem norm_zero_right (x : Int) : norm ⟨x, 0⟩ = x.natAbs := by
  simp [norm]

@[simp] theorem norm_zero_left (x : Int) : norm ⟨0, x⟩ = x.natAbs := by
  simp [norm]

/-- Doubling a row doubles its `ℓ₁` norm. -/
theorem norm_double (r : SignedRow) : norm r.double = 2 * norm r := by
  simp [norm, double, Int.natAbs_mul, Nat.mul_add]

/-- The `ℓ₁` norm satisfies the triangle inequality for row subtraction. -/
theorem norm_sub_le (r s : SignedRow) : norm (r.sub s) ≤ norm r + norm s := by
  calc
    norm (r.sub s) = (r.left - s.left).natAbs + (r.right - s.right).natAbs := rfl
    _ ≤ (r.left.natAbs + s.left.natAbs) + (r.right.natAbs + s.right.natAbs) :=
      Nat.add_le_add (Int.natAbs_sub_le r.left s.left)
        (Int.natAbs_sub_le r.right s.right)
    _ = norm r + norm s := by simp [norm]; omega

/-- Applying a row costs at most its `ℓ₁` norm times a common input bound. -/
theorem natAbs_apply_le (r : SignedRow) (x y : Int) (bound : Nat)
    (hx : x.natAbs ≤ bound) (hy : y.natAbs ≤ bound) :
    (r.apply x y).natAbs ≤ r.norm * bound := by
  calc
    (r.apply x y).natAbs ≤ (r.left * x).natAbs + (r.right * y).natAbs := by
      simpa [apply] using Int.natAbs_add_le (r.left * x) (r.right * y)
    _ = r.left.natAbs * x.natAbs + r.right.natAbs * y.natAbs := by
      simp only [Int.natAbs_mul]
    _ ≤ r.left.natAbs * bound + r.right.natAbs * bound :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hx) (Nat.mul_le_mul_left _ hy)
    _ = r.norm * bound := by simp [norm, Nat.add_mul]

end SignedRow

/-- The two signed rows returned by a batched inner loop. -/
structure SignedMatrix where
  row0 : SignedRow
  row1 : SignedRow
  deriving DecidableEq, Repr

namespace SignedMatrix

/-- Both matrix rows have `ℓ₁` norm at most `bound`. -/
def Bounded (m : SignedMatrix) (bound : Nat) : Prop :=
  m.row0.norm ≤ bound ∧ m.row1.norm ≤ bound

end SignedMatrix

/-- The pair of signed coefficients attached to the current GCD state. -/
structure CoeffPair where
  first : Int
  second : Int
  deriving DecidableEq, Repr

namespace CoeffPair

/-- Apply both rows of a transition matrix to a coefficient pair. -/
def update (m : SignedMatrix) (c : CoeffPair) : CoeffPair :=
  ⟨m.row0.apply c.first c.second, m.row1.apply c.first c.second⟩

/-- Both signed coefficients have absolute value at most `bound`. -/
def Bounded (c : CoeffPair) (bound : Nat) : Prop :=
  c.first.natAbs ≤ bound ∧ c.second.natAbs ≤ bound

/-- A row-norm bound and a coefficient bound multiply under a matrix update. -/
theorem update_bounded {m : SignedMatrix} {c : CoeffPair} {matrixBound coeffBound : Nat}
    (hm : m.Bounded matrixBound) (hc : c.Bounded coeffBound) :
    (update m c).Bounded (matrixBound * coeffBound) := by
  constructor
  · exact (m.row0.natAbs_apply_le c.first c.second coeffBound hc.1 hc.2).trans
      (Nat.mul_le_mul_right coeffBound hm.1)
  · exact (m.row1.natAbs_apply_le c.first c.second coeffBound hc.1 hc.2).trans
      (Nat.mul_le_mul_right coeffBound hm.2)

end CoeffPair

/-- The three possible row updates performed by one inner-loop operation.

The control path can come from exact low limbs or from the high/low
approximation.  The bound below needs only the selected row operation, not an
assertion that the two control paths coincide. -/
inductive CoeffStep : SignedMatrix → SignedMatrix → Prop
  /-- The halved state was even: keep its row and double the other row. -/
  | even (r0 r1 : SignedRow) :
      CoeffStep ⟨r0, r1⟩ ⟨r0, r1.double⟩
  /-- The first state was the larger odd state: subtract rows and double the
  unchanged state's row. -/
  | subtract (r0 r1 : SignedRow) :
      CoeffStep ⟨r0, r1⟩ ⟨r0.sub r1, r1.double⟩
  /-- The second state was larger: swap while subtracting, and double the old
  first row for the new second state. -/
  | swapSubtract (r0 r1 : SignedRow) :
      CoeffStep ⟨r0, r1⟩ ⟨r1.sub r0, r0.double⟩

namespace CoeffStep

/-- Every possible inner-loop operation increases the maximum row norm by at
most a factor of two. -/
theorem bounded {before after : SignedMatrix} {bound : Nat}
    (hstep : CoeffStep before after) (hbefore : before.Bounded bound) :
    after.Bounded (2 * bound) := by
  cases hstep with
  | even r0 r1 =>
      constructor
      · exact hbefore.1.trans (Nat.le_mul_of_pos_left bound (by omega))
      · simpa [SignedRow.norm_double] using Nat.mul_le_mul_left 2 hbefore.2
  | subtract r0 r1 =>
      constructor
      · exact (SignedRow.norm_sub_le r0 r1).trans (by
          simpa [two_mul] using Nat.add_le_add hbefore.1 hbefore.2)
      · simpa [SignedRow.norm_double] using Nat.mul_le_mul_left 2 hbefore.2
  | swapSubtract r0 r1 =>
      constructor
      · exact (SignedRow.norm_sub_le r1 r0).trans (by
          simpa [two_mul] using Nat.add_le_add hbefore.2 hbefore.1)
      · simpa [SignedRow.norm_double] using Nat.mul_le_mul_left 2 hbefore.1

end CoeffStep

/-- `n` successive inner-loop row operations. -/
inductive CoeffSteps : Nat → SignedMatrix → SignedMatrix → Prop
  | zero (m : SignedMatrix) : CoeffSteps 0 m m
  | succ {n : Nat} {m₀ m₁ m₂ : SignedMatrix} :
      CoeffStep m₀ m₁ → CoeffSteps n m₁ m₂ → CoeffSteps (n + 1) m₀ m₂

namespace CoeffSteps

/-- Iterating the row recurrence for `n` operations gives the trace-independent
bound `2^n`. -/
theorem bounded {n : Nat} {before after : SignedMatrix} {bound : Nat}
    (hsteps : CoeffSteps n before after) (hbefore : before.Bounded bound) :
    after.Bounded (2^n * bound) := by
  induction hsteps generalizing bound with
  | zero m => simpa using hbefore
  | @succ n m₀ m₁ m₂ hstep hsteps ih =>
      have h₁ : m₁.Bounded (2 * bound) := hstep.bounded hbefore
      have h₂ := ih h₁
      simpa [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h₂

end CoeffSteps

/-- Identity rows used at the start of an inner loop. -/
def identityMatrix : SignedMatrix := ⟨⟨1, 0⟩, ⟨0, 1⟩⟩

/-- Any matrix produced by `n` actual inner-loop row operations has row norm at
most `2^n`, regardless of whether its control trace came from the full values or
from the high/low approximation. -/
theorem inner_loop_matrix_bounded {n : Nat} {m : SignedMatrix}
    (hsteps : CoeffSteps n identityMatrix m) : m.Bounded (2^n) := by
  have hid : identityMatrix.Bounded 1 := by simp [identityMatrix, SignedMatrix.Bounded]
  simpa using hsteps.bounded hid

/-- Repeated matrix updates, each with row norm at most `2^batchBits`. -/
inductive Batches (batchBits : Nat) : Nat → CoeffPair → CoeffPair → Prop
  | zero (c : CoeffPair) : Batches batchBits 0 c c
  | succ {n : Nat} {c₀ c₁ c₂ : CoeffPair} (m : SignedMatrix) :
      m.Bounded (2^batchBits) → c₁ = c₀.update m →
      Batches batchBits n c₁ c₂ → Batches batchBits (n + 1) c₀ c₂

namespace Batches

/-- `n` bounded batches multiply the coefficient bound by `2^(n*batchBits)`. -/
theorem bounded {batchBits n : Nat} {start finish : CoeffPair} {bound : Nat}
    (hbatches : Batches batchBits n start finish) (hstart : start.Bounded bound) :
    finish.Bounded (2^(n * batchBits) * bound) := by
  induction hbatches generalizing bound with
  | zero c => simpa using hstart
  | @succ n c₀ c₁ c₂ m hm hc₁ hrest ih =>
      subst c₁
      have hnext : (c₀.update m).Bounded (2^batchBits * bound) :=
        CoeffPair.update_bounded hm hstart
      have hfinish := ih hnext
      simpa [Nat.add_mul, Nat.mul_add, pow_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        using hfinish

end Batches

/-- The initial coefficient pair used by the Rust drivers. -/
def initialCoefficients : CoeffPair := ⟨1, 0⟩

/-- The number of row operations in the approximation-batch prefix. -/
def prefixBits : Nat := 15 * 31

/-- The number of row operations in the complete fixed schedule. -/
def scheduleBits : Nat := prefixBits + 47

/-- The coefficients attached to `a` and `b` after all fifteen 31-operation
approximation batches are bounded by `2^465`.  This theorem uses only row
recurrences of the actual approximation-controlled inner loops. -/
theorem fifteen_batches_coefficients_bounded {c : CoeffPair}
    (h : Batches 31 15 initialCoefficients c) : c.Bounded (2^prefixBits) := by
  have hinit : initialCoefficients.Bounded 1 := by simp [initialCoefficients, CoeffPair.Bounded]
  have hbound : c.Bounded (2^(15 * 31) * 1) := h.bounded hinit
  have hexponent : 15 * 31 = prefixBits := rfl
  rw [hexponent] at hbound
  simpa only [Nat.mul_one] using hbound

/-- Applying a final row with norm at most `2^47` to the result of the fifteen
31-operation batches yields the schedule's `2^512` signed-coefficient bound. -/
theorem full_schedule_coefficient_bound {c : CoeffPair} {finalRow : SignedRow}
    (hbatches : Batches 31 15 initialCoefficients c)
    (hfinal : finalRow.norm ≤ 2^47) :
    (finalRow.apply c.first c.second).natAbs ≤ 2^scheduleBits := by
  have hc := fifteen_batches_coefficients_bounded hbatches
  have happly := finalRow.natAbs_apply_le c.first c.second (2^prefixBits) hc.1 hc.2
  calc
    (finalRow.apply c.first c.second).natAbs ≤ finalRow.norm * 2^prefixBits := happly
    _ ≤ 2^47 * 2^prefixBits := Nat.mul_le_mul_right _ hfinal
    _ = 2^scheduleBits := by rw [scheduleBits, Nat.add_comm, pow_add]

/-- The fixed schedule has exactly 512 row operations. -/
theorem scheduleBits_eq : scheduleBits = 512 := by decide

/-- The prefix has exactly 465 approximation-controlled row operations. -/
theorem prefixBits_eq : prefixBits = 465 := by decide

/-- `2^512` lies strictly inside the signed 576-bit representation, leaving the
ninth word as sign/excess rather than permitting wraparound at bit 575. -/
theorem full_schedule_bound_fits_signed_wide : 2^scheduleBits < 2^575 := by
  apply Nat.pow_lt_pow_right (by omega)
  rw [scheduleBits_eq]
  omega

/-- The integer GCD state manipulated by full-width update blocks. -/
structure GCDState where
  first : Int
  second : Int
  deriving DecidableEq, Repr

/-- Applying the same signed matrix to an integer GCD state. -/
def SignedMatrix.applyState (m : SignedMatrix) (s : GCDState) : GCDState :=
  ⟨m.row0.apply s.first s.second, m.row1.apply s.first s.second⟩

/-- The two exact row equations supplied by a full-width update block.  This is
strictly weaker than saying that the matrix followed exact full-width binary-GCD
control flow. -/
def ScaledTransition (bits : Nat) (m : SignedMatrix) (before after : GCDState) : Prop :=
  (2^bits : Int) * after.first = m.row0.apply before.first before.second ∧
  (2^bits : Int) * after.second = m.row1.apply before.first before.second

/-- Both current states are scaled congruent to their attached coefficients
multiplied by the original input, modulo `modulus`. -/
def CoeffInvariant (modulus input scale : Int) (s : GCDState) (c : CoeffPair) : Prop :=
  modulus ∣ scale * s.first - c.first * input ∧
  modulus ∣ scale * s.second - c.second * input

namespace ScaledTransition

/-- A batched matrix update preserves the coefficient congruence invariant and
multiplies its scale by the batch denominator.  The hypotheses are precisely the
row equations that `update_ab` must establish; no exact-trace hypothesis is
present. -/
theorem preserves_invariant {bits : Nat} {m : SignedMatrix} {before after : GCDState}
    {modulus input scale : Int} {coeff : CoeffPair}
    (htransition : ScaledTransition bits m before after)
    (hinvariant : CoeffInvariant modulus input scale before coeff) :
    CoeffInvariant modulus input (scale * 2^bits) after (coeff.update m) := by
  rcases htransition with ⟨hfirst, hsecond⟩
  rcases hinvariant with ⟨⟨ka, hka⟩, ⟨kb, hkb⟩⟩
  constructor
  · refine ⟨m.row0.left * ka + m.row0.right * kb, ?_⟩
    dsimp [CoeffPair.update]
    unfold SignedRow.apply at hfirst
    calc
      (scale * 2 ^ bits) * after.first -
          (m.row0.left * coeff.first + m.row0.right * coeff.second) * input =
          m.row0.left * (scale * before.first - coeff.first * input) +
          m.row0.right * (scale * before.second - coeff.second * input) := by
            rw [mul_assoc scale, hfirst]
            ring
      _ = m.row0.left * (modulus * ka) + m.row0.right * (modulus * kb) := by
            rw [hka, hkb]
      _ = modulus * (m.row0.left * ka + m.row0.right * kb) := by ring
  · refine ⟨m.row1.left * ka + m.row1.right * kb, ?_⟩
    dsimp [CoeffPair.update]
    unfold SignedRow.apply at hsecond
    calc
      (scale * 2 ^ bits) * after.second -
          (m.row1.left * coeff.first + m.row1.right * coeff.second) * input =
          m.row1.left * (scale * before.first - coeff.first * input) +
          m.row1.right * (scale * before.second - coeff.second * input) := by
            rw [mul_assoc scale, hsecond]
            ring
      _ = m.row1.left * (modulus * ka) + m.row1.right * (modulus * kb) := by
            rw [hka, hkb]
      _ = modulus * (m.row1.left * ka + m.row1.right * kb) := by ring

end ScaledTransition

/-- One exact, unbounded binary-GCD operation of the form used by the final
low-limb loop.  This model is intentionally not used for the preceding high/low
approximation batches. -/
def exactStep (a b : Nat) : Nat × Nat :=
  if Even a then (a / 2, b)
  else if b ≤ a then ((a - b) / 2, b)
  else ((b - a) / 2, a)

/-- One exact step contracts the product after charging one factor of two. -/
theorem exactStep_product (a b : Nat) :
    2 * ((exactStep a b).1 * (exactStep a b).2) ≤ a * b := by
  unfold exactStep
  split_ifs with ha hab
  · have hdiv : 2 * (a / 2) ≤ a := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self a 2
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.mul_le_mul_right b hdiv
  · have hdiv : 2 * ((a - b) / 2) ≤ a - b := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self (a - b) 2
    have hle : 2 * ((a - b) / 2) ≤ a := hdiv.trans (Nat.sub_le a b)
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.mul_le_mul_right b hle
  · have hdiv : 2 * ((b - a) / 2) ≤ b - a := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self (b - a) 2
    have hle : 2 * ((b - a) / 2) ≤ b := hdiv.trans (Nat.sub_le b a)
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.mul_le_mul_right a hle

/-- Iterate only the exact low-limb step. -/
def exactSteps : Nat → Nat × Nat → Nat × Nat
  | 0, state => state
  | n + 1, state => exactSteps n (exactStep state.1 state.2)

/-- After `n` exact low-limb steps, the remaining product charged by `2^n` is
at most the initial product. -/
theorem exactSteps_product (n a b : Nat) :
    2^n * ((exactSteps n (a, b)).1 * (exactSteps n (a, b)).2) ≤ a * b := by
  induction n generalizing a b with
  | zero => simp [exactSteps]
  | succ n ih =>
      have htail := ih (exactStep a b).1 (exactStep a b).2
      have hone := exactStep_product a b
      rw [exactSteps]
      rw [pow_succ]
      calc
        2 ^ n * 2 * ((exactSteps n (exactStep a b)).1 *
            (exactSteps n (exactStep a b)).2) =
            2 * (2 ^ n * ((exactSteps n (exactStep a b)).1 *
              (exactSteps n (exactStep a b)).2)) := by ring
        _ ≤ 2 * ((exactStep a b).1 * (exactStep a b).2) := Nat.mul_le_mul_left 2 htail
        _ ≤ a * b := hone

/-- If the product entering an exact `n`-step tail is below `2^n`, one state is
zero at the end.  For the Rust schedule this is instantiated with `n = 47`; a
separate approximation proof must establish the strict pre-tail product bound. -/
theorem exactSteps_product_eq_zero {n a b : Nat} (hsmall : a * b < 2^n) :
    (exactSteps n (a, b)).1 = 0 ∨ (exactSteps n (a, b)).2 = 0 := by
  have hbound := exactSteps_product n a b
  have hprod : (exactSteps n (a, b)).1 * (exactSteps n (a, b)).2 = 0 := by
    by_contra hne
    have hone : 1 ≤ (exactSteps n (a, b)).1 * (exactSteps n (a, b)).2 :=
      Nat.one_le_iff_ne_zero.mpr hne
    have hpow : 2^n ≤ 2^n * ((exactSteps n (a, b)).1 * (exactSteps n (a, b)).2) := by
      simpa using Nat.mul_le_mul_left (2^n) hone
    omega
  exact Nat.mul_eq_zero.mp hprod

/-- The convergence endpoint needed by the final 47-operation low-limb batch. -/
theorem exactSteps_47_product_eq_zero {a b : Nat} (hsmall : a * b < 2^47) :
    (exactSteps 47 (a, b)).1 = 0 ∨ (exactSteps 47 (a, b)).2 = 0 :=
  exactSteps_product_eq_zero hsmall

end InversionSpec
end PastaAsm
