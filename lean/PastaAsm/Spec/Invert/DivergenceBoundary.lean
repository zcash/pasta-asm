/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.Spec.Invert.RegularPrefix

/-!
# The extremal first-divergence boundary

This module isolates the equality case left by the propagated approximation
error estimate. At the first comparison on which the approximate controls and
the nonnegative full-width quotients disagree, a new first quotient equal to
`-2^(n - 33)` forces the new first approximate control to be zero. The
already-proved zero-control recurrence then identifies every remaining inner
operation as a halving of that first quotient.

The hypotheses below describe the actual Semolina trace. In particular, the
comparison error is not assumed to make the new control zero, and no exact
full-width trace is substituted for the approximation-controlled trace.
-/

namespace PastaAsm.Spec.Invert.Convergence

/-- The operation at `t` is the first comparison whose approximate and actual
orders disagree. Operations strictly before `t` are regular; the odd first
control says that operation `t` takes one of the two comparison branches. -/
def SemolinaFirstIncorrectComparison (a b t : Nat) : Prop :=
  t < 31 ∧ SemolinaRegularPrefix a b t ∧
    ¬ Even (semolinaPrefixApprox a b t).1 ∧
    ¬ ((semolinaPrefixApprox a b t).2 ≤ (semolinaPrefixApprox a b t).1 ↔
      (semolinaPrefixReal a b t).2 ≤ (semolinaPrefixReal a b t).1)

/-- Divide the compiled prefix-numerator error estimate by its exact common
power of two. Thus each actual quotient is within `2^(n - 33)` of its
aligned nonnegative approximate control, at every prefix through operation
31. -/
theorem semolina_prefix_quotient_error_of_odd {a b t : Nat} (hb : Odd b)
    (hlarge : 64 < max (bitLength a) (bitLength b)) (ht : t ≤ 31) :
    let n := max (bitLength a) (bitLength b)
    let control := semolinaPrefixApprox a b t
    let real := semolinaPrefixReal a b t
    (real.1 - (2^(n - 64) : Nat) * control.1).natAbs ≤ 2^(n - 33) ∧
      (real.2 - (2^(n - 64) : Nat) * control.2).natAbs ≤ 2^(n - 33) := by
  let n := max (bitLength a) (bitLength b)
  let ap := semolinaApprox a b
  let s := approxSteps t (ApproxState.initial ap.1 ap.2)
  let control := semolinaPrefixApprox a b t
  let real := semolinaPrefixReal a b t
  have herr := semolina_prefix_error_of_odd (a := a) (b := b) (t := t) hb hlarge
  have hdiv := semolina_prefix_full_width_dvd (a := a) (b := b) (t := t) hb ht
  have hreal0 : real.1 = s.matrix.row0.apply a b / (2^t : Int) := by
    rfl
  have hreal1 : real.2 = s.matrix.row1.apply a b / (2^t : Int) := by
    rfl
  have hrow0 : s.matrix.row0.apply a b = (2^t : Int) * real.1 := by
    rw [hreal0, mul_comm]
    exact (Int.ediv_mul_cancel hdiv.1).symm
  have hrow1 : s.matrix.row1.apply a b = (2^t : Int) * real.2 := by
    rw [hreal1, mul_comm]
    exact (Int.ediv_mul_cancel hdiv.2).symm
  have hcontrol0 : control.1 = s.a := by rfl
  have hcontrol1 : control.2 = s.b := by rfl
  have hscale : n - 64 + t = t + (n - 64) := by omega
  have herrscale : n - 33 + t = t + (n - 33) := by omega
  change
    (s.matrix.row0.apply a b - (2^(n - 64 + t) : Nat) * s.a).natAbs ≤
        2^(n - 33 + t) ∧
      (s.matrix.row1.apply a b - (2^(n - 64 + t) : Nat) * s.b).natAbs ≤
        2^(n - 33 + t) at herr
  have hpowScale : (2^(n - 64 + t) : Int) = (2^t : Int) * 2^(n - 64) := by
    rw [hscale, pow_add]
  have hpowErr : 2^(n - 33 + t) = 2^t * 2^(n - 33) := by
    rw [herrscale, pow_add]
  have hfactor0 :
      s.matrix.row0.apply a b - (2^(n - 64 + t) : Nat) * s.a =
        (2^t : Int) * (real.1 - (2^(n - 64) : Nat) * control.1) := by
    rw [hrow0, ← hcontrol0]
    have hpowScaleCast : ((2^(n - 64 + t) : Nat) : Int) =
        (2^t : Int) * 2^(n - 64) := by
      exact_mod_cast hpowScale
    rw [hpowScaleCast]
    push_cast
    ring
  have hfactor1 :
      s.matrix.row1.apply a b - (2^(n - 64 + t) : Nat) * s.b =
        (2^t : Int) * (real.2 - (2^(n - 64) : Nat) * control.2) := by
    rw [hrow1, ← hcontrol1]
    have hpowScaleCast : ((2^(n - 64 + t) : Nat) : Int) =
        (2^t : Int) * 2^(n - 64) := by
      exact_mod_cast hpowScale
    rw [hpowScaleCast]
    push_cast
    ring
  have herr0 :
      (real.1 - (2^(n - 64) : Nat) * control.1).natAbs ≤ 2^(n - 33) := by
    have h := herr.1
    rw [hfactor0, hpowErr, Int.natAbs_mul] at h
    norm_num at h
    exact h
  have herr1 :
      (real.2 - (2^(n - 64) : Nat) * control.2).natAbs ≤ 2^(n - 33) := by
    have h := herr.2
    rw [hfactor1, hpowErr, Int.natAbs_mul] at h
    norm_num at h
    exact h
  exact ⟨herr0, herr1⟩

/-- A nonnegative approximate control cannot be aligned with the negative
endpoint of its error interval unless that control is zero. This is the exact
arithmetic equality case used at the first divergent comparison. -/
theorem approximate_eq_zero_of_real_eq_neg_error {real : Int} {approx scale err : Nat}
    (hscale : 0 < scale)
    (herr : (real - (scale : Int) * approx).natAbs ≤ err)
    (hboundary : real = -(err : Int)) : approx = 0 := by
  have hlower := (int_bounds_of_natAbs_le herr).1
  rw [hboundary] at hlower
  have hnonneg : (0 : Int) ≤ scale * approx := by positivity
  have hzeroInt : (scale : Int) * approx = 0 := by omega
  have hzeroNat : scale * approx = 0 := by exact_mod_cast hzeroInt
  exact (Nat.mul_eq_zero.mp hzeroNat).resolve_left (Nat.ne_of_gt hscale)

/-- At any concrete Semolina prefix through operation 31, attaining the
negative endpoint `-2^(n - 33)` of the compiled quotient-error interval forces
the corresponding first approximate control to be zero. -/
theorem semolina_prefix_boundary_zero {a b t : Nat}
    (hb : Odd b) (hlarge : 64 < max (bitLength a) (bitLength b)) (ht : t ≤ 31)
    (hboundary : (semolinaPrefixReal a b t).1 =
      -(2^(max (bitLength a) (bitLength b) - 33) : Nat)) :
    (semolinaPrefixApprox a b t).1 = 0 := by
  let n := max (bitLength a) (bitLength b)
  let control := semolinaPrefixApprox a b t
  let real := semolinaPrefixReal a b t
  have herr := semolina_prefix_quotient_error_of_odd (a := a) (b := b) (t := t)
    hb hlarge ht
  change
    (real.1 - (2^(n - 64) : Nat) * control.1).natAbs ≤ 2^(n - 33) ∧
      (real.2 - (2^(n - 64) : Nat) * control.2).natAbs ≤ 2^(n - 33) at herr
  change control.1 = 0
  apply approximate_eq_zero_of_real_eq_neg_error (by positivity) herr.1
  simpa [real, n] using hboundary

/-- At the first incorrect comparison, the extremal negative new first
quotient forces the new first approximate control to be zero. Here `n` is the
actual initial joint maximum bit length, and `n > 64` selects the concrete
non-exact Semolina approximation regime. -/
theorem semolina_firstIncorrectComparison_boundary_zero {a b t : Nat}
    (hb : Odd b) (hlarge : 64 < max (bitLength a) (bitLength b))
    (hfirst : SemolinaFirstIncorrectComparison a b t)
    (hboundary : (semolinaPrefixReal a b (t + 1)).1 =
      -(2^(max (bitLength a) (bitLength b) - 33) : Nat)) :
    (semolinaPrefixApprox a b (t + 1)).1 = 0 := by
  apply semolina_prefix_boundary_zero hb hlarge (by
    unfold SemolinaFirstIncorrectComparison at hfirst
    omega)
  exact hboundary

/-- Concrete zero-control tail after the extremal first-divergence boundary.
The final four equalities are exactly `controlledSteps_zero_approxA`: all
remaining controls select the even branch, the first scaled numerator stays
fixed, and the second acquires the full remaining denominator. -/
theorem semolina_firstIncorrectComparison_boundary_tail {a b t : Nat}
    (hb : Odd b) (hlarge : 64 < max (bitLength a) (bitLength b))
    (hfirst : SemolinaFirstIncorrectComparison a b t)
    (hboundary : (semolinaPrefixReal a b (t + 1)).1 =
      -(2^(max (bitLength a) (bitLength b) - 33) : Nat)) :
    let ap := semolinaApprox a b
    let after := controlledSteps (t + 1) (ControlledState.initial ap.1 ap.2 a b)
    let finish := controlledSteps (31 - (t + 1)) after
    after.approxA = 0 ∧ finish.approxA = 0 ∧ finish.approxB = after.approxB ∧
      finish.scaledRealA = after.scaledRealA ∧
      finish.scaledRealB = (2^(31 - (t + 1)) : Int) * after.scaledRealB := by
  let ap := semolinaApprox a b
  let after := controlledSteps (t + 1) (ControlledState.initial ap.1 ap.2 a b)
  let finish := controlledSteps (31 - (t + 1)) after
  have hzeroApprox := semolina_firstIncorrectComparison_boundary_zero hb hlarge hfirst hboundary
  have hmatches := semolina_controlled_prefix a b (t + 1)
  have hzero : after.approxA = 0 := by
    exact hmatches.1.trans hzeroApprox
  have htail := controlledSteps_zero_approxA (31 - (t + 1)) hzero
  exact ⟨hzero, htail⟩

end PastaAsm.Spec.Invert.Convergence
