/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.Spec.Invert.ConvergenceProgress

/-!
# Regular prefixes of an approximate inversion batch

This module identifies a prefix on which the approximate controls choose the
same comparisons as the nonnegative full-width quotients.  On such a prefix,
the quotient recurrence is exactly the unbounded natural binary-GCD recurrence,
so its existing charged bit-length bound applies.
-/

namespace PastaAsm.Spec.Invert.Convergence

/-- At one Semolina prefix index, both actual quotients are nonnegative and the
approximate and actual states agree on the comparison used by an odd step. -/
def SemolinaRegularAt (a b i : Nat) : Prop :=
  let control := semolinaPrefixApprox a b i
  let real := semolinaPrefixReal a b i
  0 ≤ real.1 ∧ 0 ≤ real.2 ∧
    (control.2 ≤ control.1 ↔ real.2 ≤ real.1)

/-- Every operation strictly before `t` starts in a regular state.  The strict
index makes this directly usable for a first-divergence argument. -/
def SemolinaRegularPrefix (a b t : Nat) : Prop :=
  ∀ i, i < t → SemolinaRegularAt a b i

/-- Exact iteration can equivalently append one exact step on the right. -/
theorem exactSteps_succ_right_regularPrefix (t : Nat) (state : Nat × Nat) :
    exactSteps (t + 1) state =
      exactStep (exactSteps t state).1
        (exactSteps t state).2 := by
  induction t generalizing state with
  | zero => rfl
  | succ t ih =>
      simpa only [exactSteps] using
        ih (exactStep state.1 state.2)

/-- Along a regular prefix of the 31-operation Semolina inner loop, the signed
full-width quotients are precisely the casts of the natural exact iteration. -/
theorem semolinaPrefixReal_eq_exactSteps_of_regularPrefix {a b t : Nat}
    (hb : Odd b) (ht : t ≤ 31) (hregular : SemolinaRegularPrefix a b t) :
    semolinaPrefixReal a b t =
      (((exactSteps t (a, b)).1 : Int),
        ((exactSteps t (a, b)).2 : Int)) := by
  induction t with
  | zero =>
      simp [semolinaPrefixReal, semolinaApprox, approxSteps, ApproxState.initial,
        identityMatrix, SignedRow.apply,
        exactSteps]
  | succ t ih =>
      have htlt : t < 31 := by omega
      have hprefix : SemolinaRegularPrefix a b t := by
        intro i hi
        exact hregular i (by omega)
      have hcurrent := hregular t (Nat.lt_succ_self t)
      have heq := ih (by omega) hprefix
      have hparityInt :
          (semolinaPrefixReal a b t).1 % 2 =
            ((semolinaPrefixApprox a b t).1 : Int) % 2 := by
        simpa [semolinaPrefixReal, semolinaPrefixApprox] using
          (semolina_prefix_quotient_emod_two (a := a) (b := b) (t := t) hb htlt).1
      have hparity :
          (semolinaPrefixApprox a b t).1 % 2 =
            (exactSteps t (a, b)).1 % 2 := by
        rw [heq] at hparityInt
        change ((exactSteps t (a, b)).1 : Int) % 2 =
          ((semolinaPrefixApprox a b t).1 : Int) % 2 at hparityInt
        exact_mod_cast hparityInt.symm
      have horder :
          (semolinaPrefixApprox a b t).2 ≤ (semolinaPrefixApprox a b t).1 ↔
            (exactSteps t (a, b)).2 ≤
              (exactSteps t (a, b)).1 := by
        have horderInt := hcurrent.2.2
        rw [heq] at horderInt
        change (semolinaPrefixApprox a b t).2 ≤ (semolinaPrefixApprox a b t).1 ↔
          ((exactSteps t (a, b)).2 : Int) ≤
            ((exactSteps t (a, b)).1 : Int) at horderInt
        constructor
        · intro h
          exact_mod_cast horderInt.mp h
        · intro h
          apply horderInt.mpr
          exact_mod_cast h
      rw [semolinaPrefixReal_succ hb htlt, heq,
        signedQuotientStep_eq_exactStep hparity horder,
        exactSteps_succ_right_regularPrefix]

/-- A regular prefix either has already terminated or has paid one joint bit of
length for every operation in the prefix. -/
theorem semolinaRegularPrefix_terminal_or_length_progress {a b t : Nat}
    (hb : Odd b) (ht : t ≤ 31) (hregular : SemolinaRegularPrefix a b t) :
    (semolinaPrefixReal a b t).1 = 0 ∨
      signedLengthSum (semolinaPrefixReal a b t).1
          (semolinaPrefixReal a b t).2 + t ≤ lengthSum a b := by
  rw [semolinaPrefixReal_eq_exactSteps_of_regularPrefix hb ht hregular]
  simpa [signedLengthSum, lengthSum] using
    exactSteps_terminal_or_length_progress t hb

/-- A nonterminal regular prefix has paid one joint bit of length for every
operation in the prefix. -/
theorem semolinaRegularPrefix_length_progress {a b t : Nat}
    (hb : Odd b) (ht : t ≤ 31) (hregular : SemolinaRegularPrefix a b t)
    (hne : (semolinaPrefixReal a b t).1 ≠ 0) :
    signedLengthSum (semolinaPrefixReal a b t).1
        (semolinaPrefixReal a b t).2 + t ≤ lengthSum a b := by
  rcases semolinaRegularPrefix_terminal_or_length_progress hb ht hregular with
    hzero | hprogress
  · exact (hne hzero).elim
  · exact hprogress

end PastaAsm.Spec.Invert.Convergence
