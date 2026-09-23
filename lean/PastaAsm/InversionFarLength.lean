/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.InversionRegularPrefix

/-!
# Far-length inputs to a Semolina approximation batch

When the two positive inputs differ in bit length by at least 32, the concrete
31-operation approximation trace stays synchronized with the full-width
quotients.  In the large-first orientation every odd operation is a no-swap
subtraction.  In the symmetric orientation there may first be halvings of the
small first input, followed by one swap; all later odd operations are no-swap.
-/

namespace PastaAsm
namespace InversionConvergence

open InversionSpec

/-- The value pair of the approximation iterator follows `exactSteps` on its
own approximate controls.  This says nothing about the full-width inputs. -/
theorem approxSteps_value_pair (t : Nat) (s : ApproxState) :
    ((approxSteps t s).a, (approxSteps t s).b) = exactSteps t (s.a, s.b) := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
      rw [approxSteps, exactSteps]
      have hstep : ((approxStep s).a, (approxStep s).b) = exactStep s.a s.b := by
        unfold approxStep exactStep
        split_ifs <;> rfl
      calc
        ((approxSteps t (approxStep s)).a, (approxSteps t (approxStep s)).b) =
            exactSteps t ((approxStep s).a, (approxStep s).b) := ih (approxStep s)
        _ = exactSteps t (exactStep s.a s.b) := by rw [hstep]

private theorem semolinaPrefixApprox_eq_exactSteps (a b t : Nat) :
    semolinaPrefixApprox a b t = exactSteps t (semolinaApprox a b) := by
  unfold semolinaPrefixApprox
  simpa [ApproxState.initial] using
    approxSteps_value_pair t (ApproxState.initial (semolinaApprox a b).1
      (semolinaApprox a b).2)

/-- Two natural executions are in the same far-length phase.  The first
alternative is the pre-swap phase; the second is the large-first no-swap phase. -/
def SynchronizedFar (remaining : Nat) (real control : Nat × Nat) : Prop :=
  Odd real.2 ∧ Odd control.2 ∧
    (((2^remaining - 1) * real.1 < real.2 ∧
        (2^remaining - 1) * control.1 < control.2) ∨
      ((2^remaining - 1) * real.2 < real.1 ∧
        (2^remaining - 1) * control.2 < control.1))

/-- The large-first phase of the approximate controls.  While `remaining` is
positive, the strict ratio implies that an odd first control can only take the
no-swap subtraction branch. -/
def LargeFirstFar (remaining : Nat) (control : Nat × Nat) : Prop :=
  Odd control.2 ∧ (2^remaining - 1) * control.2 < control.1

/-- Concrete expansion of Semolina's non-exact approximation branch. -/
private theorem semolinaApprox_eq_of_max_size_gt_64 {a b n : Nat}
    (hn : max (bitLength a) (bitLength b) = n) (hlarge : 64 < n) :
    semolinaApprox a b =
      (a % 2^31 + 2^31 * (a / 2^(n - 33)),
       b % 2^31 + 2^31 * (b / 2^(n - 33))) := by
  unfold semolinaApprox approximate
  simp only [hn]
  rw [if_neg (by omega)]
  norm_num
  have hshift : n - 32 - 1 = n - 33 := by omega
  rw [hshift]
  exact ⟨rfl, rfl⟩

private theorem lt_two_pow_of_bitLength_le {x m : Nat} (h : bitLength x ≤ m) :
    x < 2^m := (lt_two_pow_bitLength x).trans_le
      (Nat.pow_le_pow_right (by omega) h)

private theorem lower_pow_of_bitLength_eq {x n : Nat} (hx : 0 < x)
    (hsize : bitLength x = n) : 2^(n - 1) ≤ x := by
  rw [← hsize]
  exact two_pow_pred_bitLength_le hx

private theorem two_le_two_pow {remaining : Nat} (hremaining : 0 < remaining) :
    2 ≤ 2^remaining := by
  have := Nat.one_lt_two_pow (Nat.ne_of_gt hremaining)
  omega

/-- Initialize the large-first synchronized phase from a 32-bit size gap. -/
private theorem synchronizedFar_of_large_first {a b n : Nat}
    (ha : 0 < a) (hb : 0 < b) (hbodd : Odd b)
    (hmax : max (bitLength a) (bitLength b) = n)
    (hasize : bitLength a = n) (hn : 64 < n)
    (hbsize : bitLength b ≤ n - 32) :
    SynchronizedFar 31 (a, b) (semolinaApprox a b) ∧
      LargeFirstFar 31 (semolinaApprox a b) := by
  have happ := semolinaApprox_eq_of_max_size_gt_64 hmax hn
  have hbPow : b < 2^(n - 32) := lt_two_pow_of_bitLength_le hbsize
  have haPow : 2^(n - 1) ≤ a := lower_pow_of_bitLength_eq ha hasize
  have hexp : 31 + (n - 32) = n - 1 := by omega
  have hrealMul : 2^31 * b < a := by
    calc
      2^31 * b < 2^31 * 2^(n - 32) := Nat.mul_lt_mul_of_pos_left hbPow (by positivity)
      _ = 2^(n - 1) := by rw [← pow_add, hexp]
      _ ≤ a := haPow
  have hreal : (2^31 - 1) * b < a :=
    (Nat.mul_le_mul_right b (Nat.sub_le _ _)).trans_lt hrealMul
  have hbShift : b / 2^(n - 33) ≤ 1 := by
    apply (Nat.div_le_iff_le_mul (by positivity)).mpr
    have hbPowLe : b ≤ 2^(n - 32) - 1 := by
      have := lt_two_pow_of_bitLength_le hbsize
      omega
    have hpow : 2^(n - 32) = 2^(n - 33) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hpow] at hbPowLe
    omega
  have hcontrolSmall : (semolinaApprox a b).2 < 2^32 := by
    rw [happ]
    have hmod := Nat.mod_lt b (by positivity : 0 < 2^31)
    have hmul : 2^31 * (b / 2^(n - 33)) ≤ 2^31 * 1 :=
      Nat.mul_le_mul_left (2^31) hbShift
    norm_num [pow_succ] at *
    omega
  have haDiv : 2^32 ≤ a / 2^(n - 33) := by
    apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    calc
      2^32 * 2^(n - 33) = 2^(n - 1) := by
        rw [← pow_add]
        congr 1
        omega
      _ ≤ a := haPow
  have hcontrolLarge : 2^63 ≤ (semolinaApprox a b).1 := by
    rw [happ]
    calc
      2^63 = 2^31 * 2^32 := by norm_num [← pow_add]
      _ ≤ 2^31 * (a / 2^(n - 33)) := Nat.mul_le_mul_left _ haDiv
      _ ≤ a % 2^31 + 2^31 * (a / 2^(n - 33)) := Nat.le_add_left _ _
  have hcontrol : (2^31 - 1) * (semolinaApprox a b).2 <
      (semolinaApprox a b).1 := by
    calc
      (2^31 - 1) * (semolinaApprox a b).2 < (2^31 - 1) * 2^32 :=
        Nat.mul_lt_mul_of_pos_left hcontrolSmall (by norm_num)
      _ < 2^63 := by norm_num [← pow_add]
      _ ≤ (semolinaApprox a b).1 := hcontrolLarge
  have hcontrolOdd := semolinaApprox_snd_odd (a := a) hbodd
  exact ⟨⟨hbodd, hcontrolOdd, Or.inr ⟨hreal, hcontrol⟩⟩,
    hcontrolOdd, hcontrol⟩

/-- Initialize the small-first phase from the symmetric 32-bit size gap.  The
short loop may halve the first input before its single swap. -/
private theorem synchronizedFar_of_large_second {a b n : Nat}
    (ha : 0 < a) (hb : 0 < b) (hbodd : Odd b)
    (hmax : max (bitLength a) (bitLength b) = n)
    (hbsize : bitLength b = n) (hn : 64 < n)
    (hasize : bitLength a ≤ n - 32) :
    SynchronizedFar 31 (a, b) (semolinaApprox a b) := by
  have happ := semolinaApprox_eq_of_max_size_gt_64 hmax hn
  have haPow : a < 2^(n - 32) := lt_two_pow_of_bitLength_le hasize
  have hbPow : 2^(n - 1) ≤ b := lower_pow_of_bitLength_eq hb hbsize
  have hexp : 31 + (n - 32) = n - 1 := by omega
  have hrealMul : 2^31 * a < b := by
    calc
      2^31 * a < 2^31 * 2^(n - 32) := Nat.mul_lt_mul_of_pos_left haPow (by positivity)
      _ = 2^(n - 1) := by rw [← pow_add, hexp]
      _ ≤ b := hbPow
  have hreal : (2^31 - 1) * a < b :=
    (Nat.mul_le_mul_right a (Nat.sub_le _ _)).trans_lt hrealMul
  have haShift : a / 2^(n - 33) ≤ 1 := by
    apply (Nat.div_le_iff_le_mul (by positivity)).mpr
    have haPowLe : a ≤ 2^(n - 32) - 1 := by
      have := lt_two_pow_of_bitLength_le hasize
      omega
    have hpow : 2^(n - 32) = 2^(n - 33) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hpow] at haPowLe
    omega
  have hcontrolSmall : (semolinaApprox a b).1 < 2^32 := by
    rw [happ]
    have hmod := Nat.mod_lt a (by positivity : 0 < 2^31)
    have hmul : 2^31 * (a / 2^(n - 33)) ≤ 2^31 * 1 :=
      Nat.mul_le_mul_left (2^31) haShift
    norm_num [pow_succ] at *
    omega
  have hbDiv : 2^32 ≤ b / 2^(n - 33) := by
    apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    calc
      2^32 * 2^(n - 33) = 2^(n - 1) := by
        rw [← pow_add]
        congr 1
        omega
      _ ≤ b := hbPow
  have hcontrolLarge : 2^63 ≤ (semolinaApprox a b).2 := by
    rw [happ]
    calc
      2^63 = 2^31 * 2^32 := by norm_num [← pow_add]
      _ ≤ 2^31 * (b / 2^(n - 33)) := Nat.mul_le_mul_left _ hbDiv
      _ ≤ b % 2^31 + 2^31 * (b / 2^(n - 33)) := Nat.le_add_left _ _
  have hcontrol : (2^31 - 1) * (semolinaApprox a b).1 <
      (semolinaApprox a b).2 := by
    calc
      (2^31 - 1) * (semolinaApprox a b).1 < (2^31 - 1) * 2^32 :=
        Nat.mul_lt_mul_of_pos_left hcontrolSmall (by norm_num)
      _ < 2^63 := by norm_num [← pow_add]
      _ ≤ (semolinaApprox a b).2 := hcontrolLarge
  exact ⟨hbodd, semolinaApprox_snd_odd hbodd, Or.inl ⟨hreal, hcontrol⟩⟩

private theorem far_halve_large {remaining large small : Nat}
    (hremaining : 0 < remaining) (heven : Even large)
    (hfar : (2^remaining - 1) * small < large) :
    (2^(remaining - 1) - 1) * small < large / 2 := by
  rcases heven with ⟨q, hq⟩
  have hdiv : large / 2 = q := by rw [hq]; omega
  have hpow : 2^remaining = 2 * 2^(remaining - 1) := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hremaining)
    simp [pow_succ, Nat.mul_comm]
  rw [hpow, hq] at hfar
  rw [hdiv]
  let p := 2^(remaining - 1)
  have hp : 0 < p := by positivity
  have hcoef : 2 * (p - 1) ≤ 2 * p - 1 := by omega
  have hdouble : 2 * ((p - 1) * small) ≤ (2 * p - 1) * small := by
    calc
      2 * ((p - 1) * small) = (2 * (p - 1)) * small := by ring
      _ ≤ (2 * p - 1) * small := Nat.mul_le_mul_right small hcoef
  have htwice : 2 * ((p - 1) * small) < 2 * q := by
    simpa [two_mul] using hdouble.trans_lt hfar
  simpa [p] using Nat.lt_of_mul_lt_mul_left htwice

private theorem far_sub_halve_large {remaining large small : Nat}
    (hremaining : 0 < remaining) (hlargeOdd : Odd large) (hsmallOdd : Odd small)
    (hfar : (2^remaining - 1) * small < large) :
    (2^(remaining - 1) - 1) * small < (large - small) / 2 := by
  have hle : small ≤ large := by
    have hcoef : 1 ≤ 2^remaining - 1 := by
      have := two_le_two_pow hremaining
      omega
    calc
      small = 1 * small := by omega
      _ ≤ (2^remaining - 1) * small := Nat.mul_le_mul_right small hcoef
      _ ≤ large := hfar.le
  have hdiffEven : Even (large - small) := by
    rcases hlargeOdd with ⟨ql, hql⟩
    rcases hsmallOdd with ⟨qs, hqs⟩
    use ql - qs
    omega
  rcases hdiffEven with ⟨q, hq⟩
  have hdiv : (large - small) / 2 = q := by rw [hq]; omega
  have hpow : 2^remaining = 2 * 2^(remaining - 1) := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hremaining)
    simp [pow_succ, Nat.mul_comm]
  rw [hpow] at hfar
  rw [hdiv]
  let p := 2^(remaining - 1)
  have hp : 0 < p := by positivity
  have hcoef : 2 * (p - 1) + 1 = 2 * p - 1 := by omega
  have hsum : 2 * ((p - 1) * small) + small < large := by
    calc
      2 * ((p - 1) * small) + small = (2 * (p - 1) + 1) * small := by ring
      _ = (2 * p - 1) * small := by rw [hcoef]
      _ < large := hfar
  have hsub : 2 * ((p - 1) * small) < large - small := Nat.lt_sub_of_add_lt hsum
  rw [hq] at hsub
  have htwice : 2 * ((p - 1) * small) < 2 * q := by
    simpa [two_mul] using hsub
  simpa [p] using Nat.lt_of_mul_lt_mul_left htwice

private theorem far_halve_small {remaining large small : Nat}
    (hfar : (2^remaining - 1) * small < large) :
    (2^(remaining - 1) - 1) * (small / 2) < large := by
  have hpow : 2^(remaining - 1) ≤ 2^remaining :=
    Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
  have hsmall : small / 2 ≤ small := Nat.div_le_self _ _
  calc
    (2^(remaining - 1) - 1) * (small / 2) ≤
        (2^remaining - 1) * small :=
      Nat.mul_le_mul (Nat.sub_le_sub_right hpow 1) hsmall
    _ < large := hfar

private theorem largeFirstFar_step {remaining : Nat} {control : Nat × Nat}
    (hremaining : 0 < remaining) (h : LargeFirstFar remaining control) :
    LargeFirstFar (remaining - 1) (exactStep control.1 control.2) := by
  rcases h with ⟨hsecondOdd, hfar⟩
  have hcoef : 1 ≤ 2^remaining - 1 := by
    have := two_le_two_pow hremaining
    omega
  have horder : control.2 ≤ control.1 :=
    (show control.2 ≤ (2^remaining - 1) * control.2 by
      simpa only [one_mul] using Nat.mul_le_mul_right control.2 hcoef).trans hfar.le
  refine ⟨exactStep_second_odd_progress hsecondOdd, ?_⟩
  by_cases hfirstEven : Even control.1
  · unfold exactStep
    rw [if_pos hfirstEven]
    exact far_halve_large hremaining hfirstEven hfar
  · unfold exactStep
    rw [if_neg hfirstEven, if_pos horder]
    exact far_sub_halve_large hremaining (Nat.not_even_iff_odd.mp hfirstEven)
      hsecondOdd hfar

private theorem synchronizedFar_order {remaining : Nat} {real control : Nat × Nat}
    (hremaining : 0 < remaining) (h : SynchronizedFar remaining real control) :
    (control.2 ≤ control.1 ↔ real.2 ≤ real.1) := by
  rcases h with ⟨_, _, hpre | hpost⟩
  · have hcoef : 1 ≤ 2^remaining - 1 := by
      have := two_le_two_pow hremaining
      omega
    have hr : real.1 < real.2 :=
      (show real.1 ≤ (2^remaining - 1) * real.1 by
        simpa only [one_mul] using Nat.mul_le_mul_right real.1 hcoef).trans_lt hpre.1
    have hc : control.1 < control.2 :=
      (show control.1 ≤ (2^remaining - 1) * control.1 by
        simpa only [one_mul] using Nat.mul_le_mul_right control.1 hcoef).trans_lt hpre.2
    omega
  · have hcoef : 1 ≤ 2^remaining - 1 := by
      have := two_le_two_pow hremaining
      omega
    have hr : real.2 < real.1 :=
      (show real.2 ≤ (2^remaining - 1) * real.2 by
        simpa only [one_mul] using Nat.mul_le_mul_right real.2 hcoef).trans_lt hpost.1
    have hc : control.2 < control.1 :=
      (show control.2 ≤ (2^remaining - 1) * control.2 by
        simpa only [one_mul] using Nat.mul_le_mul_right control.2 hcoef).trans_lt hpost.2
    omega

private theorem synchronizedFar_step {remaining : Nat} {real control : Nat × Nat}
    (hremaining : 0 < remaining) (hparity : real.1 % 2 = control.1 % 2)
    (h : SynchronizedFar remaining real control) :
    SynchronizedFar (remaining - 1) (exactStep real.1 real.2)
      (exactStep control.1 control.2) := by
  rcases h with ⟨hrealOdd, hcontrolOdd, hpre | hpost⟩
  · have heven : Even real.1 ↔ Even control.1 := by
      rw [Nat.even_iff, Nat.even_iff]
      omega
    refine ⟨exactStep_second_odd_progress hrealOdd,
      exactStep_second_odd_progress hcontrolOdd, ?_⟩
    have hcoef : 1 ≤ 2^remaining - 1 := by
      have := two_le_two_pow hremaining
      omega
    have hrealLt : real.1 < real.2 :=
      (show real.1 ≤ (2^remaining - 1) * real.1 by
        simpa only [one_mul] using Nat.mul_le_mul_right real.1 hcoef).trans_lt hpre.1
    have hcontrolLt : control.1 < control.2 :=
      (show control.1 ≤ (2^remaining - 1) * control.1 by
        simpa only [one_mul] using Nat.mul_le_mul_right control.1 hcoef).trans_lt hpre.2
    by_cases hrealEven : Even real.1
    · have hcontrolEven : Even control.1 := heven.mp hrealEven
      unfold exactStep
      rw [if_pos hrealEven, if_pos hcontrolEven]
      exact Or.inl ⟨far_halve_small hpre.1, far_halve_small hpre.2⟩
    · have hcontrolEven : ¬ Even control.1 := fun hc => hrealEven (heven.mpr hc)
      unfold exactStep
      rw [if_neg hrealEven, if_neg hcontrolEven,
        if_neg (Nat.not_le_of_gt hrealLt), if_neg (Nat.not_le_of_gt hcontrolLt)]
      exact Or.inr ⟨
        far_sub_halve_large (large := real.2) (small := real.1) hremaining hrealOdd
          (Nat.not_even_iff_odd.mp hrealEven) hpre.1,
        far_sub_halve_large (large := control.2) (small := control.1) hremaining hcontrolOdd
          (Nat.not_even_iff_odd.mp hcontrolEven) hpre.2⟩
  · have heven : Even real.1 ↔ Even control.1 := by
      rw [Nat.even_iff, Nat.even_iff]
      omega
    refine ⟨exactStep_second_odd_progress hrealOdd,
      exactStep_second_odd_progress hcontrolOdd, ?_⟩
    have hcoef : 1 ≤ 2^remaining - 1 := by
      have := two_le_two_pow hremaining
      omega
    have hrealOrder : real.2 ≤ real.1 :=
      (show real.2 ≤ (2^remaining - 1) * real.2 by
        simpa only [one_mul] using Nat.mul_le_mul_right real.2 hcoef).trans hpost.1.le
    have hcontrolOrder : control.2 ≤ control.1 :=
      (show control.2 ≤ (2^remaining - 1) * control.2 by
        simpa only [one_mul] using Nat.mul_le_mul_right control.2 hcoef).trans hpost.2.le
    by_cases hrealEven : Even real.1
    · have hcontrolEven : Even control.1 := heven.mp hrealEven
      unfold exactStep
      rw [if_pos hrealEven, if_pos hcontrolEven]
      exact Or.inr ⟨far_halve_large hremaining hrealEven hpost.1,
        far_halve_large hremaining hcontrolEven hpost.2⟩
    · have hcontrolEven : ¬ Even control.1 := fun hc => hrealEven (heven.mpr hc)
      unfold exactStep
      rw [if_neg hrealEven, if_neg hcontrolEven, if_pos hrealOrder, if_pos hcontrolOrder]
      exact Or.inr ⟨far_sub_halve_large hremaining
          (Nat.not_even_iff_odd.mp hrealEven) hrealOdd hpost.1,
        far_sub_halve_large hremaining
          (Nat.not_even_iff_odd.mp hcontrolEven) hcontrolOdd hpost.2⟩

/-- An initial far phase persists jointly through the concrete Semolina prefix,
and the actual signed quotients stay equal to the natural exact real state.
The parity premise at each step comes from the actual row quotient congruence. -/
private theorem synchronizedFar_prefix {a b : Nat} (hb : Odd b)
    (hinitial : SynchronizedFar 31 (a, b) (semolinaApprox a b)) :
    ∀ i, i ≤ 31 →
      SynchronizedFar (31 - i) (exactSteps i (a, b))
          (exactSteps i (semolinaApprox a b)) ∧
        semolinaPrefixReal a b i =
          (((exactSteps i (a, b)).1 : Int), ((exactSteps i (a, b)).2 : Int)) := by
  intro i hi
  induction i with
  | zero =>
      refine ⟨by simpa [exactSteps] using hinitial, ?_⟩
      simp [semolinaPrefixReal, semolinaApprox, approxSteps, ApproxState.initial,
        identityMatrix, SignedRow.apply, exactSteps]
  | succ i ih =>
      have hilt : i < 31 := by omega
      rcases ih (by omega) with ⟨hcurrent, hrealEq⟩
      have hcontrolEq := semolinaPrefixApprox_eq_exactSteps a b i
      have hparityInt : (semolinaPrefixReal a b i).1 % 2 =
          ((semolinaPrefixApprox a b i).1 : Int) % 2 := by
        simpa [semolinaPrefixReal, semolinaPrefixApprox] using
          (semolina_prefix_quotient_emod_two (a := a) (b := b) (t := i) hb hilt).1
      have hparity : (exactSteps i (a, b)).1 % 2 =
          (exactSteps i (semolinaApprox a b)).1 % 2 := by
        rw [hrealEq, hcontrolEq] at hparityInt
        change ((exactSteps i (a, b)).1 : Int) % 2 =
          ((exactSteps i (semolinaApprox a b)).1 : Int) % 2 at hparityInt
        exact_mod_cast hparityInt
      have hnext := synchronizedFar_step (by omega) hparity hcurrent
      have horder := synchronizedFar_order (by omega) hcurrent
      have hstep : signedQuotientStep (semolinaPrefixApprox a b i)
            (semolinaPrefixReal a b i) =
          (((exactStep (exactSteps i (a, b)).1 (exactSteps i (a, b)).2).1 : Int),
            ((exactStep (exactSteps i (a, b)).1 (exactSteps i (a, b)).2).2 : Int)) := by
        rw [hcontrolEq, hrealEq]
        exact signedQuotientStep_eq_exactStep hparity.symm horder
      have hremaining : 31 - (i + 1) = 31 - i - 1 := by omega
      have hrealNext := exactSteps_succ_right_regularPrefix i (a, b)
      have hcontrolNext := exactSteps_succ_right_regularPrefix i (semolinaApprox a b)
      constructor
      · rw [hremaining, hrealNext, hcontrolNext]
        exact hnext
      · rw [semolinaPrefixReal_succ hb hilt, hstep, hrealNext]

/-- In the concrete large-first orientation, the actual approximation controls
remain in the no-swap phase through all 31 prefix states. -/
theorem semolinaFar_large_first_control_prefix {a b n : Nat}
    (ha : 0 < a) (hb : 0 < b) (hbodd : Odd b)
    (hmax : max (bitLength a) (bitLength b) = n)
    (hasize : bitLength a = n) (hn : 64 < n)
    (hbsize : bitLength b ≤ n - 32) :
    ∀ i, i ≤ 31 → LargeFirstFar (31 - i) (semolinaPrefixApprox a b i) := by
  have hinitial :=
    (synchronizedFar_of_large_first ha hb hbodd hmax hasize hn hbsize).2
  intro i hi
  rw [semolinaPrefixApprox_eq_exactSteps]
  induction i with
  | zero => simpa [exactSteps] using hinitial
  | succ i ih =>
      have hcurrent := ih (by omega)
      rw [exactSteps_succ_right_regularPrefix]
      have hstep := largeFirstFar_step (remaining := 31 - i) (by omega) hcurrent
      simpa only [Nat.sub_sub] using hstep

/-- Before each of the 31 operations in the concrete large-first orientation,
the actual approximation controls order the second component below the first.
Consequently every odd operation uses subtraction without a swap; even first
controls use the halving branch, and termination (`control.1 = 0`) is included
in that even case. -/
theorem semolinaFar_large_first_control_no_swap {a b n i : Nat}
    (ha : 0 < a) (hb : 0 < b) (hbodd : Odd b)
    (hmax : max (bitLength a) (bitLength b) = n)
    (hasize : bitLength a = n) (hn : 64 < n)
    (hbsize : bitLength b ≤ n - 32) (hi : i < 31) :
    (semolinaPrefixApprox a b i).2 ≤ (semolinaPrefixApprox a b i).1 := by
  have hfar := semolinaFar_large_first_control_prefix ha hb hbodd hmax hasize hn hbsize
    i hi.le
  rcases hfar with ⟨_, hratio⟩
  have hcoef : 1 ≤ 2^(31 - i) - 1 := by
    have := two_le_two_pow (show 0 < 31 - i by omega)
    omega
  exact
    (show (semolinaPrefixApprox a b i).2 ≤
        (2^(31 - i) - 1) * (semolinaPrefixApprox a b i).2 by
      simpa only [one_mul] using
        Nat.mul_le_mul_right (semolinaPrefixApprox a b i).2 hcoef).trans hratio.le

/-- The synchronized far invariant establishes regularity at every concrete
Semolina prefix index. -/
theorem semolinaRegularPrefix_of_synchronizedFar {a b : Nat} (hb : Odd b)
    (hinitial : SynchronizedFar 31 (a, b) (semolinaApprox a b)) :
    SemolinaRegularPrefix a b 31 := by
  intro i hi
  rcases synchronizedFar_prefix hb hinitial i hi.le with ⟨hinv, hreal⟩
  have horder := synchronizedFar_order (by omega) hinv
  have hcontrol := semolinaPrefixApprox_eq_exactSteps a b i
  unfold SemolinaRegularAt
  rw [hreal, hcontrol]
  refine ⟨by positivity, by positivity, ?_⟩
  have horderInt :
      ((exactSteps i (semolinaApprox a b)).2 : Int) ≤
          (exactSteps i (semolinaApprox a b)).1 ↔
        ((exactSteps i (a, b)).2 : Int) ≤ (exactSteps i (a, b)).1 := by
    exact_mod_cast horder
  simpa using horderInt

/-- The concrete large-first size gap makes all 31 actual Semolina operations
a regular prefix.  In particular, the control-order part is witnessed by
`semolinaFar_large_first_control_no_swap`, rather than supplied as a hypothesis. -/
theorem semolinaFar_large_first_regularPrefix {a b n : Nat}
    (ha : 0 < a) (hb : 0 < b) (hbodd : Odd b)
    (hmax : max (bitLength a) (bitLength b) = n)
    (hasize : bitLength a = n) (hn : 64 < n)
    (hbsize : bitLength b ≤ n - 32) :
    SemolinaRegularPrefix a b 31 := by
  exact semolinaRegularPrefix_of_synchronizedFar hbodd
    (synchronizedFar_of_large_first ha hb hbodd hmax hasize hn hbsize).1

/-- Generic far-phase endpoint: once both the full-width inputs and their actual
Semolina controls satisfy the indexed far condition, the complete 31-operation
batch either terminates or pays all 31 bits of joint absolute quotient length. -/
theorem semolinaFar_terminal_or_length_progress_of_synchronized {a b : Nat}
    (hb : Odd b) (hinitial : SynchronizedFar 31 (a, b) (semolinaApprox a b)) :
    (semolinaQuotients a b).1 = 0 ∨
      signedLengthSum (semolinaQuotients a b).1 (semolinaQuotients a b).2 + 31 ≤
        lengthSum a b := by
  have hregular := semolinaRegularPrefix_of_synchronizedFar hb hinitial
  have hprogress := semolinaRegularPrefix_terminal_or_length_progress hb (by omega) hregular
  simpa [semolinaPrefixReal, semolinaQuotients, semolinaNumerators, semolinaShort] using hprogress

/-- Concrete far-length result when the first input has the maximum bit length. -/
theorem semolinaFar_large_first_terminal_or_length_progress {a b n : Nat}
    (ha : 0 < a) (hb : 0 < b) (hbodd : Odd b)
    (hmax : max (bitLength a) (bitLength b) = n)
    (hasize : bitLength a = n) (hn : 64 < n)
    (hbsize : bitLength b ≤ n - 32) :
    (semolinaQuotients a b).1 = 0 ∨
      signedLengthSum (semolinaQuotients a b).1 (semolinaQuotients a b).2 + 31 ≤
        lengthSum a b := by
  have hregular := semolinaFar_large_first_regularPrefix ha hb hbodd hmax hasize hn hbsize
  have hprogress := semolinaRegularPrefix_terminal_or_length_progress hbodd (by omega) hregular
  simpa [semolinaPrefixReal, semolinaQuotients, semolinaNumerators, semolinaShort] using hprogress

/-- The requested bounded large-first milestone under its minimal input
hypotheses: every one of the first 31 actual approximation controls is ordered
for the no-swap branch, and the existing regular-prefix theorem yields either
termination or the full 31-bit joint-length contraction. -/
theorem semolinaFar_large_first_no_swap_and_length_progress {a b n : Nat}
    (ha : 0 < a) (hbodd : Odd b) (hasize : bitLength a = n) (hn : 64 < n)
    (hbsize : bitLength b ≤ n - 32) :
    (∀ i, i < 31 →
        (semolinaPrefixApprox a b i).2 ≤ (semolinaPrefixApprox a b i).1) ∧
      ((semolinaQuotients a b).1 = 0 ∨
        signedLengthSum (semolinaQuotients a b).1 (semolinaQuotients a b).2 + 31 ≤
          lengthSum a b) := by
  have hb : 0 < b := Odd.pos hbodd
  have hbLt : bitLength b < n := by omega
  have hmax : max (bitLength a) (bitLength b) = n := by omega
  constructor
  · intro i hi
    exact semolinaFar_large_first_control_no_swap ha hb hbodd hmax hasize hn hbsize hi
  · exact semolinaFar_large_first_terminal_or_length_progress ha hb hbodd hmax hasize hn hbsize

/-- Concrete far-length result when the second input has the maximum bit length.
This is the orientation that may perform initial halvings before its one swap. -/
theorem semolinaFar_large_second_terminal_or_length_progress {a b n : Nat}
    (ha : 0 < a) (hb : 0 < b) (hbodd : Odd b)
    (hmax : max (bitLength a) (bitLength b) = n)
    (hbsize : bitLength b = n) (hn : 64 < n)
    (hasize : bitLength a ≤ n - 32) :
    (semolinaQuotients a b).1 = 0 ∨
      signedLengthSum (semolinaQuotients a b).1 (semolinaQuotients a b).2 + 31 ≤
        lengthSum a b := by
  exact semolinaFar_terminal_or_length_progress_of_synchronized hbodd
    (synchronizedFar_of_large_second ha hb hbodd hmax hbsize hn hasize)

/-- Concrete 31-operation Semolina far-initial-length theorem.  For positive
inputs with odd second input, maximum bit length `n > 64`, and a gap of at least
32 bits, the actual approximation-controlled signed quotients either terminate
or pay all 31 charged bits of initial joint length. -/
theorem semolinaFar_terminal_or_length_progress {a b n : Nat}
    (ha : 0 < a) (hb : 0 < b) (hbodd : Odd b)
    (hmax : max (bitLength a) (bitLength b) = n) (hn : 64 < n)
    (hfar : (bitLength a = n ∧ bitLength b ≤ n - 32) ∨
      (bitLength b = n ∧ bitLength a ≤ n - 32)) :
    (semolinaQuotients a b).1 = 0 ∨
      signedLengthSum (semolinaQuotients a b).1 (semolinaQuotients a b).2 + 31 ≤
        lengthSum a b := by
  rcases hfar with hfirst | hsecond
  · exact semolinaFar_large_first_terminal_or_length_progress ha hb hbodd hmax
      hfirst.1 hn hfirst.2
  · exact semolinaFar_large_second_terminal_or_length_progress ha hb hbodd hmax
      hsecond.1 hn hsecond.2

end InversionConvergence
end PastaAsm
