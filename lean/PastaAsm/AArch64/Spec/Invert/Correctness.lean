/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.AArch64.Spec.Add
import PastaAsm.AArch64.Spec.Mul
import PastaAsm.AArch64.Spec.Invert.Divsteps.Steps47
import PastaAsm.AArch64.Spec.Invert.Multiply
import PastaAsm.AArch64.Spec.Invert.Normalize
import PastaAsm.AArch64.Spec.Invert.Update
import PastaAsm.Fields.Inversion
import PastaAsm.Spec.Invert.Schedule

/-!
# Concrete arithmetic correspondence for AArch64 inversion

This module connects one concrete AArch64 inversion batch to the shared signed
coefficient model. Long-schedule iteration remains in the architecture-independent
schedule module, so its induction never unfolds the generated approximation computation.
-/

namespace PastaAsm.AArch64

open Spec.Invert Spec.Invert.Convergence Spec.Invert.Normalize Spec.Invert.Schedule

set_option exponentiation.threshold 600
set_option maxRecDepth 2000

/-- The concrete 31-step helper returns register-sized coefficient bitpatterns. -/
private theorem divsteps31_words_bounded (a b : Limbs) :
    let matrix := divsteps31 a b
    matrix.f0 < 2^64 ∧ matrix.g0 < 2^64 ∧ matrix.f1 < 2^64 ∧ matrix.g1 < 2^64 := by
  dsimp only
  unfold divsteps31
  simp only
  exact ⟨sub_lt _ _, sub_lt _ _, sub_lt _ _, sub_lt _ _⟩

/-- The concrete full-width update returns register-sized row bitpatterns. -/
private theorem updateAB_words_bounded (a b : Limbs) (f g : Nat) :
    let out := updateAB a b f g
    out.f < 2^64 ∧ out.g < 2^64 := by
  dsimp only
  unfold updateAB
  simp only
  exact ⟨sub_lt _ _, sub_lt _ _⟩

/-- One final-divsteps round returns register-sized second-row bitpatterns. -/
private theorem divsteps47Round_words_bounded (state : Divsteps47State) :
    (divsteps47Round state).f1 < 2^64 ∧ (divsteps47Round state).g1 < 2^64 := by
  unfold divsteps47Round
  simp only
  exact ⟨add_lt _ _, add_lt _ _⟩

/-- The concrete final helper returns register-sized row bitpatterns. -/
theorem divsteps47_words_bounded (a b : Nat) :
    let row := divsteps47 a b
    row.f1 < 2^64 ∧ row.g1 < 2^64 := by
  dsimp only
  unfold divsteps47
  simp only
  exact divsteps47Round_words_bounded _

/-- Small bundle of final-row facts, used to prevent repeated elaboration of matrix projections. -/
structure FinalRowFacts (row : InvertRow) (matrix : SignedMatrix) : Prop where
  fBound : row.f1 < 2^64
  gBound : row.g1 < 2^64
  fRep : WordRep row.f1 matrix.row1.left
  gRep : WordRep row.g1 matrix.row1.right
  rowBound : matrix.row1.norm ≤ 2^47

/-- The final helper exposes exactly the second-row facts consumed by the schedule proof. -/
theorem divsteps47_row_spec (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) (hodd : Odd b) :
    let row := divsteps47 a b
    let final := approxSteps 47 (ApproxState.initial a b)
    FinalRowFacts row final.matrix ∧ Odd final.b := by
  dsimp only
  obtain ⟨hf, hg, hfinalOdd, hmatrixBound, _⟩ :=
    divsteps47_spec a b ha hb hodd (divsteps47 a b) rfl
  exact ⟨⟨(divsteps47_words_bounded a b).1, (divsteps47_words_bounded a b).2,
    hf, hg, hmatrixBound.2⟩, hfinalOdd⟩

/-- A bounded nine-word bitpattern represents an integer modulo its wrapping width. -/
def WideCoeffRep (words : PastaAsm.WideLimbs) (coefficient : Int) : Prop :=
  words.Bounded ∧ (coefficientModulus : Int) ∣ (words.toNat : Int) - coefficient

@[simp] theorem wideCoeffRep_one :
    WideCoeffRep ⟨1, 0, 0, 0, 0, 0, 0, 0, 0⟩ 1 := by
  constructor
  · simp [PastaAsm.WideLimbs.Bounded, regMod]
  · simp [PastaAsm.WideLimbs.toNat]

@[simp] theorem wideCoeffRep_zero :
    WideCoeffRep ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩ 0 := by
  constructor
  · simp [PastaAsm.WideLimbs.Bounded, regMod]
  · simp [PastaAsm.WideLimbs.toNat]

private theorem mulSigned_signed_modEq
    (value : PastaAsm.WideLimbs) (scalar : Nat) (x : Int)
    (hv : value.Bounded) (hscalarBound : scalar < 2^64) (hscalar : WordRep scalar x)
    (hx : x.natAbs < 2^63) :
    (mulSigned value scalar).Bounded ∧
      (mulSigned value scalar).toNat ≡ (value.toNat : Int) * x
        [ZMOD coefficientModulus] := by
  obtain ⟨hout, hcases⟩ := mulSigned_spec value scalar hv hscalarBound _ rfl
  refine ⟨hout, ?_⟩
  rw [WordRep, Int.modEq_iff_dvd] at hscalar
  rcases hscalar with ⟨k, hk⟩
  let j := -k
  have hk' : x - (scalar : Int) = (2^64 : Int) * k := by
    norm_num only at hk ⊢
    exact hk
  have hj : (scalar : Int) - x = (2^64 : Int) * j := by
    dsimp only [j]
    rw [show (scalar : Int) - x = -(x - scalar) by ring, hk']
    ring
  rcases hcases with ⟨hsmall, hmod⟩ | ⟨hlarge, hmod⟩
  · have hjzero : j = 0 := by
      have hscalarInt : (scalar : Int) < 2^63 := by exact_mod_cast hsmall
      have hxlower : -(2^63 : Int) < x := by
        have habs : (x.natAbs : Int) < 2^63 := by exact_mod_cast hx
        omega
      norm_num only at hj
      omega
    have hxeq : x = scalar := by
      norm_num only at hj
      rw [hjzero] at hj
      omega
    simpa only [hxeq, Int.natCast_mul] using Int.natCast_modEq_iff.mpr hmod
  · have hjone : j = 1 := by
      have hscalarInt : (2^63 : Int) ≤ scalar := by exact_mod_cast hlarge
      have hxupper : x < (2^63 : Int) := by
        have habs : (x.natAbs : Int) < 2^63 := by exact_mod_cast hx
        omega
      norm_num only at hj
      omega
    have hxeq : x = (scalar : Int) - 2^64 := by
      norm_num only at hj
      rw [hjone] at hj
      omega
    have hcast := Int.natCast_modEq_iff.mpr hmod
    have hsubCast : ((2^64 - scalar : Nat) : Int) = (2^64 : Int) - scalar := by
      rw [Int.natCast_sub hscalarBound.le]
      norm_num
    push_cast at hcast
    have hsubCast' : ((18446744073709551616 - scalar : Nat) : Int) =
        (18446744073709551616 : Int) - scalar := by
      simpa only [show (18446744073709551616 : Nat) = 2^64 by norm_num] using hsubCast
    rw [hsubCast'] at hcast
    rw [Int.modEq_iff_dvd] at hcast ⊢
    convert hcast using 1
    all_goals (rw [hxeq]; ring)

/-- The concrete nine-word linear combination applies a represented signed row. -/
theorem invertLincomb_rep
    (u v : PastaAsm.WideLimbs) (f g : Nat) (x y left right : Int)
    (hu : WideCoeffRep u x) (hv : WideCoeffRep v y)
    (hfBound : f < 2^64) (hgBound : g < 2^64)
    (hf : WordRep f left) (hg : WordRep g right)
    (hleft : left.natAbs < 2^63) (hright : right.natAbs < 2^63) :
    WideCoeffRep (invertLincomb u v f g) (left * x + right * y) := by
  obtain ⟨huf, hufMod⟩ := mulSigned_signed_modEq u f left hu.1 hfBound hf hleft
  obtain ⟨hvg, hvgMod⟩ := mulSigned_signed_modEq v g right hv.1 hgBound hg hright
  obtain ⟨hout, _, _, _⟩ := addWords_spec (mulSigned u f) (mulSigned v g) huf hvg _ rfl
  refine ⟨hout, ?_⟩
  have hadd := Int.natCast_modEq_iff.mpr
    (addWords_modEq (mulSigned u f) (mulSigned v g) huf hvg)
  have huMod : (u.toNat : Int) ≡ x [ZMOD coefficientModulus] := by
    exact (Int.modEq_iff_dvd.mpr hu.2).symm
  have hvMod : (v.toNat : Int) ≡ y [ZMOD coefficientModulus] := by
    exact (Int.modEq_iff_dvd.mpr hv.2).symm
  have hresult : ((invertLincomb u v f g).toNat : Int) ≡
      left * x + right * y [ZMOD coefficientModulus] := by
    calc
      ((invertLincomb u v f g).toNat : Int) ≡
          ((mulSigned u f).toNat : Int) + ((mulSigned v g).toNat : Int)
          [ZMOD coefficientModulus] := by simpa [invertLincomb] using hadd
      _ ≡ (u.toNat : Int) * left + (v.toNat : Int) * right
          [ZMOD coefficientModulus] := hufMod.add hvgMod
      _ ≡ x * left + y * right [ZMOD coefficientModulus] :=
        (huMod.mul_right left).add (hvMod.mul_right right)
      _ = left * x + right * y := by ring
  exact Int.modEq_iff_dvd.mp hresult.symm

/-- A represented coefficient in the signed 576-bit interval decodes exactly. -/
theorem WideCoeffRep.toInt_eq {words : PastaAsm.WideLimbs} {coefficient : Int}
    (hrep : WideCoeffRep words coefficient) (hcoeff : coefficient.natAbs < 2^575) :
    words.toInt = coefficient := by
  have hnatLt : words.toNat < 2^576 := by
    unfold PastaAsm.WideLimbs.toNat
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hrep.1
    simp only [regMod] at h0 h1 h2 h3 h4 h5 h6 h7 h8
    omega
  have hmod : (coefficientModulus : Int) ∣ words.toInt - coefficient := by
    unfold PastaAsm.WideLimbs.toInt
    split_ifs with hsign
    · exact hrep.2
    · obtain ⟨k, hk⟩ := hrep.2
      refine ⟨k - 1, ?_⟩
      simp only [coefficientModulus] at hk ⊢
      omega
  have hwordsLower : -(2^575 : Int) ≤ words.toInt := by
    unfold PastaAsm.WideLimbs.toInt
    split_ifs with hsign
    · have hnonneg : (0 : Int) ≤ words.toNat := by positivity
      omega
    · have hnatGe : 2^575 ≤ words.toNat := by
        unfold PastaAsm.WideLimbs.toNat
        have htop : 2^63 ≤ words.l8 := by omega
        omega
      have hnatGeInt : (2^575 : Int) ≤ words.toNat := by exact_mod_cast hnatGe
      omega
  have hwordsUpper : words.toInt < (2^575 : Int) := by
    unfold PastaAsm.WideLimbs.toInt
    split_ifs with hsign
    · have htop : words.toNat < 2^575 := by
        unfold PastaAsm.WideLimbs.toNat
        obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hrep.1
        simp only [regMod] at h0 h1 h2 h3 h4 h5 h6 h7 h8
        omega
      exact_mod_cast htop
    · have hnatLtInt : (words.toNat : Int) < 2^576 := by exact_mod_cast hnatLt
      omega
  have hcoeffLower : -(2^575 : Int) < coefficient := by
    have habs : (coefficient.natAbs : Int) < 2^575 := by exact_mod_cast hcoeff
    omega
  have hcoeffUpper : coefficient < (2^575 : Int) := by
    have habs : (coefficient.natAbs : Int) < 2^575 := by exact_mod_cast hcoeff
    omega
  have hdiffAbs : (words.toInt - coefficient).natAbs < 2^576 := by
    apply natAbs_lt_of_int_bounds
    · norm_num only
      omega
    · norm_num only
      omega
  apply Int.eq_of_sub_eq_zero
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hmod
  simpa only [coefficientModulus, Int.natAbs_natCast] using hdiffAbs

private theorem orient_ediv_eq_of_dvd {x : Int} {d : Nat}
    (hd : 0 < d) (hdiv : (d : Int) ∣ x) :
    orient (x / (d : Int)) = orient x := by
  rcases hdiv with ⟨q, rfl⟩
  rw [Int.mul_ediv_cancel_left q (by exact_mod_cast Nat.ne_of_gt hd)]
  have hdInt : (0 : Int) < d := by exact_mod_cast hd
  have hsign : (d : Int) * q < 0 ↔ q < 0 := by
    rw [mul_neg_iff]
    omega
  unfold orient
  rw [if_congr hsign rfl rfl]

private theorem row_entry_lt_signed_word {row : SignedRow}
    (hrow : row.norm ≤ 2^31) :
    row.left.natAbs < 2^63 ∧ row.right.natAbs < 2^63 := by
  unfold SignedRow.norm at hrow
  constructor <;> omega

private theorem update_numerator_lt
    (a b : Limbs) (row : SignedRow) (ha : a.Bounded) (hb : b.Bounded)
    (hrow : row.norm ≤ 2^31) :
    (row.apply a.toNat b.toNat).natAbs < 2^287 := by
  have haLt := Limbs.toNat_lt a ha
  have hbLt := Limbs.toNat_lt b hb
  have happly := row.natAbs_apply_le (a.toNat : Int) (b.toNat : Int) (2^256 - 1)
    (by simpa only [Int.natAbs_natCast] using Nat.le_sub_one_of_lt haLt)
    (by simpa only [Int.natAbs_natCast] using Nat.le_sub_one_of_lt hbLt)
  calc
    (row.apply a.toNat b.toNat).natAbs ≤ row.norm * (2^256 - 1) := happly
    _ ≤ 2^31 * (2^256 - 1) := Nat.mul_le_mul_right _ hrow
    _ < 2^287 := by norm_num

/-- A concrete driver state represents its natural GCD state and signed coefficients. -/
def InvertStateRep (state : InvertState) (values : Nat × Nat) (coeff : CoeffPair) : Prop :=
  state.a.Bounded ∧ state.b.Bounded ∧
    state.a.toNat = values.1 ∧ state.b.toNat = values.2 ∧ Odd values.2 ∧
    WideCoeffRep state.u coeff.first ∧ WideCoeffRep state.v coeff.second

/-- One concrete batch consumes a fully named opaque shared batch view. -/
theorem invertBatch_components_spec
    (state : InvertState) (coeff : CoeffPair)
    (raw : SignedMatrix) (nums quotients : Int × Int)
    (batchMatrix : SignedMatrix) (nextState : Nat × Nat)
    (ha : state.a.Bounded) (hb : state.b.Bounded) (hodd : Odd state.b.toNat)
    (hu : WideCoeffRep state.u coeff.first) (hv : WideCoeffRep state.v coeff.second)
    (hraw : (semolinaShort state.a.toNat state.b.toNat).matrix = raw)
    (hnums0 : nums.1 = raw.row0.apply state.a.toNat state.b.toNat)
    (hnums1 : nums.2 = raw.row1.apply state.a.toNat state.b.toNat)
    (hdiv0 : (2^31 : Int) ∣ nums.1) (hdiv1 : (2^31 : Int) ∣ nums.2)
    (hquot0 : quotients.1 = nums.1 / (2^31 : Int))
    (hquot1 : quotients.2 = nums.2 / (2^31 : Int))
    (hnext0 : nextState.1 = quotients.1.natAbs)
    (hnext1 : nextState.2 = quotients.2.natAbs)
    (hrow0 : batchMatrix.row0 = SignedRow.scale (orient quotients.1) raw.row0)
    (hrow1 : batchMatrix.row1 = SignedRow.scale (orient quotients.2) raw.row1)
    (hbatchBound : batchMatrix.Bounded (2^31)) (hnextOdd : Odd nextState.2) :
    ∀ matrix, matrix = divsteps31 state.a state.b →
    ∀ nextA, nextA = updateAB state.a state.b matrix.f0 matrix.g0 →
    ∀ nextB, nextB = updateAB state.a state.b matrix.f1 matrix.g1 →
    ∀ nextU, nextU = invertLincomb state.u state.v nextA.f nextA.g →
    ∀ nextV, nextV = invertLincomb state.u state.v nextB.f nextB.g →
      nextA.value.Bounded ∧ nextB.value.Bounded ∧
      nextA.value.toNat = nextState.1 ∧ nextB.value.toNat = nextState.2 ∧
      Odd nextB.value.toNat ∧
      WideCoeffRep nextU (coeff.update batchMatrix).first ∧
      WideCoeffRep nextV (coeff.update batchMatrix).second := by
  intro matrix hmatrix nextA hnextA nextB hnextB nextU hnextU nextV hnextV
  subst nextA
  subst nextB
  subst nextU
  subst nextV
  have hdivsteps := divsteps31_spec state.a state.b ha hb hodd matrix hmatrix
  have hmatrixWords : matrix.f0 < 2^64 ∧ matrix.g0 < 2^64 ∧
      matrix.f1 < 2^64 ∧ matrix.g1 < 2^64 := by
    rw [hmatrix]
    exact divsteps31_words_bounded state.a state.b
  have hmatrixRep : InvertMatrixRep matrix raw := by
    rw [← hraw]
    exact hdivsteps.1
  have hrawBound : raw.Bounded (2^31) := by
    rw [← hraw]
    exact hdivsteps.2
  have hnum0 : nums.1.natAbs < 2^287 := by
    rw [hnums0]
    exact update_numerator_lt state.a state.b raw.row0 ha hb hrawBound.1
  have hnum1 : nums.2.natAbs < 2^287 := by
    rw [hnums1]
    exact update_numerator_lt state.a state.b raw.row1 ha hb hrawBound.2
  have hentries0 := row_entry_lt_signed_word hrawBound.1
  have hentries1 := row_entry_lt_signed_word hrawBound.2
  have hzeroRows := semolinaShort_left_nonneg_if_zero state.a.toNat state.b.toNat
  have hzero0 : state.a.toNat = 0 → 0 ≤ raw.row0.left := by rw [← hraw]; exact hzeroRows.1
  have hzero1 : state.a.toNat = 0 → 0 ≤ raw.row1.left := by rw [← hraw]; exact hzeroRows.2
  have hbPos : 0 < state.b.toNat := by
    rcases hodd with ⟨k, hk⟩
    omega
  obtain ⟨hnextABound, hnextAValue, hnextAF, hnextAG⟩ :=
    updateAB_exact state.a state.b matrix.f0 matrix.g0 raw.row0.left raw.row0.right
      ha hb hmatrixWords.1 hmatrixWords.2.1 hmatrixRep.1 hmatrixRep.2.1
      hentries0.1 hentries0.2 hzero0 hbPos
      (by simpa only [hnums0, SignedRow.apply] using hnum0)
      (by simpa only [hnums0, SignedRow.apply] using hdiv0) _ rfl
  obtain ⟨hnextBBound, hnextBValue, hnextBF, hnextBG⟩ :=
    updateAB_exact state.a state.b matrix.f1 matrix.g1 raw.row1.left raw.row1.right
      ha hb hmatrixWords.2.2.1 hmatrixWords.2.2.2 hmatrixRep.2.2.1 hmatrixRep.2.2.2
      hentries1.1 hentries1.2 hzero1 hbPos
      (by simpa only [hnums1, SignedRow.apply] using hnum1)
      (by simpa only [hnums1, SignedRow.apply] using hdiv1) _ rfl
  have hvalueA : (updateAB state.a state.b matrix.f0 matrix.g0).value.toNat = nextState.1 := by
    calc
      _ = nums.1.natAbs / 2^31 := by simpa only [hnums0, SignedRow.apply] using hnextAValue
      _ = (nums.1 / (2^31 : Int)).natAbs :=
        (natAbs_ediv_of_dvd (by positivity) hdiv0).symm
      _ = quotients.1.natAbs := by rw [hquot0]
      _ = nextState.1 := hnext0.symm
  have hvalueB : (updateAB state.a state.b matrix.f1 matrix.g1).value.toNat = nextState.2 := by
    calc
      _ = nums.2.natAbs / 2^31 := by simpa only [hnums1, SignedRow.apply] using hnextBValue
      _ = (nums.2 / (2^31 : Int)).natAbs :=
        (natAbs_ediv_of_dvd (by positivity) hdiv1).symm
      _ = quotients.2.natAbs := by rw [hquot1]
      _ = nextState.2 := hnext1.symm
  have horient0 : orient quotients.1 = orient nums.1 := by
    rw [hquot0]
    exact orient_ediv_eq_of_dvd (by positivity) hdiv0
  have horient1 : orient quotients.2 = orient nums.2 := by
    rw [hquot1]
    exact orient_ediv_eq_of_dvd (by positivity) hdiv1
  have hnextAF' : WordRep (updateAB state.a state.b matrix.f0 matrix.g0).f
      batchMatrix.row0.left := by
    rw [hrow0]
    change WordRep _ (orient quotients.1 * raw.row0.left)
    rw [horient0, hnums0]
    simpa only [SignedRow.apply] using hnextAF
  have hnextAG' : WordRep (updateAB state.a state.b matrix.f0 matrix.g0).g
      batchMatrix.row0.right := by
    rw [hrow0]
    change WordRep _ (orient quotients.1 * raw.row0.right)
    rw [horient0, hnums0]
    simpa only [SignedRow.apply] using hnextAG
  have hnextBF' : WordRep (updateAB state.a state.b matrix.f1 matrix.g1).f
      batchMatrix.row1.left := by
    rw [hrow1]
    change WordRep _ (orient quotients.2 * raw.row1.left)
    rw [horient1, hnums1]
    simpa only [SignedRow.apply] using hnextBF
  have hnextBG' : WordRep (updateAB state.a state.b matrix.f1 matrix.g1).g
      batchMatrix.row1.right := by
    rw [hrow1]
    change WordRep _ (orient quotients.2 * raw.row1.right)
    rw [horient1, hnums1]
    simpa only [SignedRow.apply] using hnextBG
  have hbatchEntries0 := row_entry_lt_signed_word hbatchBound.1
  have hbatchEntries1 := row_entry_lt_signed_word hbatchBound.2
  have hnextAWords := updateAB_words_bounded state.a state.b matrix.f0 matrix.g0
  have hnextBWords := updateAB_words_bounded state.a state.b matrix.f1 matrix.g1
  have hnextURep := invertLincomb_rep state.u state.v
    (updateAB state.a state.b matrix.f0 matrix.g0).f
    (updateAB state.a state.b matrix.f0 matrix.g0).g
    coeff.first coeff.second batchMatrix.row0.left batchMatrix.row0.right
    hu hv hnextAWords.1 hnextAWords.2 hnextAF' hnextAG'
    hbatchEntries0.1 hbatchEntries0.2
  have hnextVRep := invertLincomb_rep state.u state.v
    (updateAB state.a state.b matrix.f1 matrix.g1).f
    (updateAB state.a state.b matrix.f1 matrix.g1).g
    coeff.first coeff.second batchMatrix.row1.left batchMatrix.row1.right
    hu hv hnextBWords.1 hnextBWords.2 hnextBF' hnextBG'
    hbatchEntries1.1 hbatchEntries1.2
  refine ⟨hnextABound, hnextBBound, hvalueA, hvalueB, ?_, ?_, ?_⟩
  · rw [hvalueB]
    exact hnextOdd
  · simpa only [CoeffPair.update, SignedRow.apply] using hnextURep
  · simpa only [CoeffPair.update, SignedRow.apply] using hnextVRep

/-- The actual batch represents the opaque view's successor and coefficient update. -/
theorem invertBatch_rep (state : InvertState) (values : Nat × Nat) (coeff : CoeffPair)
    (hstate : InvertStateRep state values coeff) (view : SemolinaBatchView values) :
    InvertStateRep (invertBatch state) view.nextState (coeff.update view.batchMatrix) ∧
      Batches 31 1 coeff (coeff.update view.batchMatrix) := by
  rcases hstate with ⟨ha, hb, hstateA, hstateB, hodd, hu, hv⟩
  have hoddConcrete : Odd state.b.toNat := by simpa only [hstateB] using hodd
  let matrix := divsteps31 state.a state.b
  let nextA := updateAB state.a state.b matrix.f0 matrix.g0
  let nextB := updateAB state.a state.b matrix.f1 matrix.g1
  let nextU := invertLincomb state.u state.v nextA.f nextA.g
  let nextV := invertLincomb state.u state.v nextB.f nextB.g
  have hcomponents := invertBatch_components_spec state coeff view.raw view.numerators
    view.quotients view.batchMatrix view.nextState ha hb hoddConcrete hu hv
    (by simpa only [hstateA, hstateB] using view.raw_eq)
    (by simpa only [hstateA, hstateB] using view.numerator_fst)
    (by simpa only [hstateA, hstateB] using view.numerator_snd)
    view.numerator_fst_dvd view.numerator_snd_dvd view.quotient_fst view.quotient_snd
    view.next_fst view.next_snd view.row0_eq view.row1_eq view.matrix_bounded view.next_odd
    matrix rfl nextA rfl nextB rfl nextU rfl nextV rfl
  rcases hcomponents with ⟨hnextA, hnextB, hvalueA, hvalueB, hnextOdd, hnextU, hnextV⟩
  constructor
  · change nextA.value.Bounded ∧ nextB.value.Bounded ∧
      nextA.value.toNat = view.nextState.1 ∧ nextB.value.toNat = view.nextState.2 ∧
      Odd view.nextState.2 ∧ WideCoeffRep nextU (coeff.update view.batchMatrix).first ∧
      WideCoeffRep nextV (coeff.update view.batchMatrix).second
    exact ⟨hnextA, hnextB, hvalueA, hvalueB, view.next_odd, hnextU, hnextV⟩
  · exact Batches.succ view.batchMatrix view.matrix_bounded rfl (Batches.zero _)

/-- A four-limb value below one word is exactly its low limb. -/
theorem Limbs.l0_eq_toNat_of_lt_word (value : Limbs) (hlt : value.toNat < 2^64) :
    value.l0 = value.toNat := by
  unfold Limbs.toNat at hlt ⊢
  omega

/-- The concrete final-row linear combination represents its signed abstract coefficient. -/
theorem finalCoefficient_rep (u v : PastaAsm.WideLimbs) (f g : Nat) (coeff : CoeffPair)
    (row : SignedRow)
    (hu : WideCoeffRep u coeff.first) (hv : WideCoeffRep v coeff.second)
    (hfBound : f < 2^64) (hgBound : g < 2^64)
    (hf : WordRep f row.left) (hg : WordRep g row.right)
    (hrow : row.norm ≤ 2^47) :
    WideCoeffRep (invertLincomb u v f g) (row.apply coeff.first coeff.second) := by
  have hentries : row.left.natAbs < 2^63 ∧ row.right.natAbs < 2^63 := by
    unfold SignedRow.norm at hrow
    constructor <;> omega
  simpa only [SignedRow.apply] using
    invertLincomb_rep u v f g coeff.first coeff.second row.left row.right
      hu hv hfBound hgBound hf hg hentries.1 hentries.2

/-- A represented coefficient within the complete schedule bound decodes exactly. -/
theorem WideCoeffRep.schedule_range {words : PastaAsm.WideLimbs} {coefficient : Int}
    (hrep : WideCoeffRep words coefficient)
    (hbound : coefficient.natAbs ≤ 2^scheduleBits) :
    words.toInt = coefficient ∧
      -(coefficientRadix : Int) ≤ words.toInt ∧
      words.toInt ≤ coefficientRadix := by
  have hfits : coefficient.natAbs < 2^575 :=
    hbound.trans_lt full_schedule_bound_fits_signed_wide
  have hexact := hrep.toInt_eq hfits
  have h512 : coefficient.natAbs ≤ 2^512 := by
    simpa only [scheduleBits_eq] using hbound
  have habs : (coefficient.natAbs : Int) ≤ 2^512 := by exact_mod_cast h512
  refine ⟨hexact, ?_, ?_⟩
  · rw [hexact]
    change -(2^512 : Int) ≤ coefficient
    omega
  · rw [hexact]
    change coefficient ≤ (2^512 : Int)
    omega

/-- The fixed schedule scale is the square of the Montgomery radix. -/
theorem schedule_scale_eq_R_sq : 2^scheduleBits = R^2 := by
  rw [scheduleBits_eq]
  change 2^512 = (2^256)^2
  rw [show 512 = 256 * 2 by omega, pow_mul]

/-- The complete schedule connects the represented final concrete coefficient
with its closed normalization range and `R²` congruence. -/
theorem finalCoefficient_schedule_spec
    {modulus input : Nat} {start finish : BatchPoint}
    {matrix : SignedMatrix} {after : GCDState}
    (u v : PastaAsm.WideLimbs) (f g : Nat)
    (schedule : RelationN BatchRel 15 start finish)
    (hstartValues : start.values = (input, modulus))
    (hstartCoeff : start.coeff = initialCoefficients)
    (htransition : ScaledTransition 47 matrix
      ⟨finish.values.1, finish.values.2⟩ after)
    (hafter : after.second = 1)
    (hu : WideCoeffRep u finish.coeff.first)
    (hv : WideCoeffRep v finish.coeff.second)
    (hfBound : f < 2^64) (hgBound : g < 2^64)
    (hf : WordRep f matrix.row1.left)
    (hg : WordRep g matrix.row1.right)
    (hrow : matrix.row1.norm ≤ 2^47) :
    let coefficient := invertLincomb u v f g
    coefficient.Bounded ∧
      -(coefficientRadix : Int) ≤ coefficient.toInt ∧
      coefficient.toInt ≤ coefficientRadix ∧
      (modulus : Int) ∣ (R^2 : Int) - coefficient.toInt * input := by
  dsimp only
  let coefficient := invertLincomb u v f g
  have hcoefficientRep := finalCoefficient_rep u v f g finish.coeff matrix.row1
    hu hv hfBound hgBound hf hg hrow
  have hbatches : Batches 31 15 initialCoefficients finish.coeff := by
    rw [← hstartCoeff]
    exact batchSchedule_batches schedule
  have hcoefficientAbs :
      (matrix.row1.apply finish.coeff.first finish.coeff.second).natAbs ≤
        2^scheduleBits :=
    schedule_row1_coefficient_bound hbatches hrow
  obtain ⟨hcoefficientExact, hcoefficientLower, hcoefficientUpper⟩ :=
    hcoefficientRep.schedule_range hcoefficientAbs
  have habstractInvariant : (modulus : Int) ∣
      (2^scheduleBits : Int) -
        matrix.row1.apply finish.coeff.first finish.coeff.second * input :=
    schedule_identity_final_coefficient_invariant schedule hstartValues hstartCoeff
      htransition hafter
  have hconcreteInvariant : (modulus : Int) ∣
      (R^2 : Int) - coefficient.toInt * input := by
    rw [hcoefficientExact]
    simpa only [schedule_scale_eq_R_sq] using habstractInvariant
  exact ⟨hcoefficientRep.1, hcoefficientLower, hcoefficientUpper, hconcreteInvariant⟩

/-- A final concrete row connects the represented prefix coefficients to the complete
schedule invariant. This boundary keeps row projections out of the top-level driver proof. -/
theorem finalRowCoefficient_schedule_spec
    {modulus input : Nat} {start finish : BatchPoint}
    {matrix : SignedMatrix} {after : GCDState}
    (u v : PastaAsm.WideLimbs) (row : InvertRow)
    (schedule : RelationN BatchRel 15 start finish)
    (hstartValues : start.values = (input, modulus))
    (hstartCoeff : start.coeff = initialCoefficients)
    (htransition : ScaledTransition 47 matrix
      ⟨finish.values.1, finish.values.2⟩ after)
    (hafter : after.second = 1)
    (hu : WideCoeffRep u finish.coeff.first)
    (hv : WideCoeffRep v finish.coeff.second)
    (hfBound : row.f1 < 2^64) (hgBound : row.g1 < 2^64)
    (hf : WordRep row.f1 matrix.row1.left)
    (hg : WordRep row.g1 matrix.row1.right)
    (hrow : matrix.row1.norm ≤ 2^47) :
    let coefficient := invertLincomb u v row.f1 row.g1
    coefficient.Bounded ∧
      -(coefficientRadix : Int) ≤ coefficient.toInt ∧
      coefficient.toInt ≤ coefficientRadix ∧
      (modulus : Int) ∣ (R^2 : Int) - coefficient.toInt * input := by
  exact finalCoefficient_schedule_spec u v row.f1 row.g1 schedule hstartValues hstartCoeff
    htransition hafter hu hv hfBound hgBound hf hg hrow

/-- Small bundle of final-tail facts, used to prevent repeated elaboration of matrix projections. -/
structure FinalTailFacts (row : InvertRow) (matrix : SignedMatrix) (after : GCDState) : Prop where
  rowFacts : FinalRowFacts row matrix
  terminal : after.second = 1

/-- Explicit-coefficient form of the final-row schedule boundary. -/
theorem finalRowCoefficient_named_spec
    {modulus input : Nat} {start finish : BatchPoint}
    {matrix : SignedMatrix} {after : GCDState}
    (u v : PastaAsm.WideLimbs) (row : InvertRow) (coefficient : PastaAsm.WideLimbs)
    (hcoefficient : coefficient = invertLincomb u v row.f1 row.g1)
    (schedule : RelationN BatchRel 15 start finish)
    (hstartValues : start.values = (input, modulus))
    (hstartCoeff : start.coeff = initialCoefficients)
    (htransition : ScaledTransition 47 matrix
      ⟨finish.values.1, finish.values.2⟩ after)
    (hafter : after.second = 1)
    (hu : WideCoeffRep u finish.coeff.first)
    (hv : WideCoeffRep v finish.coeff.second)
    (hfBound : row.f1 < 2^64) (hgBound : row.g1 < 2^64)
    (hf : WordRep row.f1 matrix.row1.left)
    (hg : WordRep row.g1 matrix.row1.right)
    (hrow : matrix.row1.norm ≤ 2^47) :
    coefficient.Bounded ∧
      -(coefficientRadix : Int) ≤ coefficient.toInt ∧
      coefficient.toInt ≤ coefficientRadix ∧
      (modulus : Int) ∣ (R^2 : Int) - coefficient.toInt * input := by
  subst coefficient
  exact finalRowCoefficient_schedule_spec u v row schedule hstartValues hstartCoeff
    htransition hafter hu hv hfBound hgBound hf hg hrow

/-- Bundled final-tail form used by the top-level driver proof. -/
theorem finalTailCoefficient_spec
    {modulus input : Nat} {start finish : BatchPoint}
    {matrix : SignedMatrix} {after : GCDState}
    (u v : PastaAsm.WideLimbs) (row : InvertRow) (coefficient : PastaAsm.WideLimbs)
    (hcoefficient : coefficient = invertLincomb u v row.f1 row.g1)
    (schedule : RelationN BatchRel 15 start finish)
    (hstartValues : start.values = (input, modulus))
    (hstartCoeff : start.coeff = initialCoefficients)
    (htransition : ScaledTransition 47 matrix
      ⟨finish.values.1, finish.values.2⟩ after)
    (hu : WideCoeffRep u finish.coeff.first)
    (hv : WideCoeffRep v finish.coeff.second)
    (facts : FinalTailFacts row matrix after) :
    coefficient.Bounded ∧
      -(coefficientRadix : Int) ≤ coefficient.toInt ∧
      coefficient.toInt ≤ coefficientRadix ∧
      (modulus : Int) ∣ (R^2 : Int) - coefficient.toInt * input := by
  exact finalRowCoefficient_named_spec u v row coefficient hcoefficient schedule
    hstartValues hstartCoeff htransition facts.terminal hu hv facts.rowFacts.fBound
    facts.rowFacts.gBound facts.rowFacts.fRep facts.rowFacts.gRep facts.rowFacts.rowBound

/-- The shared final approximation transition, specialized to a named prefix endpoint. -/
theorem finalTransition_spec (a b : Nat) (values : Nat × Nat)
    (ha : a = values.1) (hb : b = values.2) (hodd : Odd b) :
    let final := approxSteps 47 (ApproxState.initial a b)
    ScaledTransition 47 final.matrix ⟨values.1, values.2⟩ ⟨final.a, final.b⟩ := by
  dsimp only
  have hrepr := approxSteps_initial_representation 47 a b hodd
  simpa only [ha, hb] using hrepr

/-- Three applications of the epilogue reduction helper reduce any bounded four-limb
value to a canonical Pasta residue. Each application preserves its residue. -/
theorem reduceThree_spec (value modulus : Limbs) (hv : value.Bounded)
    (hm : modulus.Bounded) (hshape : modulus.l2 = 0 ∧ modulus.l3 = 2^62) :
    let high1 := reduceOnce value modulus
    let high2 := reduceOnce high1 modulus
    let high := reduceOnce high2 modulus
    high.Bounded ∧ high.toNat < modulus.toNat ∧
      high.toNat ≡ value.toNat [MOD modulus.toNat] := by
  dsimp only
  let high1 := reduceOnce value modulus
  let high2 := reduceOnce high1 modulus
  let high := reduceOnce high2 modulus
  obtain ⟨hhigh1, hcases1⟩ := reduceOnce_spec value modulus hv hm high1 rfl
  obtain ⟨hhigh2, hcases2⟩ := reduceOnce_spec high1 modulus hhigh1 hm high2 rfl
  obtain ⟨hhigh, hcases3⟩ := reduceOnce_spec high2 modulus hhigh2 hm high rfl
  have hmod1 : high1.toNat ≡ value.toNat [MOD modulus.toNat] := by
    rcases hcases1 with ⟨_, heq⟩ | ⟨_, heq⟩
    · exact modEq_of_add_mul _ _ 0 0 _ (by omega)
    · exact modEq_of_add_mul _ _ 1 0 _ (by omega)
  have hmod2 : high2.toNat ≡ high1.toNat [MOD modulus.toNat] := by
    rcases hcases2 with ⟨_, heq⟩ | ⟨_, heq⟩
    · exact modEq_of_add_mul _ _ 0 0 _ (by omega)
    · exact modEq_of_add_mul _ _ 1 0 _ (by omega)
  have hmod3 : high.toNat ≡ high2.toNat [MOD modulus.toNat] := by
    rcases hcases3 with ⟨_, heq⟩ | ⟨_, heq⟩
    · exact modEq_of_add_mul _ _ 0 0 _ (by omega)
    · exact modEq_of_add_mul _ _ 1 0 _ (by omega)
  have hpLower : 2^254 ≤ modulus.toNat := by
    calc
      2^254 = 2^192 * 2^62 := by norm_num [pow_add]
      _ ≤ modulus.toNat := by
        simp only [Limbs.toNat, hshape.1, hshape.2, mul_zero, add_zero]
        omega
  have hvalueLt : value.toNat < 4 * modulus.toNat := by
    apply lt_of_lt_of_le (Limbs.toNat_lt value hv)
    calc
      2^256 = 4 * 2^254 := by norm_num [pow_add]
      _ ≤ 4 * modulus.toNat := Nat.mul_le_mul_left 4 hpLower
  refine ⟨hhigh, ?_, hmod3.trans (hmod2.trans hmod1)⟩
  change high.toNat < modulus.toNat
  rcases hcases1 with ⟨h1lt, h1eq⟩ | ⟨h1ge, h1eq⟩ <;>
    rcases hcases2 with ⟨h2lt, h2eq⟩ | ⟨h2ge, h2eq⟩ <;>
      rcases hcases3 with ⟨h3lt, h3eq⟩ | ⟨h3ge, h3eq⟩ <;> omega

/-- The concrete normalization and reduction epilogue turns the schedule's signed
coefficient congruence into a canonical inverse result. -/
theorem invertEpilogue_spec
    (coefficient : PastaAsm.WideLimbs) (modulus : Limbs) (inv converted original : Nat)
    (hcoefficientBound : coefficient.Bounded) (hm : modulus.Bounded)
    (hshape : modulus.l2 = 0 ∧ modulus.l3 = 2^62)
    (hinvLt : inv < 2^64) (hinv : (inv * modulus.l0 + 1) % 2^64 = 0)
    (hp : PastaSizedOdd modulus.toNat)
    (hlower : -(coefficientRadix : Int) ≤ coefficient.toInt)
    (hupper : coefficient.toInt ≤ coefficientRadix)
    (hcoefficientInvariant : (modulus.toNat : Int) ∣
      (R^2 : Int) - coefficient.toInt * converted)
    (hconverted : R * converted ≡ original [MOD modulus.toNat]) :
    let split := normalizeCoefficient coefficient modulus
    let low := fromMont split.low modulus inv
    let high1 := reduceOnce split.high modulus
    let high2 := reduceOnce high1 modulus
    let high := reduceOnce high2 modulus
    let out := addMod low high modulus
    out.Bounded ∧ out.toNat < modulus.toNat ∧
      original * out.toNat ≡ R^2 [MOD modulus.toNat] := by
  dsimp only
  let split := normalizeCoefficient coefficient modulus
  let low := fromMont split.low modulus inv
  let high1 := reduceOnce split.high modulus
  let high2 := reduceOnce high1 modulus
  let high := reduceOnce high2 modulus
  let out := addMod low high modulus
  obtain ⟨hsplitLow, hsplitHighBound, hsplitValue, _⟩ :=
    normalizeCoefficient_spec coefficient modulus hcoefficientBound hm hshape hp hlower hupper
      split rfl
  obtain ⟨hlowBound, hlowLt, hlowMod⟩ :=
    fromMont_spec split.low modulus inv
      (by rw [hsplitLow]; exact ⟨hcoefficientBound.1, hcoefficientBound.2.1,
        hcoefficientBound.2.2.1, hcoefficientBound.2.2.2.1⟩)
      hm hshape hinvLt hinv low rfl
  obtain ⟨hhighBound, hhighLt, hhighMod⟩ :=
    reduceThree_spec split.high modulus hsplitHighBound hm hshape
  obtain ⟨houtBound, houtLt, houtMod⟩ :=
    addMod_spec_of_lt low high modulus hlowBound hhighBound hm hshape hlowLt hhighLt out rfl
  have hnormalizedNonneg : 0 ≤ normalize modulus.toNat coefficient.toInt :=
    (normalize_schedule_spec hp hlower hupper).1
  have hnormalizedCast :
      (((normalize modulus.toNat coefficient.toInt).toNat : Nat) : Int) =
        normalize modulus.toNat coefficient.toInt :=
    Int.toNat_of_nonneg hnormalizedNonneg
  have hnormalizationDvd : (modulus.toNat : Int) ∣
      ((normalize modulus.toNat coefficient.toInt).toNat : Int) - coefficient.toInt := by
    rw [hnormalizedCast]
    exact normalize_schedule_sub_dvd_modulus hp hlower hupper
  have hnormalizedModInt :
      ((normalize modulus.toNat coefficient.toInt).toNat : Int) ≡ coefficient.toInt
        [ZMOD modulus.toNat] :=
    (Int.modEq_iff_dvd.mpr hnormalizationDvd).symm
  have hcoefficientModInt : coefficient.toInt * converted ≡ (R^2 : Int)
      [ZMOD modulus.toNat] := Int.modEq_iff_dvd.mpr hcoefficientInvariant
  have hnormalizedProductInt :
      ((normalize modulus.toNat coefficient.toInt).toNat : Int) * converted ≡ (R^2 : Int)
        [ZMOD modulus.toNat] :=
    (hnormalizedModInt.mul_right converted).trans hcoefficientModInt
  have hnormalizedProduct :
      (normalize modulus.toNat coefficient.toInt).toNat * converted ≡ R^2
        [MOD modulus.toNat] := by
    exact Int.natCast_modEq_iff.mp (by
      simpa only [Int.natCast_mul, Int.natCast_pow] using hnormalizedProductInt)
  have hsplitMod : R * (low.toNat + high.toNat) ≡
      split.low.toNat + R * split.high.toNat [MOD modulus.toNat] := by
    calc
      R * (low.toNat + high.toNat) = R * low.toNat + R * high.toNat := by ring
      _ ≡ split.low.toNat + R * high.toNat [MOD modulus.toNat] :=
        hlowMod.add_right (R * high.toNat)
      _ ≡ split.low.toNat + R * split.high.toNat [MOD modulus.toNat] :=
        Nat.ModEq.add_left split.low.toNat (Nat.ModEq.mul_left R hhighMod)
  have hnormalizedEq : split.low.toNat + R * split.high.toNat =
      (normalize modulus.toNat coefficient.toInt).toNat := by
    simpa only [R, splitRadix] using hsplitValue
  have houtScaled : R * out.toNat ≡
      (normalize modulus.toNat coefficient.toInt).toNat [MOD modulus.toNat] := by
    calc
      R * out.toNat ≡ R * (low.toNat + high.toNat) [MOD modulus.toNat] :=
        Nat.ModEq.mul_left R houtMod
      _ ≡ split.low.toNat + R * split.high.toNat [MOD modulus.toNat] := hsplitMod
      _ = (normalize modulus.toNat coefficient.toInt).toNat := hnormalizedEq
  have hleft : R * (out.toNat * converted) ≡ R^2 [MOD modulus.toNat] := by
    calc
      R * (out.toNat * converted) = (R * out.toNat) * converted := by ring
      _ ≡ (normalize modulus.toNat coefficient.toInt).toNat * converted
          [MOD modulus.toNat] := Nat.ModEq.mul_right converted houtScaled
      _ ≡ R^2 [MOD modulus.toNat] := hnormalizedProduct
  have hright : R * (out.toNat * converted) ≡ original * out.toNat
      [MOD modulus.toNat] := by
    calc
      R * (out.toNat * converted) = (R * converted) * out.toNat := by ring
      _ ≡ original * out.toNat [MOD modulus.toNat] := Nat.ModEq.mul_right out.toNat hconverted
  exact ⟨houtBound, houtLt, hright.symm.trans hleft⟩

/-- Either supported field has the size and parity used by normalization. -/
theorem IsInversionField.pastaSizedOdd {F : PastaField} (hF : IsInversionField F) :
    PastaSizedOdd F.modulus.toNat := by
  rcases hF with rfl | rfl <;>
    refine ⟨Nat.odd_iff.mpr (by decide), ?_, ?_⟩ <;>
    norm_num [pallasBase, vestaBase, Limbs.toNat]

end PastaAsm.AArch64
