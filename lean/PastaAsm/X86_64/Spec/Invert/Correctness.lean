/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.Fields.Inversion
import PastaAsm.Spec.Invert.Batch
import PastaAsm.X86_64.Spec.Add
import PastaAsm.X86_64.Spec.FromMont
import PastaAsm.X86_64.Spec.Invert.Divsteps
import PastaAsm.X86_64.Spec.Invert.Normalize
import PastaAsm.X86_64.Spec.Invert.Schedule
import PastaAsm.X86_64.Spec.Invert.Update

/-!
# Concrete arithmetic correspondence for x86-64 inversion

This module connects one concrete x86-64 inversion batch to the shared signed
coefficient model.  Long-schedule iteration is kept in `Schedule.lean` so its
induction never unfolds the generated approximation computation.
-/

namespace PastaAsm.X86_64

open Spec.Invert Spec.Invert.Convergence Spec.Invert.Normalize

set_option exponentiation.threshold 600

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

private theorem mulSigned9_signed_modEq
    (value : PastaAsm.WideLimbs) (scalar : Nat) (x : Int)
    (hv : value.Bounded) (hscalar : SignedWordRep scalar x)
    (hx : x.natAbs < 2^63) :
    (mulSigned9 value scalar).Bounded ∧
      (mulSigned9 value scalar).toNat ≡ (value.toNat : Int) * x
        [ZMOD coefficientModulus] := by
  have hslt : scalar < 2^64 := hscalar.1
  obtain ⟨hout, hcases⟩ := mulSigned9_spec value scalar hv hslt
  refine ⟨hout, ?_⟩
  rcases hscalar.2 with ⟨k, hk⟩
  rcases hcases with ⟨hsmall, hmod⟩ | ⟨hlarge, hmod⟩
  · have hkzero : k = 0 := by
      have hscalarInt : (scalar : Int) < 2^63 := by exact_mod_cast hsmall
      have hxlower : -(2^63 : Int) < x := by
        have habs : (x.natAbs : Int) < 2^63 := by exact_mod_cast hx
        omega
      norm_num only at hk
      omega
    have hxeq : x = scalar := by
      norm_num only at hk
      rw [hkzero] at hk
      omega
    simpa only [hxeq, Int.natCast_mul] using Int.natCast_modEq_iff.mpr hmod
  · have hkone : k = 1 := by
      have hscalarInt : (2^63 : Int) ≤ scalar := by exact_mod_cast hlarge
      have hxupper : x < (2^63 : Int) := by
        have habs : (x.natAbs : Int) < 2^63 := by exact_mod_cast hx
        omega
      norm_num only at hk
      omega
    have hxeq : x = (scalar : Int) - 2^64 := by
      norm_num only at hk
      rw [hkone] at hk
      omega
    have hcast := Int.natCast_modEq_iff.mpr hmod
    rw [Int.natCast_add, Int.natCast_mul] at hcast
    have hsubCast : ((2^64 - scalar : Nat) : Int) = (2^64 : Int) - scalar := by
      rw [Int.natCast_sub hslt.le]
      norm_num
    rw [Int.modEq_iff_dvd] at hcast ⊢
    rw [hsubCast] at hcast
    convert hcast using 1
    all_goals (rw [hxeq]; ring)

/-- The concrete nine-word linear combination applies a represented signed row. -/
theorem invertLincomb9_rep
    (u v : PastaAsm.WideLimbs) (f g : Nat) (x y left right : Int)
    (hu : WideCoeffRep u x) (hv : WideCoeffRep v y)
    (hf : SignedWordRep f left) (hg : SignedWordRep g right)
    (hleft : left.natAbs < 2^63) (hright : right.natAbs < 2^63) :
    WideCoeffRep (invertLincomb9 u v f g) (left * x + right * y) := by
  obtain ⟨huf, hufMod⟩ := mulSigned9_signed_modEq u f left hu.1 hf hleft
  obtain ⟨hvg, hvgMod⟩ := mulSigned9_signed_modEq v g right hv.1 hg hright
  have hout := addWords9_spec (mulSigned9 u f) (mulSigned9 v g) huf hvg
  refine ⟨hout.1, ?_⟩
  have hadd := Int.natCast_modEq_iff.mpr
    (addWords9_modEq (mulSigned9 u f) (mulSigned9 v g) huf hvg)
  have huMod : (u.toNat : Int) ≡ x [ZMOD coefficientModulus] := by
    exact (Int.modEq_iff_dvd.mpr hu.2).symm
  have hvMod : (v.toNat : Int) ≡ y [ZMOD coefficientModulus] := by
    exact (Int.modEq_iff_dvd.mpr hv.2).symm
  have hresult : ((invertLincomb9 u v f g).toNat : Int) ≡
      left * x + right * y [ZMOD coefficientModulus] := by
    calc
      ((invertLincomb9 u v f g).toNat : Int) ≡
          ((mulSigned9 u f).toNat : Int) + ((mulSigned9 v g).toNat : Int)
          [ZMOD coefficientModulus] := by simpa [invertLincomb9] using hadd
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
    ∀ nextA, nextA = updateAb state.a state.b matrix.f0 matrix.g0 →
    ∀ nextB, nextB = updateAb state.a state.b matrix.f1 matrix.g1 →
    ∀ nextU, nextU = invertLincomb9 state.u state.v nextA.f nextA.g →
    ∀ nextV, nextV = invertLincomb9 state.u state.v nextB.f nextB.g →
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
  obtain ⟨hnextABound, hnextAValue, hnextAF, hnextAG⟩ :=
    updateAb_exact state.a state.b matrix.f0 matrix.g0 raw.row0.left raw.row0.right
      ha hb hmatrixRep.1 hmatrixRep.2.1 hentries0.1 hentries0.2
      (by simpa only [hnums0] using hnum0) (by simpa only [hnums0] using hdiv0)
  obtain ⟨hnextBBound, hnextBValue, hnextBF, hnextBG⟩ :=
    updateAb_exact state.a state.b matrix.f1 matrix.g1 raw.row1.left raw.row1.right
      ha hb hmatrixRep.2.2.1 hmatrixRep.2.2.2 hentries1.1 hentries1.2
      (by simpa only [hnums1] using hnum1) (by simpa only [hnums1] using hdiv1)
  have hvalueA : (updateAb state.a state.b matrix.f0 matrix.g0).value.toNat = nextState.1 := by
    calc
      (updateAb state.a state.b matrix.f0 matrix.g0).value.toNat = nums.1.natAbs / 2^31 := by
        simpa only [hnums0] using hnextAValue
      _ = (nums.1 / (2^31 : Int)).natAbs :=
        (natAbs_ediv_of_dvd (by positivity) hdiv0).symm
      _ = quotients.1.natAbs := by rw [hquot0]
      _ = nextState.1 := hnext0.symm
  have hvalueB : (updateAb state.a state.b matrix.f1 matrix.g1).value.toNat = nextState.2 := by
    calc
      (updateAb state.a state.b matrix.f1 matrix.g1).value.toNat = nums.2.natAbs / 2^31 := by
        simpa only [hnums1] using hnextBValue
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
  have hnextAF' : SignedWordRep (updateAb state.a state.b matrix.f0 matrix.g0).f
      batchMatrix.row0.left := by
    rw [hrow0]
    change SignedWordRep _ (orient quotients.1 * raw.row0.left)
    rw [horient0, hnums0]
    exact hnextAF
  have hnextAG' : SignedWordRep (updateAb state.a state.b matrix.f0 matrix.g0).g
      batchMatrix.row0.right := by
    rw [hrow0]
    change SignedWordRep _ (orient quotients.1 * raw.row0.right)
    rw [horient0, hnums0]
    exact hnextAG
  have hnextBF' : SignedWordRep (updateAb state.a state.b matrix.f1 matrix.g1).f
      batchMatrix.row1.left := by
    rw [hrow1]
    change SignedWordRep _ (orient quotients.2 * raw.row1.left)
    rw [horient1, hnums1]
    exact hnextBF
  have hnextBG' : SignedWordRep (updateAb state.a state.b matrix.f1 matrix.g1).g
      batchMatrix.row1.right := by
    rw [hrow1]
    change SignedWordRep _ (orient quotients.2 * raw.row1.right)
    rw [horient1, hnums1]
    exact hnextBG
  have hbatchEntries0 := row_entry_lt_signed_word hbatchBound.1
  have hbatchEntries1 := row_entry_lt_signed_word hbatchBound.2
  have hnextURep := invertLincomb9_rep state.u state.v
    (updateAb state.a state.b matrix.f0 matrix.g0).f
    (updateAb state.a state.b matrix.f0 matrix.g0).g
    coeff.first coeff.second batchMatrix.row0.left batchMatrix.row0.right
    hu hv hnextAF' hnextAG' hbatchEntries0.1 hbatchEntries0.2
  have hnextVRep := invertLincomb9_rep state.u state.v
    (updateAb state.a state.b matrix.f1 matrix.g1).f
    (updateAb state.a state.b matrix.f1 matrix.g1).g
    coeff.first coeff.second batchMatrix.row1.left batchMatrix.row1.right
    hu hv hnextBF' hnextBG' hbatchEntries1.1 hbatchEntries1.2
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
  let nextA := updateAb state.a state.b matrix.f0 matrix.g0
  let nextB := updateAb state.a state.b matrix.f1 matrix.g1
  let nextU := invertLincomb9 state.u state.v nextA.f nextA.g
  let nextV := invertLincomb9 state.u state.v nextB.f nextB.g
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

/-- The concrete final-row linear combination represents its signed abstract
coefficient. The interface takes only the four component facts needed by the
linear-combination proof, avoiding projection through a complete batch witness. -/
theorem finalCoefficient_rep (u v : PastaAsm.WideLimbs) (f g : Nat) (coeff : CoeffPair)
    (row : SignedRow)
    (hu : WideCoeffRep u coeff.first) (hv : WideCoeffRep v coeff.second)
    (hf : SignedWordRep f row.left) (hg : SignedWordRep g row.right)
    (hrow : row.norm ≤ 2^47) :
    WideCoeffRep (invertLincomb9 u v f g)
      (row.apply coeff.first coeff.second) := by
  have hentries : row.left.natAbs < 2^63 ∧ row.right.natAbs < 2^63 := by
    unfold SignedRow.norm at hrow
    constructor <;> omega
  simpa only [SignedRow.apply] using
    invertLincomb9_rep u v f g coeff.first coeff.second row.left row.right
      hu hv hf hg hentries.1 hentries.2

/-- A represented coefficient within the complete schedule bound decodes exactly
and lies in the normalizer's closed signed range. -/
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
to its closed normalization range and its `R²` congruence.  Keeping all row
expressions behind this boundary prevents the concrete driver from elaborating
the transported schedule invariant. -/
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
    (hf : SignedWordRep f matrix.row1.left)
    (hg : SignedWordRep g matrix.row1.right)
    (hrow : matrix.row1.norm ≤ 2^47) :
    let coefficient := invertLincomb9 u v f g
    coefficient.Bounded ∧
      -(coefficientRadix : Int) ≤ coefficient.toInt ∧
      coefficient.toInt ≤ coefficientRadix ∧
      (modulus : Int) ∣ (R^2 : Int) - coefficient.toInt * input := by
  dsimp only
  let coefficient := invertLincomb9 u v f g
  have hcoefficientRep := finalCoefficient_rep u v f g finish.coeff matrix.row1
    hu hv hf hg hrow
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

/-- The concrete normalization and reduction epilogue turns the schedule's signed
coefficient congruence into a canonical inverse result.  This boundary keeps the
large inversion execution out of the modular arithmetic proof. -/
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
    let normalized := normalizeCoefficient coefficient modulus
    let low := fromMont normalized.1 modulus inv
    let high1 := reduceOnce normalized.2 modulus
    let high2 := reduceOnce high1 modulus
    let high := reduceOnce high2 modulus
    let out := addMod low high modulus
    out.Bounded ∧ out.toNat < modulus.toNat ∧
      original * out.toNat ≡ R^2 [MOD modulus.toNat] := by
  dsimp only
  let normalized := normalizeCoefficient coefficient modulus
  let low := fromMont normalized.1 modulus inv
  let high1 := reduceOnce normalized.2 modulus
  let high2 := reduceOnce high1 modulus
  let high := reduceOnce high2 modulus
  let out := addMod low high modulus
  obtain ⟨hnormalizedLow, hnormalizedHighBound, hnormalizedValue, _⟩ :=
    normalizeCoefficient_schedule_spec coefficient modulus hcoefficientBound hm hp hlower hupper
  obtain ⟨hlowBound, hlowLt, hlowMod⟩ :=
    fromMont_spec normalized.1 modulus inv
      (by rw [hnormalizedLow]; exact ⟨hcoefficientBound.1, hcoefficientBound.2.1,
        hcoefficientBound.2.2.1, hcoefficientBound.2.2.2.1⟩)
      hm hshape hinvLt hinv low rfl
  obtain ⟨hhighBound, hhighLt, hhighMod⟩ :=
    reduceThree_spec normalized.2 modulus hnormalizedHighBound hm hshape
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
      normalized.1.toNat + R * normalized.2.toNat [MOD modulus.toNat] := by
    calc
      R * (low.toNat + high.toNat) = R * low.toNat + R * high.toNat := by ring
      _ ≡ normalized.1.toNat + R * high.toNat [MOD modulus.toNat] :=
        hlowMod.add_right (R * high.toNat)
      _ ≡ normalized.1.toNat + R * normalized.2.toNat [MOD modulus.toNat] :=
        Nat.ModEq.add_left normalized.1.toNat (Nat.ModEq.mul_left R hhighMod)
  have hnormalizedEq : normalized.1.toNat + R * normalized.2.toNat =
      (normalize modulus.toNat coefficient.toInt).toNat := by
    simpa only [R, splitRadix] using hnormalizedValue
  have houtScaled : R * out.toNat ≡
      (normalize modulus.toNat coefficient.toInt).toNat [MOD modulus.toNat] := by
    calc
      R * out.toNat ≡ R * (low.toNat + high.toNat) [MOD modulus.toNat] :=
        Nat.ModEq.mul_left R houtMod
      _ ≡ normalized.1.toNat + R * normalized.2.toNat [MOD modulus.toNat] := hsplitMod
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

end PastaAsm.X86_64
