/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.Compositions
import PastaAsm.Fields
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

/-!
# Primality facts for inversion

`PastaField` records exactly the modulus shape and Montgomery facts used by the arithmetic
blocks. Those facts do not imply that an arbitrary `PastaField` has prime modulus. This module
therefore proves primality separately for the two concrete Pasta moduli and exposes
`IsInversionField`, the precise extra entry-point condition needed by inversion.

The large primality facts use Pocklington certificates. All modular powers, gcds, factorizations,
and inequalities in the certificates are checked by Lean's kernel; no native evaluation or new
axioms are used.
-/

open scoped Nat

namespace PastaAsm

namespace InversionPrimality

private structure Witness (n q : ℕ) where
  prime : q.Prime
  dvd_pred : q ∣ n - 1
  witnessBase : ℕ
  witnessResidue : ℕ
  pow_pred : (witnessBase : ZMod n) ^ (n - 1) = 1
  pow_div : (witnessBase : ZMod n) ^ ((n - 1) / q) = witnessResidue
  residue_pos : 0 < witnessResidue
  coprime : (witnessResidue - 1).Coprime n

private lemma Witness.dvd_primeDivisor_sub_one {n q : ℕ} (w : Witness n q) (hn : 1 < n)
    {r : ℕ} (hr : r.Prime) (hrn : r ∣ n) : q ∣ r - 1 := by
  have hbase : w.witnessBase.Coprime n := by
    rw [← ZMod.isUnit_iff_coprime]
    exact IsUnit.of_pow_eq_one w.pow_pred (by omega)
  let u : (ZMod r)ˣ := ZMod.unitOfCoprime w.witnessBase (hbase.of_dvd_right hrn)
  have horder_dvd : orderOf u ∣ r - 1 := by
    haveI : Fact r.Prime := ⟨hr⟩
    exact ZMod.orderOf_units_dvd_card_sub_one u
  have hq_order : q ∣ orderOf u := by
    by_contra hnot
    have hpow_pred_mod : w.witnessBase ^ (n - 1) ≡ 1 [MOD n] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      simpa only [Nat.cast_pow, Nat.cast_one] using w.pow_pred
    have horder_pred : orderOf u ∣ n - 1 := orderOf_dvd_of_pow_eq_one (by
      apply Units.ext
      simpa [u, ZMod.coe_unitOfCoprime] using
        ((ZMod.natCast_eq_natCast_iff _ _ _).2 (Nat.ModEq.of_dvd hrn hpow_pred_mod)))
    have horder_mul : orderOf u ∣ (n - 1) / q * q := by
      simpa [Nat.div_mul_cancel w.dvd_pred] using horder_pred
    have hpow : u ^ ((n - 1) / q) = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one]
      exact (Nat.Coprime.dvd_mul_right (w.prime.coprime_iff_not_dvd.mpr hnot).symm).mp
        (by simpa [Nat.mul_comm] using horder_mul)
    have hpow_div_mod : w.witnessBase ^ ((n - 1) / q) ≡ w.witnessResidue [MOD n] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      simpa only [Nat.cast_pow] using w.pow_div
    have hresidue : (w.witnessResidue : ZMod r) = 1 := by
      calc
        (w.witnessResidue : ZMod r) = w.witnessBase ^ ((n - 1) / q) := by
          symm
          simpa only [Nat.cast_pow] using
            ((ZMod.natCast_eq_natCast_iff _ _ _).2 (Nat.ModEq.of_dvd hrn hpow_div_mod))
        _ = (u ^ ((n - 1) / q) : (ZMod r)ˣ) := by
          simp [u, ZMod.coe_unitOfCoprime]
        _ = 1 := by rw [hpow]; rfl
    have hresidue_mod : w.witnessResidue ≡ 1 [MOD r] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      simpa only [Nat.cast_one] using hresidue
    have hr_residue : r ∣ w.witnessResidue - 1 :=
      (Nat.modEq_iff_dvd' (Nat.one_le_iff_ne_zero.mpr w.residue_pos.ne')).mp hresidue_mod.symm
    exact hr.ne_one (Nat.eq_one_of_dvd_coprimes w.coprime hr_residue hrn)
  exact hq_order.trans horder_dvd

private theorem prime_of_witness {n q : ℕ} (hn : 2 ≤ n) (w : Witness n q)
    (hlarge : n < q ^ 2) : n.Prime := by
  by_contra hnprime
  let r := n.minFac
  have hr : r.Prime := Nat.minFac_prime (by omega)
  have hrn : r ∣ n := Nat.minFac_dvd n
  have hr_le : r ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnprime
  have hq : q ∣ r - 1 := w.dvd_primeDivisor_sub_one (by omega) hr hrn
  have hr_pred_pos : 0 < r - 1 := Nat.sub_pos_of_lt hr.one_lt
  have hr_pred_lt : r - 1 < r := Nat.pred_lt hr.ne_zero
  have hq_lt : q < r := (Nat.le_of_dvd hr_pred_pos hq).trans_lt hr_pred_lt
  have hsquares : q ^ 2 < r ^ 2 := Nat.pow_lt_pow_left hq_lt (by omega)
  exact (not_lt_of_ge hr_le) (hlarge.trans hsquares)

private theorem prime_of_two_witnesses {n q₁ q₂ : ℕ} (hn : 2 ≤ n) (hne : q₁ ≠ q₂)
    (w₁ : Witness n q₁) (w₂ : Witness n q₂) (hlarge : n < (q₁ * q₂) ^ 2) : n.Prime := by
  by_contra hnprime
  let r := n.minFac
  have hr : r.Prime := Nat.minFac_prime (by omega)
  have hrn : r ∣ n := Nat.minFac_dvd n
  have hr_le : r ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnprime
  have hq₁ : q₁ ∣ r - 1 := w₁.dvd_primeDivisor_sub_one (by omega) hr hrn
  have hq₂ : q₂ ∣ r - 1 := w₂.dvd_primeDivisor_sub_one (by omega) hr hrn
  have hprod : q₁ * q₂ ∣ r - 1 :=
    Nat.Prime.dvd_mul_of_dvd_ne hne w₁.prime w₂.prime hq₁ hq₂
  have hr_pred_pos : 0 < r - 1 := Nat.sub_pos_of_lt hr.one_lt
  have hr_pred_lt : r - 1 < r := Nat.pred_lt hr.ne_zero
  have hprod_lt : q₁ * q₂ < r :=
    (Nat.le_of_dvd hr_pred_pos hprod).trans_lt hr_pred_lt
  have hsquares : (q₁ * q₂) ^ 2 < r ^ 2 := Nat.pow_lt_pow_left hprod_lt (by omega)
  exact (not_lt_of_ge hr_le) (hlarge.trans hsquares)

-- The leaves are small enough for `norm_num`'s kernel-checked trial-division certificates.
private theorem prime_6942563 : Nat.Prime 6942563 := by norm_num
private theorem prime_5701177 : Nat.Prime 5701177 := by norm_num
private theorem prime_4025699 : Nat.Prime 4025699 := by norm_num
private theorem prime_772231 : Nat.Prime 772231 := by norm_num
private theorem prime_413527 : Nat.Prime 413527 := by norm_num

private theorem prime_41655379 : Nat.Prime 41655379 := by
  apply prime_of_witness (by norm_num) (q := 6942563)
  · exact {
      prime := prime_6942563
      dvd_pred := by norm_num
      witnessBase := 2
      witnessResidue := 64
      pow_pred := by reduce_mod_char
      pow_div := by reduce_mod_char
      residue_pos := by norm_num
      coprime := by norm_num }
  · norm_num

private theorem prime_80513981 : Nat.Prime 80513981 := by
  apply prime_of_witness (by norm_num) (q := 4025699)
  · exact {
      prime := prime_4025699
      dvd_pred := by norm_num
      witnessBase := 2
      witnessResidue := 1048576
      pow_pred := by reduce_mod_char
      pow_div := by reduce_mod_char
      residue_pos := by norm_num
      coprime := by norm_num }
  · norm_num

private theorem prime_399082391 : Nat.Prime 399082391 := by
  apply prime_of_witness (by norm_num) (q := 5701177)
  · exact {
      prime := prime_5701177
      dvd_pred := by norm_num
      witnessBase := 2
      witnessResidue := 93074030
      pow_pred := by reduce_mod_char
      pow_div := by reduce_mod_char
      residue_pos := by norm_num
      coprime := by norm_num }
  · norm_num

private theorem prime_5239247429827 : Nat.Prime 5239247429827 := by
  apply prime_of_two_witnesses (by norm_num) (by norm_num) (q₁ := 31649) (q₂ := 12149)
  · exact {
      prime := by norm_num
      dvd_pred := by norm_num
      witnessBase := 2
      witnessResidue := 1269557927592
      pow_pred := by reduce_mod_char
      pow_div := by reduce_mod_char
      residue_pos := by norm_num
      coprime := by norm_num }
  · exact {
      prime := by norm_num
      dvd_pred := by norm_num
      witnessBase := 2
      witnessResidue := 1185373242847
      pow_pred := by reduce_mod_char
      pow_div := by reduce_mod_char
      residue_pos := by norm_num
      coprime := by norm_num }
  · norm_num

private theorem prime_325086459374267 : Nat.Prime 325086459374267 := by
  apply prime_of_two_witnesses (by norm_num) (by norm_num) (q₁ := 772231) (q₂ := 413527)
  · exact {
      prime := prime_772231
      dvd_pred := by norm_num
      witnessBase := 2
      witnessResidue := 156180095894647
      pow_pred := by reduce_mod_char
      pow_div := by reduce_mod_char
      residue_pos := by norm_num
      coprime := by norm_num }
  · exact {
      prime := prime_413527
      dvd_pred := by norm_num
      witnessBase := 2
      witnessResidue := 102008102706872
      pow_pred := by reduce_mod_char
      pow_div := by reduce_mod_char
      residue_pos := by norm_num
      coprime := by norm_num }
  · norm_num

private theorem prime_22160661629 : Nat.Prime 22160661629 := by
  apply prime_of_witness (by norm_num) (q := 41655379)
  · exact {
      prime := prime_41655379
      dvd_pred := by norm_num
      witnessBase := 2
      witnessResidue := 17216609584
      pow_pred := by reduce_mod_char
      pow_div := by reduce_mod_char
      residue_pos := by norm_num
      coprime := by norm_num }
  · norm_num

private theorem prime_5247740253619 : Nat.Prime 5247740253619 := by
  apply prime_of_witness (by norm_num) (q := 80513981)
  · exact {
      prime := prime_80513981
      dvd_pred := by norm_num
      witnessBase := 2
      witnessResidue := 93740937873
      pow_pred := by reduce_mod_char
      pow_div := by reduce_mod_char
      residue_pos := by norm_num
      coprime := by norm_num }
  · norm_num

private theorem prime_10427374428728808478656897599072717 :
    Nat.Prime 10427374428728808478656897599072717 := by
  apply prime_of_two_witnesses (by norm_num) (by norm_num)
    (q₁ := 5239247429827) (q₂ := 399082391)
  · exact {
      prime := prime_5239247429827
      dvd_pred := by norm_num
      witnessBase := 2
      witnessResidue := 3927780385925492675817601106173530
      pow_pred := by reduce_mod_char
      pow_div := by reduce_mod_char
      residue_pos := by norm_num
      coprime := by norm_num }
  · exact {
      prime := prime_399082391
      dvd_pred := by norm_num
      witnessBase := 2
      witnessResidue := 8608077744952143376646591648751451
      pow_pred := by reduce_mod_char
      pow_div := by reduce_mod_char
      residue_pos := by norm_num
      coprime := by norm_num }
  · norm_num

private theorem prime_1690502597179744445941507 : Nat.Prime 1690502597179744445941507 := by
  apply prime_of_witness (by norm_num) (q := 5247740253619)
  · exact {
      prime := prime_5247740253619
      dvd_pred := by norm_num
      witnessBase := 2
      witnessResidue := 1660222743337851280110475
      pow_pred := by reduce_mod_char
      pow_div := by reduce_mod_char
      residue_pos := by norm_num
      coprime := by norm_num }
  · norm_num

private theorem prime_8999194758858563409123804352480028797519453 :
    Nat.Prime 8999194758858563409123804352480028797519453 := by
  apply prime_of_two_witnesses (by norm_num) (by norm_num)
    (q₁ := 325086459374267) (q₂ := 22160661629)
  · exact {
      prime := prime_325086459374267
      dvd_pred := by norm_num
      witnessBase := 2
      witnessResidue := 1923835525255145170976080895073905971702885
      pow_pred := by reduce_mod_char
      pow_div := by reduce_mod_char
      residue_pos := by norm_num
      coprime := by norm_num }
  · exact {
      prime := prime_22160661629
      dvd_pred := by norm_num
      witnessBase := 2
      witnessResidue := 7468371576130240648439236849311461678235198
      pow_pred := by reduce_mod_char
      pow_div := by reduce_mod_char
      residue_pos := by norm_num
      coprime := by norm_num }
  · norm_num

private theorem prime_pallas_modulus_value :
    Nat.Prime 28948022309329048855892746252171976963363056481941560715954676764349967630337 := by
  apply prime_of_witness (by norm_num)
    (q := 8999194758858563409123804352480028797519453)
  · exact {
      prime := prime_8999194758858563409123804352480028797519453
      dvd_pred := by norm_num
      witnessBase := 2
      witnessResidue :=
        23769141747542929275130461462532321991434488634464651886715445812013527626387
      pow_pred := by reduce_mod_char
      pow_div := by reduce_mod_char
      residue_pos := by norm_num
      coprime := by norm_num }
  · norm_num

private theorem prime_vesta_modulus_value :
    Nat.Prime 28948022309329048855892746252171976963363056481941647379679742748393362948097 := by
  apply prime_of_two_witnesses (by norm_num) (by norm_num)
    (q₁ := 10427374428728808478656897599072717)
    (q₂ := 1690502597179744445941507)
  · exact {
      prime := prime_10427374428728808478656897599072717
      dvd_pred := by norm_num
      witnessBase := 2
      witnessResidue :=
        21577701278964860764616844091496499530098850519810142228219162002401576116285
      pow_pred := by reduce_mod_char
      pow_div := by reduce_mod_char
      residue_pos := by norm_num
      coprime := by norm_num }
  · exact {
      prime := prime_1690502597179744445941507
      dvd_pred := by norm_num
      witnessBase := 2
      witnessResidue :=
        10702370410624564121457417238554209300056693753982888245966960388067878619600
      pow_pred := by reduce_mod_char
      pow_div := by reduce_mod_char
      residue_pos := by norm_num
      coprime := by norm_num }
  · norm_num

end InversionPrimality

/-- The concrete Pallas base-field modulus is prime. -/
theorem pallasBase_modulus_prime : pallasBase.modulus.toNat.Prime := by
  change Nat.Prime
    28948022309329048855892746252171976963363056481941560715954676764349967630337
  exact InversionPrimality.prime_pallas_modulus_value

/-- The concrete Vesta base-field modulus is prime. -/
theorem vestaBase_modulus_prime : vestaBase.modulus.toNat.Prime := by
  change Nat.Prime
    28948022309329048855892746252171976963363056481941647379679742748393362948097
  exact InversionPrimality.prime_vesta_modulus_value

/-- Exactly the two concrete fields for which the crate's inversion entry point is intended. -/
def IsInversionField (F : PastaField) : Prop := F = pallasBase ∨ F = vestaBase

namespace IsInversionField

/-- Every supported inversion field has prime modulus. This deliberately does not hold for an
arbitrary `PastaField`, whose structure records only the facts needed by the arithmetic blocks. -/
theorem prime {F : PastaField} (hF : IsInversionField F) : F.modulus.toNat.Prime := by
  rcases hF with rfl | rfl
  · exact pallasBase_modulus_prime
  · exact vestaBase_modulus_prime

/-- A nonzero canonical natural representative is coprime to a supported inversion modulus. -/
theorem coprime_of_nonzero_of_lt {F : PastaField} (hF : IsInversionField F) {value : Limbs}
    (hne : value.toNat ≠ 0) (hlt : value.toNat < F.modulus.toNat) :
    value.toNat.Coprime F.modulus.toNat :=
  (Nat.coprime_of_lt_prime hne hlt hF.prime).symm

/-- The Boolean canonicality check used by the crate's entry points, together with nonzeroness,
implies the gcd precondition used by inversion. -/
theorem coprime_of_isCanonical {F : PastaField} (hF : IsInversionField F) (value : Limbs)
    (hv : value.Bounded) (hne : value.toNat ≠ 0)
    (hcanonical : isCanonical value F.modulus = true) :
    value.toNat.Coprime F.modulus.toNat :=
  hF.coprime_of_nonzero_of_lt hne
    ((isCanonical_iff value F.modulus hv F.bounded).mp hcanonical)

/-- The crate's selected `R²` constant is a bounded, canonical right operand for Montgomery
multiplication at either supported inversion field, and represents `R²` modulo that field. -/
theorem montgomeryR2_spec {F : PastaField} (hF : IsInversionField F) :
    (montgomeryR2 F.modulus).Bounded ∧
      (montgomeryR2 F.modulus).toNat < F.modulus.toNat ∧
      (montgomeryR2 F.modulus).l1 ≤ 2^64 - 3 ∧
      (montgomeryR2 F.modulus).l2 ≤ 2^64 - 3 ∧
      (montgomeryR2 F.modulus).l3 ≤ 2^64 - 3 ∧
      (montgomeryR2 F.modulus).toNat ≡ R^2 [MOD F.modulus.toNat] := by
  rcases hF with rfl | rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold Limbs.Bounded montgomeryR2 pallasR2
      decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · unfold Nat.ModEq
      decide +kernel
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold Limbs.Bounded montgomeryR2 vestaR2
      decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · unfold Nat.ModEq
      decide +kernel

/-- The selected `R²` constant has four 64-bit limbs. -/
theorem montgomeryR2_bounded {F : PastaField} (hF : IsInversionField F) :
    (montgomeryR2 F.modulus).Bounded :=
  hF.montgomeryR2_spec.1

/-- The selected `R²` constant is canonical. -/
theorem montgomeryR2_lt {F : PastaField} (hF : IsInversionField F) :
    (montgomeryR2 F.modulus).toNat < F.modulus.toNat :=
  hF.montgomeryR2_spec.2.1

/-- The crate's Boolean canonicality check accepts the selected `R²` constant. -/
theorem montgomeryR2_isCanonical {F : PastaField} (hF : IsInversionField F) :
    isCanonical (montgomeryR2 F.modulus) F.modulus = true :=
  (isCanonical_iff _ _ hF.montgomeryR2_bounded F.bounded).2 hF.montgomeryR2_lt

/-- Limbs 1 to 3 of the selected `R²` constant satisfy the multiplication block's right-operand
bounds. -/
theorem montgomeryR2_limb_bounds {F : PastaField} (hF : IsInversionField F) :
    (montgomeryR2 F.modulus).l1 ≤ 2^64 - 3 ∧
      (montgomeryR2 F.modulus).l2 ≤ 2^64 - 3 ∧
      (montgomeryR2 F.modulus).l3 ≤ 2^64 - 3 :=
  ⟨hF.montgomeryR2_spec.2.2.1, hF.montgomeryR2_spec.2.2.2.1,
    hF.montgomeryR2_spec.2.2.2.2.1⟩

/-- The same limb bounds in the form consumed by `mulMont_spec_of_rhs_lt`. -/
theorem montgomeryR2_mul_limb_bounds {F : PastaField} (hF : IsInversionField F) :
    (montgomeryR2 F.modulus).l1 + 3 ≤ 2^64 ∧
      (montgomeryR2 F.modulus).l2 + 3 ≤ 2^64 ∧
      (montgomeryR2 F.modulus).l3 + 3 ≤ 2^64 := by
  obtain ⟨h1, h2, h3⟩ := hF.montgomeryR2_limb_bounds
  omega

/-- The selected constant represents `R²` modulo the supported field modulus. -/
theorem montgomeryR2_modEq {F : PastaField} (hF : IsInversionField F) :
    (montgomeryR2 F.modulus).toNat ≡ R^2 [MOD F.modulus.toNat] :=
  hF.montgomeryR2_spec.2.2.2.2.2

end IsInversionField

end PastaAsm
