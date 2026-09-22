/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.Semantics

/-!
# Shared inversion state

The Rust inversion drivers keep coefficients as nine little-endian words. These
are bit patterns, not unbounded signed integers: all coefficient operations wrap
modulo `2^576`. The last word is the sign/excess word used by normalization.
-/

namespace PastaAsm

/-- The nine-word coefficient representation used by both inversion backends. -/
structure WideLimbs where
  l0 : Nat
  l1 : Nat
  l2 : Nat
  l3 : Nat
  l4 : Nat
  l5 : Nat
  l6 : Nat
  l7 : Nat
  l8 : Nat
  deriving DecidableEq, Repr

namespace WideLimbs

/-- Unsigned interpretation of the coefficient's bit pattern. -/
def toNat (x : WideLimbs) : Nat :=
  x.l0 + 2^64 * x.l1 + 2^128 * x.l2 + 2^192 * x.l3 +
  2^256 * x.l4 + 2^320 * x.l5 + 2^384 * x.l6 + 2^448 * x.l7 + 2^512 * x.l8

/-- Every register-sized coefficient limb is in range. -/
def Bounded (x : WideLimbs) : Prop :=
  x.l0 < regMod ∧ x.l1 < regMod ∧ x.l2 < regMod ∧ x.l3 < regMod ∧
  x.l4 < regMod ∧ x.l5 < regMod ∧ x.l6 < regMod ∧ x.l7 < regMod ∧ x.l8 < regMod

/-- Truncation to the coefficient representation. -/
def ofNat (n : Nat) : WideLimbs :=
  ⟨n % regMod, n / 2^64 % regMod, n / 2^128 % regMod,
   n / 2^192 % regMod, n / 2^256 % regMod, n / 2^320 % regMod,
   n / 2^384 % regMod, n / 2^448 % regMod, n / 2^512 % regMod⟩

/-- Signed two's-complement interpretation of the stored bit pattern. -/
def toInt (x : WideLimbs) : Int :=
  if x.l8 < 2^63 then (x.toNat : Int) else (x.toNat : Int) - 2^576

/-- Low half consumed by Montgomery reduction. -/
def low (x : WideLimbs) : Limbs := ⟨x.l0, x.l1, x.l2, x.l3⟩

/-- High half before the separate sign/excess adjustment. -/
def high (x : WideLimbs) : Limbs := ⟨x.l4, x.l5, x.l6, x.l7⟩

end WideLimbs

/-- Bit patterns of the four signed 64-bit batch coefficients, in Rust field order. -/
structure InvertMatrix where
  f0 : Nat
  g0 : Nat
  f1 : Nat
  g1 : Nat
  deriving DecidableEq, Repr

end PastaAsm
