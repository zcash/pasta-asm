/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.X86_64.Transcription
import PastaAsm.Compositions
import PastaAsm.Semantics.Inversion

/-!
# The x86-64 Rust around the blocks

`src/x86_64.rs` implements `square` as `square_hi(square_lo(*value), modulus, inv)`.
Its repeated-squaring loop uses the same pair, then calls the multiplication block once.
Unlike AArch64, conversion out of Montgomery form has its own transcribed assembly block.

The backend has additional debug assertions beyond the public wrappers in `src/lib.rs`:
`mul` checks a canonical right operand, and `sqr_n_mul` checks both its input and its right
operand. The contract definitions below record these checks, not correctness claims about
inputs outside them. Limb boundedness is a separate hypothesis, modeling Rust's `u64` type.
-/

namespace PastaAsm.X86_64

/-- `square`: the full eight-word product followed by Montgomery reduction. -/
def sqrMont (value modulus : Limbs) (inv : Nat) : Limbs :=
  squareHi (squareLo value) modulus inv

/-- The two squaring blocks applied `count` times. -/
def sqrN (value modulus : Limbs) (inv : Nat) : Nat → Limbs
  | 0 => value
  | count + 1 => sqrMont (sqrN value modulus inv count) modulus inv

/-- `sqr_n_mul`: the squaring pair `count` times, then the multiplication block by `rhs`. -/
def sqrNMul (value : Limbs) (count : Nat) (rhs modulus : Limbs) (inv : Nat) : Limbs :=
  mulMont (sqrN value modulus inv count) rhs modulus inv

/-- Both the public multiplication wrapper's check and the x86-64 backend's check. -/
def mulEntryContract (lhs rhs modulus : Limbs) : Bool :=
  mulContract lhs rhs modulus && isCanonical rhs modulus

/-- The x86-64 repeated-squaring entry point checks both operands, even when `count = 0`. -/
def sqrNMulEntryContract (value rhs modulus : Limbs) : Bool :=
  isCanonical value modulus && isCanonical rhs modulus

/-- A four-limb value extended with the zero fifth word used by `update_ab`'s `N = 5`
linear combination. The remaining words are irrelevant to that five-iteration loop and are zero. -/
def extendForUpdate (value : Limbs) : PastaAsm.WideLimbs :=
  ⟨value.l0, value.l1, value.l2, value.l3, 0, 0, 0, 0, 0⟩

/-- The mask, low sign bit, and magnitude with which Rust initializes `mul_signed`. -/
structure SignedScalar where
  sign : Nat
  signBit : Nat
  magnitude : Nat
  deriving DecidableEq, Repr

/-- Rust's wrapping conversion of an `i64` scalar bitpattern into its sign mask and magnitude. -/
def signedScalar (scalar : Nat) : SignedScalar :=
  let scalar := word scalar
  let sign := if scalar < 2^63 then 0 else regMod - 1
  let signBit := sign % 2
  let magnitude := word ((scalar ^^^ sign) + signBit)
  ⟨sign, signBit, magnitude⟩

/-- The generic `mul_signed` loop instantiated at `N = 5`, as `update_ab` does. Each iteration
is the corresponding generated assembly helper; the public loop state is threaded in Rust order. -/
def mulSigned5 (value : PastaAsm.WideLimbs) (scalar : Nat) : PastaAsm.WideLimbs :=
  let scalarState := signedScalar scalar
  let s0 := mulSignedLimb value.l0 scalarState.sign scalarState.signBit scalarState.magnitude 0
  let s1 := mulSignedLimb value.l1 scalarState.sign s0.negateCarry scalarState.magnitude s0.high
  let s2 := mulSignedLimb value.l2 scalarState.sign s1.negateCarry scalarState.magnitude s1.high
  let s3 := mulSignedLimb value.l3 scalarState.sign s2.negateCarry scalarState.magnitude s2.high
  let s4 := mulSignedLimb value.l4 scalarState.sign s3.negateCarry scalarState.magnitude s3.high
  ⟨s0.low, s1.low, s2.low, s3.low, s4.low, 0, 0, 0, 0⟩

/-- The generic `mul_signed` loop instantiated at `N = 9`, as coefficient updates do. -/
def mulSigned9 (value : PastaAsm.WideLimbs) (scalar : Nat) : PastaAsm.WideLimbs :=
  let scalarState := signedScalar scalar
  let s0 := mulSignedLimb value.l0 scalarState.sign scalarState.signBit scalarState.magnitude 0
  let s1 := mulSignedLimb value.l1 scalarState.sign s0.negateCarry scalarState.magnitude s0.high
  let s2 := mulSignedLimb value.l2 scalarState.sign s1.negateCarry scalarState.magnitude s1.high
  let s3 := mulSignedLimb value.l3 scalarState.sign s2.negateCarry scalarState.magnitude s2.high
  let s4 := mulSignedLimb value.l4 scalarState.sign s3.negateCarry scalarState.magnitude s3.high
  let s5 := mulSignedLimb value.l5 scalarState.sign s4.negateCarry scalarState.magnitude s4.high
  let s6 := mulSignedLimb value.l6 scalarState.sign s5.negateCarry scalarState.magnitude s5.high
  let s7 := mulSignedLimb value.l7 scalarState.sign s6.negateCarry scalarState.magnitude s6.high
  let s8 := mulSignedLimb value.l8 scalarState.sign s7.negateCarry scalarState.magnitude s7.high
  ⟨s0.low, s1.low, s2.low, s3.low, s4.low, s5.low, s6.low, s7.low, s8.low⟩

/-- The generic `add_words` loop instantiated at `N = 5`. Carry above word four is discarded. -/
def addWords5 (lhs rhs : PastaAsm.WideLimbs) : PastaAsm.WideLimbs :=
  let s0 := addWordsLimb lhs.l0 rhs.l0 0
  let s1 := addWordsLimb lhs.l1 rhs.l1 s0.carry
  let s2 := addWordsLimb lhs.l2 rhs.l2 s1.carry
  let s3 := addWordsLimb lhs.l3 rhs.l3 s2.carry
  let s4 := addWordsLimb lhs.l4 rhs.l4 s3.carry
  ⟨s0.value, s1.value, s2.value, s3.value, s4.value, 0, 0, 0, 0⟩

/-- The generic `add_words` loop instantiated at `N = 9`. Carry above word eight is discarded. -/
def addWords9 (lhs rhs : PastaAsm.WideLimbs) : PastaAsm.WideLimbs :=
  let s0 := addWordsLimb lhs.l0 rhs.l0 0
  let s1 := addWordsLimb lhs.l1 rhs.l1 s0.carry
  let s2 := addWordsLimb lhs.l2 rhs.l2 s1.carry
  let s3 := addWordsLimb lhs.l3 rhs.l3 s2.carry
  let s4 := addWordsLimb lhs.l4 rhs.l4 s3.carry
  let s5 := addWordsLimb lhs.l5 rhs.l5 s4.carry
  let s6 := addWordsLimb lhs.l6 rhs.l6 s5.carry
  let s7 := addWordsLimb lhs.l7 rhs.l7 s6.carry
  let s8 := addWordsLimb lhs.l8 rhs.l8 s7.carry
  ⟨s0.value, s1.value, s2.value, s3.value, s4.value,
    s5.value, s6.value, s7.value, s8.value⟩

/-- `lincomb::<5>` from the Rust `update_ab` path. -/
def invertLincomb5 (u v : PastaAsm.WideLimbs) (f g : Nat) : PastaAsm.WideLimbs :=
  addWords5 (mulSigned5 u f) (mulSigned5 v g)

/-- `lincomb::<9>` from the Rust coefficient-update path. -/
def invertLincomb9 (u v : PastaAsm.WideLimbs) (f g : Nat) : PastaAsm.WideLimbs :=
  addWords9 (mulSigned9 u f) (mulSigned9 v g)

/-- `update_ab`: form its five-word linear combination in Rust, then execute the generated
shift/absolute-value helper, which also applies the row's sign correction to `f` and `g`. -/
def updateAb (a b : Limbs) (f g : Nat) : UpdateAbResult :=
  updateAbShift (invertLincomb5 (extendForUpdate a) (extendForUpdate b) f g) f g

/-- The mutable four-value state carried by the Rust inversion driver's fixed batch loop. -/
structure InvertState where
  a : Limbs
  b : Limbs
  u : PastaAsm.WideLimbs
  v : PastaAsm.WideLimbs
  deriving DecidableEq, Repr

/-- One iteration of the Rust driver's `0..15` loop. -/
def invertBatch (state : InvertState) : InvertState :=
  let matrix := divsteps31 state.a state.b
  let nextA := updateAb state.a state.b matrix.f0 matrix.g0
  let nextB := updateAb state.a state.b matrix.f1 matrix.g1
  let nextU := invertLincomb9 state.u state.v nextA.f nextA.g
  let nextV := invertLincomb9 state.u state.v nextB.f nextB.g
  ⟨nextA.value, nextB.value, nextU, nextV⟩

/-- The Rust driver's public fixed-count batch loop. The inversion schedule calls this with `15`. -/
def invertBatches : Nat → InvertState → InvertState
  | 0, state => state
  | count + 1, state => invertBatches count (invertBatch state)

/-- Rust's four-word `modx = 2 * modulus`, with every word operation wrapping as `u64`. -/
def doubledModulus (modulus : Limbs) : Limbs :=
  ⟨word (2 * modulus.l0),
    word (2 * modulus.l1 + modulus.l0 / 2^63),
    word (2 * modulus.l2 + modulus.l1 / 2^63),
    word (2 * modulus.l3 + modulus.l2 / 2^63)⟩

/-- The two generated `normalize` assembly blocks composed around their Rust-computed `modx`.
The low coefficient half is unchanged; the first block corrects a negative coefficient and the
second block adds or subtracts one aligned modulus according to the remaining excess word. -/
def normalizeCoefficient (value : PastaAsm.WideLimbs) (modulus : Limbs) : Limbs × Limbs :=
  let modulus2 := doubledModulus modulus
  let first := normalizeNegative value modulus2
  let high := normalizeExcess ⟨first.h0, first.h1, first.h2, first.h3⟩ modulus2 first.excess
  (value.low, high)

/-- The x86-64 Rust inversion driver: fifteen 31-step batches and one final 47-step batch. -/
def invert (value modulus : Limbs) (inv : Nat) : Limbs :=
  let initial : InvertState :=
    ⟨fromMont value modulus inv, modulus, ⟨1, 0, 0, 0, 0, 0, 0, 0, 0⟩,
      ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
  let state := invertBatches 15 initial
  let matrix := divsteps47 state.a.l0 state.b.l0
  let coefficient := invertLincomb9 state.u state.v matrix.f1 matrix.g1
  let normalized := normalizeCoefficient coefficient modulus
  let low := fromMont normalized.1 modulus inv
  let high := reduceOnce normalized.2 modulus
  addMod low high modulus

end PastaAsm.X86_64
