/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.Compositions
import PastaAsm.Inversion
import PastaAsm.AArch64.Transcription

/-!
# The crate's Rust around the blocks

`src/lib.rs` composes the crate's `sqr_n_mul` and `from_mont` from the `square` and `mul`
blocks. These definitions mirror that Rust: the two compositions.
-/

namespace PastaAsm.AArch64

/-- `from_mont`: the multiplication block with `1` as its right operand, `value * 2^-256 mod p`.
-/
def fromMont (value modulus : Limbs) (inv : Nat) : Limbs :=
  mulMont value ⟨1, 0, 0, 0⟩ modulus inv

/-- The squaring block applied `count` times. -/
def sqrN (value modulus : Limbs) (inv : Nat) : Nat → Limbs
  | 0 => value
  | count + 1 => sqrMont (sqrN value modulus inv count) modulus inv

/-- `sqr_n_mul`: the squaring block `count` times, then the multiplication block by `rhs`. -/
def sqrNMul (value : Limbs) (count : Nat) (rhs modulus : Limbs) (inv : Nat) : Limbs :=
  mulMont (sqrN value modulus inv count) rhs modulus inv

/-- The mutable four-value state carried by the Rust inversion driver's fixed batch loop. -/
structure InvertState where
  a : Limbs
  b : Limbs
  u : PastaAsm.WideLimbs
  v : PastaAsm.WideLimbs
  deriving DecidableEq, Repr

/-- `lincomb`: `u * f + v * g` in the driver's nine-word wrapping representation. -/
def invertLincomb (u v : PastaAsm.WideLimbs) (f g : Nat) : PastaAsm.WideLimbs :=
  addWords (mulSigned u f) (mulSigned v g)

/-- One iteration of the Rust driver's `0..15` loop. -/
def invertBatch (state : InvertState) : InvertState :=
  let matrix := divsteps31 state.a state.b
  let nextA := updateAB state.a state.b matrix.f0 matrix.g0
  let nextB := updateAB state.a state.b matrix.f1 matrix.g1
  let nextU := invertLincomb state.u state.v nextA.f nextA.g
  let nextV := invertLincomb state.u state.v nextB.f nextB.g
  ⟨nextA.value, nextB.value, nextU, nextV⟩

/-- The Rust driver's public fixed-count batch loop. The inversion schedule calls this with `15`. -/
def invertBatches : Nat → InvertState → InvertState
  | 0, state => state
  | count + 1, state => invertBatches count (invertBatch state)

/-- The AArch64 Rust inversion driver: fifteen 31-step batches and one final 47-step batch. -/
def invert (value modulus : Limbs) (inv : Nat) : Limbs :=
  let initial : InvertState :=
    ⟨fromMont value modulus inv, modulus, ⟨1, 0, 0, 0, 0, 0, 0, 0, 0⟩,
      ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
  let state := invertBatches 15 initial
  let row := divsteps47 state.a.l0 state.b.l0
  let coefficient := invertLincomb state.u state.v row.f1 row.g1
  let split := normalizeCoefficient coefficient modulus
  let low := fromMont split.low modulus inv
  let high1 := reduceOnce split.high modulus
  let high2 := reduceOnce high1 modulus
  let high := reduceOnce high2 modulus
  addMod low high modulus

end PastaAsm.AArch64
