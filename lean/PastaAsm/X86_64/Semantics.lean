/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.Semantics

/-!
# x86-64 instruction semantics for the Pasta Montgomery routines

This file adds only the x86-64-specific value operations used by the arithmetic and inversion
blocks. Shared word truncation, zero-flag derivation, addition, multiplication, and logical shifts
come from `PastaAsm.Semantics`: `word`, `zeroFlag`, `addc`, `mulLo`, `umulh`, `lsl`, and `lsr`.

Unlike AArch64's subtraction carry, x86-64 CF is set when subtraction borrows. `sub` passes zero
to `sbb`; `neg` sets CF exactly when its operand is nonzero. CF and OF remain independent for the
ADX instructions: the generator tracks their validity separately, and rejects a read after an
instruction invalidates the corresponding flag.

The inversion helpers additionally need bitwise word operations, 32-bit zero-extending writes,
arithmetic and double-word shifts, bit test and scan, and ZF/CF conditional moves. SF is not
consumed by these blocks, and OF from ordinary arithmetic is never consumed, so neither is given
a parallel arithmetic API here. Logical instructions' cleared CF/OF and derived ZF, and shifts'
defined CF and derived ZF, are emitted directly by the generator where live. Architecturally
undefined flags are invalidated there rather than assigned invented values. A masked-zero variable
shift has the correct no-op value; conservative invalidation is safe because no later instruction
in these blocks consumes its flags. `bsr` uses `Option` for its undefined zero-source destination.

Loads are modeled as reads of the corresponding input limb, not as memory operations. This leaves
pointer validity, register allocation, and inline-assembly operand bindings in the same external
trust boundary as the AArch64 transcription.
-/

namespace PastaAsm.X86_64

/-- `sub` and `sbb`: the low word of `a - b - borrow` and CF, which is `1` on borrow.
For bounded operands and `borrow ≤ 1`, adding `2^64` keeps the natural subtraction from
truncating; its quotient is `1` exactly when the original subtraction did not borrow. -/
def sbb (a b borrow : Nat) : Nat × Nat :=
  ((a + regMod - b - borrow) % regMod, 1 - (a + regMod - b - borrow) / regMod)

/-- `neg`: the low word of `-a` and CF. -/
def neg (a : Nat) : Nat × Nat := ((sbb 0 a 0).1, if a = 0 then 0 else 1)

/-- Truncate to the value produced by a write to a 32-bit subregister. Such a write
zero-extends into the full 64-bit register. -/
def word32 (a : Nat) : Nat := a % 2^32

/-- Bit `k` of the low 64-bit word. Instructions with register indices mask them at the call site. -/
def bit (a k : Nat) : Nat := lsr (word a) k % 2

/-- The low-word value written by 64-bit `and`. -/
def bitAnd (a b : Nat) : Nat := word (word a &&& word b)

/-- The low-word value written by 64-bit `or`. -/
def bitOr (a b : Nat) : Nat := word (word a ||| word b)

/-- The low-word value written by 64-bit `xor`. -/
def bitXor (a b : Nat) : Nat := word (word a ^^^ word b)

/-- The zero-extended value written by 32-bit `xor`. -/
def bitXor32 (a b : Nat) : Nat := word32 (word32 a ^^^ word32 b)

/-- The low-word value written by `not`; all status flags are preserved by the instruction. -/
def bitNot (a : Nat) : Nat := regMod - 1 - word a

/-- `lea dst, [src + offset]`: wrapping address arithmetic with no flag write. -/
def lea (src offset : Nat) : Nat := word (src + offset)

/-- `cmovz dst, src`: replace the destination exactly when ZF is set. -/
def cmovz (zf dst src : Nat) : Nat := if zf = 0 then dst else src

/-- `cmovnz dst, src`: replace the destination exactly when ZF is clear. -/
def cmovnz (zf dst src : Nat) : Nat := if zf = 0 then src else dst

/-- `cmovc`/`cmovb dst, src`: replace the destination exactly when CF is set. -/
def cmovc (cf dst src : Nat) : Nat := if cf = 0 then dst else src

/-- `cmovnc dst, src`: keep `dst` on borrow, replace it with `src` when CF is clear. -/
def cmovnc (cf dst src : Nat) : Nat := if cf = 0 then src else dst

/-- `setc`: materialize the low bit of CF as a byte; flags are preserved. -/
def setc (cf : Nat) : Nat := cf % 2

/-- `bt base, index`: the 64-bit register-index form masks the index to six bits and returns CF. -/
def bt (base index : Nat) : Nat := bit base (index % 64)

/-- `sar r64, count`, with sign extension from bit 63 and the architectural six-bit count mask. -/
def sar (a count : Nat) : Nat :=
  let count := count % 64
  if count = 0 then word a else
    word (lsr (word a) count + if bit a 63 = 0 then 0 else regMod - 2^(64 - count))

/-- `shld dst, src, count`. The low six count bits select the shift; a masked-zero count is a no-op. -/
def shld (dst src count : Nat) : Nat :=
  let count := count % 64
  if count = 0 then word dst else
    word (lsl (word dst) count + lsr (word src) (64 - count))

/-- `shrd dst, src, count`, with the same six-bit count mask as `shld`. -/
def shrd (dst src count : Nat) : Nat :=
  let count := count % 64
  if count = 0 then word dst else
    word (lsr (word dst) count + lsl (word src) (64 - count))

/-- `bsr r64, src`; the destination is architecturally undefined for a zero source. -/
def bsr (src : Nat) : Option Nat :=
  if word src = 0 then none else some (Nat.log2 (word src))

/-- `mulx hi, lo, src` in Intel syntax, with implicit multiplicand RDX.
The pair is in destination order, high word first; neither CF nor OF changes. -/
def mulx (rdx src : Nat) : Nat × Nat := (umulh rdx src, mulLo rdx src)

/-! ## Inversion semantics lemmas -/

/-- Every selected word bit is zero or one. -/
theorem bit_le_one (a k : Nat) : bit a k ≤ 1 := by
  simp only [bit, lsr]
  omega

/-- A 32-bit subregister write is below `2^32`. -/
theorem word32_lt (a : Nat) : word32 a < 2^32 := by
  exact Nat.mod_lt _ (Nat.two_pow_pos 32)

/-- A 32-bit exclusive-OR result is also a valid 64-bit register value. -/
theorem bitXor32_lt (a b : Nat) : bitXor32 a b < regMod := by
  exact Nat.lt_trans (word32_lt _) (by decide)

/-- `setc` always produces a bit. -/
theorem setc_le_one (cf : Nat) : setc cf ≤ 1 := by
  simp only [setc]
  omega

/-- A bit selected by `bt` is a bit. -/
theorem bt_le_one (a k : Nat) : bt a k ≤ 1 := bit_le_one _ _

/-- Every new word-valued inversion operation returns a register value. -/
theorem bitAnd_lt (a b : Nat) : bitAnd a b < regMod := word_lt _
theorem bitOr_lt (a b : Nat) : bitOr a b < regMod := word_lt _
theorem bitXor_lt (a b : Nat) : bitXor a b < regMod := word_lt _
theorem bitNot_lt (a : Nat) : bitNot a < regMod := by
  simp only [bitNot]
  have h := word_lt a
  omega
theorem sar_lt (a count : Nat) : sar a count < regMod := by
  simp only [sar]
  split <;> exact word_lt _
theorem shld_lt (dst src count : Nat) : shld dst src count < regMod := by
  simp only [shld]
  split <;> exact word_lt _
theorem shrd_lt (dst src count : Nat) : shrd dst src count < regMod := by
  simp only [shrd]
  split <;> exact word_lt _

/-- The destination of a nonzero `bsr` is a valid bit index. -/
theorem bsr_index_lt (src index : Nat) (h : bsr src = some index) : index < 64 := by
  simp only [bsr] at h
  split at h
  · contradiction
  · rename_i hne
    simp only [Option.some.injEq] at h
    subst index
    exact (Nat.log2_lt hne).2 (word_lt src)

/-- The totalized generated destination remains a register value on the undefined zero case. -/
theorem bsr_getD_lt (src : Nat) : (bsr src).getD 0 < regMod := by
  simp only [bsr]
  split
  · decide
  · rename_i hne
    exact Nat.lt_trans ((Nat.log2_lt hne).2 (word_lt src)) (by decide)

/-- Variable shift values are periodic modulo 64, matching x86-64 count masking. -/
theorem sar_add_64 (a count : Nat) : sar a (count + 64) = sar a count := by
  simp only [sar, Nat.add_mod_right]

theorem shld_add_64 (dst src count : Nat) :
    shld dst src (count + 64) = shld dst src count := by
  simp only [shld, Nat.add_mod_right]

theorem shrd_add_64 (dst src count : Nat) :
    shrd dst src (count + 64) = shrd dst src count := by
  simp only [shrd, Nat.add_mod_right]

/-- A masked-zero double shift leaves the destination value unchanged. Its flag preservation is
tracked by the instruction validator, and no inversion block reads those flags. -/
theorem shld_of_count_mod_eq_zero (dst src count : Nat) (h : count % 64 = 0) :
    shld dst src count = word dst := by
  simp only [shld, h, if_pos]

/-- Eight little-endian words, the output of the squaring block before Montgomery reduction. -/
structure WideLimbs where
  l0 : Nat
  l1 : Nat
  l2 : Nat
  l3 : Nat
  l4 : Nat
  l5 : Nat
  l6 : Nat
  l7 : Nat
  deriving DecidableEq, Repr

/-- The integer represented by the eight words. -/
def WideLimbs.toNat (x : WideLimbs) : Nat :=
  x.l0 + 2^64 * x.l1 + 2^128 * x.l2 + 2^192 * x.l3 +
    2^256 * x.l4 + 2^320 * x.l5 + 2^384 * x.l6 + 2^448 * x.l7

/-- Every word of the unreduced product is below `2^64`. -/
def WideLimbs.Bounded (x : WideLimbs) : Prop :=
  x.l0 < 2^64 ∧ x.l1 < 2^64 ∧ x.l2 < 2^64 ∧ x.l3 < 2^64 ∧
    x.l4 < 2^64 ∧ x.l5 < 2^64 ∧ x.l6 < 2^64 ∧ x.l7 < 2^64

-- Boundary cases distinguish x86-64's borrow convention from AArch64's carry convention.
example : sbb 0 0 0 = (0, 0) := by decide +kernel
example : sbb 0 0 1 = (2^64 - 1, 1) := by decide +kernel
example : sbb (2^64 - 1) (2^64 - 1) 1 = (2^64 - 1, 1) := by decide +kernel
example : neg 0 = (0, 0) := by decide +kernel
example : neg 1 = (2^64 - 1, 1) := by decide +kernel
example : mulx (2^64 - 1) 2 = (1, 2^64 - 2) := by decide +kernel
example : cmovnc 0 3 5 = 5 ∧ cmovnc 1 3 5 = 3 := by decide +kernel

-- Logical instructions derive ZF from their value; the generator records their CF/OF clearing.
example : bitOr 0 0 = 0 ∧ zeroFlag (bitOr 0 0) = 1 := by decide +kernel
example : bitXor32 (2^64 - 1) (2^32 - 1) = 0 := by decide +kernel
example : zeroFlag (bitAnd (2^63) (2^63)) = 0 := by decide +kernel

-- Conditional moves read exactly their named condition and preserve all flags.
example : cmovz 1 3 5 = 5 ∧ cmovz 0 3 5 = 3 := by decide +kernel
example : cmovnz 0 3 5 = 5 ∧ cmovnz 1 3 5 = 3 := by decide +kernel
example : cmovc 1 3 5 = 5 ∧ cmovc 0 3 5 = 3 := by decide +kernel

-- Variable counts are masked to six bits, and signed/double shifts have their word values.
example : shld 0x0123456789abcdef 0xfedcba9876543210 64 =
    0x0123456789abcdef := by decide +kernel
example : shld 0x0123456789abcdef 0xfedcba9876543210 68 =
    0x123456789abcdeff := by decide +kernel
example : shrd 0x0123456789abcdef 0xfedcba9876543210 4 =
    0x00123456789abcde := by decide +kernel
example : sar (2^64 - 1) 63 = 2^64 - 1 := by decide +kernel

-- Bit operations retain their masking and undefined-destination edge cases.
example : bt 2 65 = 1 := by decide +kernel
example : bsr 0 = none := by decide +kernel
example : bsr (2^63) = some 63 := by decide +kernel

end PastaAsm.X86_64
