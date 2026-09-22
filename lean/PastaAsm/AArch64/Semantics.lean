/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.Semantics

/-!
# AArch64 instruction semantics for the Pasta arithmetic routines

The subset of AArch64 used by the crate's arithmetic and inversion inline blocks. The shared
semantics supply word truncation, multiplication, addition with carry, and immediate logical
shifts. This module adds AArch64's no-borrow subtraction convention, the word operations used by
inversion, and the carry/zero conditions consumed by `CSEL`.

Register-specified shifts use the low six bits of the shift register. The generator separately
checks the architectural encoding restrictions on immediate shifts and bitfields, so definitions
below may assume those arguments are legal at generated call sites. Loads and stores are not
modelled as memory operations: generated programs read operand limbs where assembly loads them
and return the limbs assembly stores.
-/

namespace PastaAsm.AArch64

/-- `subs` and `sbcs`: the low 64 bits of `a - b - (1 - c)` and the carry-out, where a carry of
`1` means that no borrow occurred. `subs` passes carry-in `1`. The difference is formed as
`a + 2^64 - b - (1 - c)`, which is nonnegative for in-range operands, so the quotient by `2^64`
is `1` exactly when `a ≥ b + (1 - c)`. -/
def subc (a b c : Nat) : Nat × Nat :=
  ((a + regMod - b - (1 - c)) % regMod, (a + regMod - b - (1 - c)) / regMod)

/-- `ADD` without a flag write, derived from the shared addition-with-carry primitive. -/
def add (a b : Nat) : Nat := (addc a b 0).1

/-- `SUB` without a flag write, derived from AArch64 subtraction with no incoming borrow. -/
def sub (a b : Nat) : Nat := (subc a b 1).1

/-- `NEG`, the `SUB` alias with the first operand equal to zero. -/
def neg (a : Nat) : Nat := sub 0 a

/-- AArch64 `AND` on 64-bit register values. The mnemonic is a Lean keyword, hence `bitAnd`. -/
def bitAnd (a b : Nat) : Nat := word (a &&& b)

/-- AArch64 `EOR` on 64-bit register values. -/
def eor (a b : Nat) : Nat := word (a ^^^ b)

/-- AArch64 `ORR` on 64-bit register values. -/
def orr (a b : Nat) : Nat := word (a ||| b)

/-- `ASR` by an immediate in `0..63`, with the high bits filled from bit 63. -/
def asr (a k : Nat) : Nat :=
  let a := word a
  if a < 2^63 then a / 2^k else word (a / 2^k + (regMod - 2^(64 - k)))

/-- `LSLV`: shared logical left shift with the register count masked to six bits. -/
def lslv (a k : Nat) : Nat := lsl a (k % 64)

/-- `LSRV`: shared logical right shift with the register count masked to six bits. -/
def lsrv (a k : Nat) : Nat := lsr (word a) (k % 64)

/-- `EXTR high, low, #lsb`: bits `[lsb, lsb+63]` of the concatenation `high:low`.
The immediate satisfies `lsb < 64`. -/
def extr (high low lsb : Nat) : Nat :=
  word (lsr low lsb + lsl high (64 - lsb))

/-- `UBFX`: extract `width` bits starting at `lsb` and zero-extend them. Generated calls satisfy
`0 < width` and `lsb + width ≤ 64`. -/
def ubfx (a lsb width : Nat) : Nat := word (lsr a lsb % 2^width)

/-- `SBFX`: extract `width` bits starting at `lsb` and sign-extend them to 64 bits. Generated
calls satisfy `0 < width` and `lsb + width ≤ 64`. -/
def sbfx (a lsb width : Nat) : Nat :=
  let field := ubfx a lsb width
  if field < 2^(width - 1) then field else word (field + (regMod - 2^width))

/-- `BFXIL dst, src, #lsb, #width`: replace the low `width` bits of `dst` with an extracted
field from `src`. Generated calls satisfy `0 < width` and `lsb + width ≤ 64`. -/
def bfxil (dst src lsb width : Nat) : Nat :=
  word ((dst / 2^width) * 2^width + ubfx src lsb width)

/-- `CLZ`: the number of leading zero bits in a 64-bit register value. -/
def clz (a : Nat) : Nat := if a = 0 then 64 else 63 - Nat.log2 a

/-- The two flags needed from `CMP` by the generated AArch64 inversion model. -/
structure CmpFlags where
  /-- Zero: the two operands compare equal. -/
  z : Nat
  /-- Carry: the unsigned subtraction did not borrow. -/
  c : Nat
  deriving DecidableEq, Repr

/-- `CMP a, b`: the zero and carry/no-borrow flags of `SUBS XZR, a, b`. -/
def cmp (a b : Nat) : CmpFlags :=
  let s := subc a b 1
  ⟨zeroFlag s.1, s.2⟩

/-- `csel d, x, y, lo` (also `cc`): `x` when the carry is clear, else `y`. -/
def cselLo (c x y : Nat) : Nat := if c = 0 then x else y

/-- `csel d, x, y, cs` (also `hs`): `x` when the carry is set, else `y`. -/
def cselCs (c x y : Nat) : Nat := if c = 0 then y else x

/-- `csel d, x, y, ne`: `x` when the zero flag is clear, else `y`. -/
def cselNe (z x y : Nat) : Nat := if z = 0 then x else y

/-- The zero flag produced by `cmp` is always a bit. Kept as a small opaque interface so
large generated wrapper proofs do not need to unfold the compared operands. -/
theorem cmp_z_le_one (a b : Nat) : (cmp a b).z ≤ 1 := zeroFlag_le_one _

/-! ## Bounds used by generated proof skeletons -/

/-- Every word addition result is a register value. -/
theorem add_lt (a b : Nat) : add a b < 2^64 := by
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- Every word subtraction result is a register value. -/
theorem sub_lt (a b : Nat) : sub a b < 2^64 := by
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- Every two's-complement negation is a register value. -/
theorem neg_lt (a : Nat) : neg a < 2^64 := sub_lt _ _

/-- Every bitwise AND result is a register value. -/
theorem bitAnd_lt (a b : Nat) : bitAnd a b < 2^64 := word_lt _

/-- Every bitwise exclusive-OR result is a register value. -/
theorem eor_lt (a b : Nat) : eor a b < 2^64 := word_lt _

/-- Every bitwise OR result is a register value. -/
theorem orr_lt (a b : Nat) : orr a b < 2^64 := word_lt _

/-- Every arithmetic-right-shift result is a register value. -/
theorem asr_lt (a k : Nat) : asr a k < 2^64 := by
  simp only [asr]
  split
  · exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (word_lt a)
  · exact word_lt _

/-- Every variable left shift is a register value. -/
theorem lslv_lt (a k : Nat) : lslv a k < 2^64 := by
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- Every variable right shift is a register value. -/
theorem lsrv_lt (a k : Nat) : lsrv a k < 2^64 := by
  unfold lsrv lsr
  exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (word_lt a)

/-- Every extract result is a register value. -/
theorem extr_lt (high low lsb : Nat) : extr high low lsb < 2^64 := word_lt _

/-- Every unsigned bitfield extraction is a register value. -/
theorem ubfx_lt (a lsb width : Nat) : ubfx a lsb width < 2^64 := word_lt _

/-- Every signed bitfield extraction is a register value. -/
theorem sbfx_lt (a lsb width : Nat) : sbfx a lsb width < 2^64 := by
  simp only [sbfx]
  split
  · exact ubfx_lt _ _ _
  · exact word_lt _

/-- Every bitfield insertion is a register value. -/
theorem bfxil_lt (dst src lsb width : Nat) : bfxil dst src lsb width < 2^64 := word_lt _

/-- `CLZ` returns a count from zero through 64. -/
theorem clz_le (a : Nat) : clz a ≤ 64 := by
  simp only [clz]
  split <;> omega

/-! ## Kernel-checked instruction edges -/

example : add (2^64 - 1) 1 = 0 := by decide +kernel
example : sub 0 1 = 2^64 - 1 := by decide +kernel
example : neg 1 = 2^64 - 1 := by decide +kernel
example : asr (2^64 - 1) 63 = 2^64 - 1 := by decide +kernel
example : lslv 1 65 = 2 := by decide +kernel
example : lsrv (2^64 - 1) 65 = 2^63 - 1 := by decide +kernel
example : extr 1 0 63 = 2 := by decide +kernel
example : ubfx 0xffff00000000ffff 16 32 = 0 := by decide +kernel
example : sbfx 1 0 1 = 2^64 - 1 := by decide +kernel
example : bfxil 0xffff000000000000 0x12345678 0 31 = 0xffff000012345678 := by decide +kernel
example : clz 0 = 64 ∧ clz 1 = 63 ∧ clz (2^63) = 0 := by decide +kernel
example : cmp 0 0 = ⟨1, 1⟩ ∧ cmp 0 1 = ⟨0, 0⟩ := by decide +kernel

end PastaAsm.AArch64
