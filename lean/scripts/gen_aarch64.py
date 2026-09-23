#!/usr/bin/env python3
"""AArch64 backend for the unified Lean transcription generator.

The shared fail-closed Rust/``asm!`` parser feeds this architecture-specific
instruction emitter. It produces

- `lean/PastaAsm/AArch64/Transcription.lean`: the AArch64 blocks as Lean definitions;
- `lean/PastaAsm/AArch64/Vectors.lean`: kernel-checked AArch64 reference vectors; and
- `lean/PastaAsm/AArch64/InvertVectors.lean`: kernel-checked inversion-composition vectors
  with independently derived mathematical expectations.

Invoke it through ``python3 lean/scripts/gen.py``.

The transcription is deliberately mechanical. A block is read from its template lines, with
the operand placeholders as register names, rebound by each instruction that writes them:
the `in` and `inout` operands bind argument limbs and `inv`, the named `out` and the `inout`
operands are the result limbs, and the block ends as a routine does. The compiler's
allocation of registers to the operands is not modelled; the script checks that every
register the block reads was written by the block or bound by an operand.

A binding that nothing later reads is not emitted. For an operand this records that the
block binds a value it never uses, and the dropped binding is left as a comment; for a carry
flag it is an ordinary unread flag write. A computed register that is never read would be
dead code in the block and is reported as an error, since none is expected.

Run from the repository root:

    python3 lean/scripts/gen.py

`lean/scripts/check.sh` regenerates and fails if the output differs from the committed
files.

The script also generates the mechanical part of each block's correctness proof in
`lean/PastaAsm/AArch64/Spec.lean`: `--skeleton NAME` prints it (see `skeleton`), and
`--check-spec FILE` checks that FILE contains every block's skeleton verbatim once its
`-- BEGIN ... -- END` annotation blocks are removed; the check script runs that too.
Python 3.9+; stdlib only.
"""
import dataclasses
import re
from pathlib import Path
from typing import Dict, Optional, Sequence, Tuple

import asm_source
import gen

INLINE = Path("src/aarch64.rs")
INVERT = Path("src/aarch64/invert.rs")
VECTORS = gen.VECTORS
OUT_PROGRAM = Path("lean/PastaAsm/AArch64/Transcription.lean")
OUT_VECTORS = Path("lean/PastaAsm/AArch64/Vectors.lean")
OUT_INVERT_VECTORS = Path("lean/PastaAsm/AArch64/InvertVectors.lean")

HEADER = """/-
Copyright Supranational LLC (the routines, transcribed from Semolina v0.1.4).
Copyright (c) 2026 the pasta-asm contributors (the transcription).
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
"""

HEADER_VECTORS = gen.HEADER_VECTORS

# Code longer than this does not set the instruction-comment column (see `Routine.text`).
COMMENT_COLUMN_MAX = 40

# Blocks whose instruction stream Semolina's generator (`pasta_mul-armv8.pl`) emitted as a
# prologue, a loop body repeated a fixed number of times, and an epilogue. The body is
# transcribed once, as a function of the registers that cross its boundary; the block calls it
# once per round. `end` is the instruction that ends the prologue and each body. The rounds
# differ in one place only, which is checked: `operand`, the register holding the round's `rhs`
# limb (`{i}` is the round number), which the round takes as its parameter `param`. `roles`
# lists the registers carried from one round to the next as (register, field, description); the
# structure `state` has those fields, `value` names the ones that make up the accumulator, and
# `emit_struct` says whether this block's transcription declares the structure.
LOOPS = {
    "mulMont": dict(
        end="lsl t3,q,#62", count=3, operand="b{i}",
        round="mulMontRound", state="MulMontAcc", emit_struct=True, param="b", arg="acc",
        value=["r0", "r1", "r2", "r3", "r4"],
        roles=[("r0", "r0", "accumulator limb 0"), ("r1", "r1", "accumulator limb 1"),
               ("r2", "r2", "accumulator limb 2"), ("r3", "r3", "accumulator limb 3"),
               ("r4", "r4", "accumulator limb 4"),
               ("q", "q", "the round's Montgomery quotient `q`"),
               ("t1", "t1", "`low(p1 * q)`, the first term of the round's reduction"),
               ("t3", "t3", "`low(q * 2^62)`, the third term of the round's reduction")]),
}

# The inline `asm!` blocks of the crate: the function whose block to read, the Lean name, the
# docstring, and the argument names in signature order. The block's template lines are the
# instruction stream; its `in` and `inout` operands bind the arguments (`lhs[0]` is `lhs.l0`,
# `inv` is `inv`, and a `let mut a0 = value[0];` before the block makes the `inout` operand
# `a0` the limb `value.l0`), and its named `out` and its `inout` operands are the result limbs.
INLINE_ROUTINES = [
    ("mul", "mulMont",
     "The inline `asm!` block of `mul`: Montgomery multiplication, `lhs * rhs * 2^-256 mod p`, "
     "with the result in the block's output operands. Its rounds are those of Semolina's "
     "`mul_mont_pasta`; its epilogue keeps four limbs of the final candidate.",
     ["lhs", "rhs", "modulus"]),
    ("square", "sqrMont",
     "The inline `asm!` block of `square`: Montgomery squaring, `value^2 * 2^-256 mod p`, the "
     "squaring loop body of Semolina's `sqr_n_mul_mont_pasta` followed by a conditional "
     "subtraction, with the result in the block's `inout` operands.",
     ["value", "modulus"]),
    ("add", "addMod",
     "The inline `asm!` block of `add`: modular addition, `lhs + rhs mod p`, as a full-width "
     "addition, a subtraction of the modulus, and the selection of the reduced sum when that "
     "subtraction did not borrow, with the result in the block's `inout` operands.",
     ["lhs", "rhs", "modulus"]),
    ("sub", "subMod",
     "The inline `asm!` block of `sub`: modular subtraction, `lhs - rhs mod p`, as a full-width "
     "subtraction and the addition of the modulus when it borrowed, with the result in the "
     "block's `inout` operands.",
     ["lhs", "rhs", "modulus"]),
]


@dataclasses.dataclass(frozen=True)
class InvertRoutineConfig:
    rust_name: str
    lean_name: str
    signature: str
    regions: Tuple[Tuple[str, str], ...]
    args: Tuple[Tuple[str, str], ...]
    result_type: str
    result_fields: Tuple[str, ...]
    doc: str
    loop_count: Optional[int] = None
    local_inputs: Tuple[Tuple[str, str], ...] = ()


D = asm_source.Declaration


INVERT_DECLARATIONS = {
    "divsteps_31": (
        *(D(name, "inout", name, "_") for name in
          ("a0", "a1", "a2", "a3", "b0", "b1", "b2", "b3")),
        D("fg0", "inout", "0x7fff_ffff_8000_0000_u64", "_"),
        D("fg1", "inout", "0x8000_0000_7fff_ffff_u64", "_"),
        D("bias", "inout", "0x7fff_ffff_7fff_ffff_u64", "_"),
        D("cnt", "inout", "31_u64", "_"),
        *(D(name, "out", name, name) for name in ("f0", "g0", "f1", "g1")),
        *(D(name, "out", "_", "_") for name in ("t0", "t1", "t2", "t3")),
    ),
    "update_ab": (
        *(D(name, "inout", name, name) for name in ("a0", "a1", "a2", "a3")),
        *(D(name, "inout", name, "_") for name in ("b0", "b1", "b2", "b3")),
        D("f", "inout", "f", "f"), D("g", "inout", "g", "g"),
        *(D(name, "out", "_", "_") for name in
          ("t0", "t1", "t2", "t3", "t4", "t5", "t6")),
    ),
    "add_words": (
        *(D(f"o{i}", "inout", f"lhs[{i}]", f"o{i}") for i in range(9)),
        *(D(f"r{i}", "in", f"rhs[{i}]", None) for i in range(9)),
    ),
    "mul_signed": (
        D("scalar", "in", "scalar", None),
        *(D(f"o{i}", "inout", f"value[{i}]", f"o{i}") for i in range(9)),
        *(D(name, "out", "_", "_") for name in ("sign", "mag", "carry", "hi")),
    ),
    "divsteps_47": (
        D("a", "inout", "a", "_"), D("b", "inout", "b", "_"),
        D("cnt", "inout", "47_u64", "_"),
        D("f0", "inout", "1_i64", "_"), D("g0", "inout", "0_i64", "_"),
        D("f1", "inout", "0_i64", "f1"), D("g1", "inout", "1_i64", "g1"),
        *(D(name, "out", "_", "_") for name in ("odd", "t0", "t1", "t2")),
    ),
    "normalize_coefficient": (
        D("p0", "in", "modulus[0]", None), D("p1", "in", "modulus[1]", None),
        *(D(f"w{i}", "inout", f"value[{i}]", f"w{i}") for i in range(4, 8)),
        D("w8", "inout", "value[8]", "_"),
        *(D(name, "out", "_", "_") for name in
          ("sign", "excess", "m4", "m5", "m6", "m7", "tmp")),
    ),
    "redc": (
        *(D(f"r{i}", "inout", f"r{i}", f"r{i}") for i in range(4)),
        *(D(f"h{i}", "in", f"high[{i}]", None) for i in range(4)),
        *(D(f"p{i}", "in", f"modulus[{i}]", None) for i in range(4)),
        D("inv", "in", "inv", None),
        *(D(name, "out", "_", "_") for name in ("q", "r4", "t0", "t1", "t2", "t3")),
    ),
    "reduce_once": (
        *(D(f"r{i}", "inout", f"value[{i}]", f"value[{i}]") for i in range(4)),
        *(D(f"p{i}", "in", f"modulus[{i}]", None) for i in range(4)),
        *(D(f"t{i}", "out", "_", "_") for i in range(4)),
    ),
}


INVERT_ROUTINES = (
    InvertRoutineConfig(
        "divsteps_31", "divsteps31",
        "fn divsteps_31(a: &Limbs, b: &Limbs) -> Matrix",
        (("before asm", """
            let [a0, a1, a2, a3] = *a;
            let [b0, b1, b2, b3] = *b;
            let (f0, g0, f1, g1): (i64, i64, i64, i64);
            unsafe {
        """), ("after asm", "; } Matrix { f0, g0, f1, g1 }")),
        (("a", "Limbs"), ("b", "Limbs")), "InvertMatrix", ("f0", "g0", "f1", "g1"),
        "The 31-step approximation helper, including its checked fixed-count inner loop. "
        "Signed matrix entries are represented by their 64-bit register bitpatterns.",
        loop_count=31,
        local_inputs=(("a0", "a.l0"), ("a1", "a.l1"), ("a2", "a.l2"), ("a3", "a.l3"),
                      ("b0", "b.l0"), ("b1", "b.l1"), ("b2", "b.l2"), ("b3", "b.l3")),
    ),
    InvertRoutineConfig(
        "update_ab", "updateAB",
        "fn update_ab(a: &Limbs, b: &Limbs, mut f: i64, mut g: i64) -> (Limbs, i64, i64)",
        (("before asm", """
            let [mut a0, mut a1, mut a2, mut a3] = *a;
            let [b0, b1, b2, b3] = *b;
            unsafe {
        """), ("after asm", "; } ([a0, a1, a2, a3], f, g)")),
        (("a", "Limbs"), ("b", "Limbs"), ("f", "Nat"), ("g", "Nat")),
        "UpdateABResult", ("a0", "a1", "a2", "a3", "f", "g"),
        "The signed fixed-width matrix-row update of one GCD state, shifted by 31 bits.",
        local_inputs=(("a0", "a.l0"), ("a1", "a.l1"), ("a2", "a.l2"), ("a3", "a.l3"),
                      ("b0", "b.l0"), ("b1", "b.l1"), ("b2", "b.l2"), ("b3", "b.l3")),
    ),
    InvertRoutineConfig(
        "add_words", "addWords",
        "fn add_words(lhs: &Wide, rhs: &Wide) -> Wide",
        (("before asm", """
            let (o0, o1, o2, o3, o4, o5, o6, o7, o8):
              (u64, u64, u64, u64, u64, u64, u64, u64, u64);
            unsafe {
        """), ("after asm", "; } [o0, o1, o2, o3, o4, o5, o6, o7, o8]")),
        (("lhs", "WideLimbs"), ("rhs", "WideLimbs")), "WideLimbs",
        tuple(f"o{i}" for i in range(9)),
        "Addition of two nine-word coefficient bitpatterns modulo 2^576.",
    ),
    InvertRoutineConfig(
        "mul_signed", "mulSigned",
        "fn mul_signed(value: &Wide, scalar: i64) -> Wide",
        (("before asm", """
            let (o0, o1, o2, o3, o4, o5, o6, o7, o8):
              (u64, u64, u64, u64, u64, u64, u64, u64, u64);
            unsafe {
        """), ("after asm", "; } [o0, o1, o2, o3, o4, o5, o6, o7, o8]")),
        (("value", "WideLimbs"), ("scalar", "Nat")), "WideLimbs",
        tuple(f"o{i}" for i in range(9)),
        "Multiplication of a nine-word signed bitpattern by a signed scalar bitpattern modulo 2^576.",
    ),
    InvertRoutineConfig(
        "divsteps_47", "divsteps47",
        "fn divsteps_47(a: u64, b: u64) -> (i64, i64)",
        (("before asm", "let (f1, g1): (i64, i64); unsafe {"),
         ("after asm", "; } (f1, g1)")),
        (("a", "Nat"), ("b", "Nat")), "InvertRow", ("f1", "g1"),
        "The second transition row after the checked fixed-count final 47 low-limb steps.",
        loop_count=47,
    ),
    InvertRoutineConfig(
        "normalize_coefficient", "normalizeCoefficient",
        "fn normalize_coefficient(value: &Wide, modulus: &Limbs) -> (Limbs, Limbs)",
        (("before asm", """
            let low = [value[0], value[1], value[2], value[3]];
            let (w4, w5, w6, w7): (u64, u64, u64, u64);
            unsafe {
        """), ("after asm", "; } (low, [w4, w5, w6, w7])")),
        (("value", "WideLimbs"), ("modulus", "Limbs")), "CoefficientSplit",
        ("w4", "w5", "w6", "w7"),
        "The final signed coefficient adjustment; the low half is unchanged and the adjusted high half is returned.",
    ),
    InvertRoutineConfig(
        "redc", "redcMont",
        "fn redc(low: &Limbs, high: &Limbs, modulus: &Limbs, inv: u64) -> Limbs",
        (("before asm", """
            let (mut r0, mut r1, mut r2, mut r3) = (low[0], low[1], low[2], low[3]);
            unsafe {
        """), ("after asm", "; } [r0, r1, r2, r3]")),
        (("low", "Limbs"), ("high", "Limbs"), ("modulus", "Limbs"), ("inv", "Nat")),
        "Limbs", ("r0", "r1", "r2", "r3"),
        "Semolina's full 512-bit Montgomery reduction: four low-half cancellation rounds, "
        "addition of the high half, and one five-limb conditional subtraction.",
        local_inputs=(("r0", "low.l0"), ("r1", "low.l1"),
                      ("r2", "low.l2"), ("r3", "low.l3")),
    ),
    InvertRoutineConfig(
        "reduce_once", "reduceOnce",
        "fn reduce_once(mut value: Limbs, modulus: &Limbs) -> Limbs",
        (("before asm", "unsafe {"), ("after asm", "; } value")),
        (("value", "Limbs"), ("modulus", "Limbs")), "Limbs", ("r0", "r1", "r2", "r3"),
        "One conditional subtraction of the modulus from a value known to be below twice it.",
    ),
)

def tokenize(rest):
    return re.findall(r"\[[^\]]*\]!?|[^,\s]+", rest)


def imm(tok):
    """An immediate operand such as `#62` or `8*1`, as an integer."""
    s = tok.lstrip("#")
    if re.fullmatch(r"0x[0-9a-fA-F]+", s):
        return int(s, 16)
    if not re.fullmatch(r"-?[0-9]+(\*[0-9]+)?", s):
        raise ValueError(f"unexpected immediate {tok}")
    return eval(s)


def shift_imm(tok, instruction):
    value = imm(tok)
    if not 0 <= value < 64:
        raise ValueError(f"shift immediate outside 0..63: {instruction}")
    return value


def bitfield_imms(lsb_token, width_token, instruction):
    lsb, width = imm(lsb_token), imm(width_token)
    if lsb < 0 or width <= 0 or lsb + width > 64:
        raise ValueError(f"invalid bitfield range: {instruction}")
    return lsb, width


class Emitter(gen.Emitter):
    """AArch64 instruction decoder backed by the shared binding and liveness IR."""

    def __init__(self, ins, directions=None):
        super().__init__()
        self.ins = ins
        self.directions = directions or {}
        self.zero_condition_valid = False

    def read(self, tok):
        if tok == "xzr":
            return "0"
        if tok.startswith("#"):
            return str(imm(tok))
        if tok not in self.known:
            raise ValueError(f"{tok} read before being written")
        self.cur_reads.add(tok)
        return tok

    def shifted(self, tokens, start, instruction):
        """Read one register operand and its optional AArch64 shift modifier."""
        value = self.read(tokens[start])
        remaining = tokens[start + 1:]
        if not remaining:
            return value
        if len(remaining) != 2 or remaining[0] not in ("asr", "lsl", "lsr"):
            raise ValueError(f"unsupported shifted operand: {' '.join(tokens[start:])}")
        shift = shift_imm(remaining[1], instruction)
        semantics = {"asr": "asr", "lsl": "lsl", "lsr": "lsr"}[remaining[0]]
        return f"({semantics} {value} {shift})"

    def bind(self, name, expr, comment, reads=None, load=False, fact=None, note=None):
        if name != "xzr":
            super().bind(name, expr, comment, reads=reads, load=load, fact=fact, note=note)

    def step(self, op, t, text):
        fixed_arity = {
            "mov": 2, "mul": 3, "umulh": 3, "lsl": 3, "lsr": 3,
            "asr": 3, "lslv": 3, "lsrv": 3, "neg": 2, "eor": 3,
            "clz": 2, "extr": 4, "sbfx": 4, "ubfx": 4, "bfxil": 4,
            "cmp": 2, "csel": 4,
        }
        variable_arity = {"add": (3, 5), "sub": (3, 5), "and": (3, 5),
                          "orr": (3, 5), "adds": (3, 5), "adcs": (3, 5),
                          "adc": (3, 5), "subs": (3, 5), "sbcs": (3, 5)}
        if op in fixed_arity and len(t) != fixed_arity[op]:
            raise ValueError(f"{op} expects {fixed_arity[op]} operands, got {len(t)}: {text}")
        if op in variable_arity and len(t) not in variable_arity[op]:
            expected = " or ".join(str(n) for n in variable_arity[op])
            raise ValueError(f"{op} expects {expected} operands, got {len(t)}: {text}")
        if op not in fixed_arity and op not in variable_arity:
            raise ValueError(f"unhandled instruction: {text}")
        if op != "cmp" and t[0] != "xzr":
            if self.directions.get(t[0]) == "in":
                raise ValueError(f"input-only register {t[0]} cannot be written: {text}")
            if t[0] not in self.directions:
                raise ValueError(f"undeclared destination {t[0]}: {text}")
        self.cur_reads = set()
        if op == "mov":
            a = self.read(t[1])
            self.bind(t[0], a, text, fact=("mov", a))
        elif op == "mul":
            a, b = self.read(t[1]), self.read(t[2])
            self.bind(t[0], f"mulLo {a} {b}", text, fact=("mul", a, b))
        elif op == "umulh":
            a, b = self.read(t[1]), self.read(t[2])
            self.bind(t[0], f"umulh {a} {b}", text, fact=("umulh", a, b))
        elif op in ("lsl", "lsr", "asr"):
            a, k = self.read(t[1]), shift_imm(t[2], text)
            semantics = {"lsl": "lsl", "lsr": "lsr", "asr": "asr"}[op]
            self.bind(t[0], f"{semantics} {a} {k}", text, fact=(op, a, k))
        elif op in ("lslv", "lsrv"):
            a, k = self.read(t[1]), self.read(t[2])
            self.bind(t[0], f"{op} {a} {k}", text, fact=(op, a, k))
        elif op in ("add", "sub", "and", "orr"):
            a, b = self.read(t[1]), self.shifted(t, 2, text)
            semantics = {"add": "add", "sub": "sub", "and": "bitAnd", "orr": "orr"}[op]
            self.bind(t[0], f"{semantics} {a} {b}", text, fact=(op, a, b))
        elif op == "eor":
            a, b = self.read(t[1]), self.read(t[2])
            self.bind(t[0], f"eor {a} {b}", text, fact=("eor", a, b))
        elif op == "neg":
            a = self.read(t[1])
            self.bind(t[0], f"neg {a}", text, fact=("neg", a))
        elif op == "clz":
            a = self.read(t[1])
            self.bind(t[0], f"clz {a}", text, fact=("clz", a))
        elif op == "extr":
            hi, lo, k = self.read(t[1]), self.read(t[2]), shift_imm(t[3], text)
            self.bind(t[0], f"extr {hi} {lo} {k}", text, fact=("extr", hi, lo, k))
        elif op in ("sbfx", "ubfx"):
            a = self.read(t[1])
            start, width = bitfield_imms(t[2], t[3], text)
            self.bind(t[0], f"{op} {a} {start} {width}", text,
                      fact=(op, a, start, width))
        elif op == "bfxil":
            old, src = self.read(t[0]), self.read(t[1])
            start, width = bitfield_imms(t[2], t[3], text)
            self.bind(t[0], f"bfxil {old} {src} {start} {width}", text,
                      fact=("bfxil", old, src, start, width))
        elif op in ("adds", "adcs", "adc"):
            cin = "0" if op == "adds" else self.read("c")
            a, b = self.read(t[1]), self.shifted(t, 2, text)
            expr = f"addc {a} {b} {cin}"
            self.zero_condition_valid = False
            if op == "adc":
                self.bind(t[0], f"({expr}).1", text, fact=("adc", a, b, cin))
            else:
                self.bind("s", expr, text, fact=("adds", a, b, cin))
                self.bind(t[0], "s.1", text, reads=("s",), fact=("fst",), note=f"  `-> {t[0]}")
                self.bind("c", "s.2", text, reads=("s",), fact=("snd",), note="  `-> carry")
        elif op in ("subs", "sbcs"):
            cin = "1" if op == "subs" else self.read("c")
            a, b = self.read(t[1]), self.shifted(t, 2, text)
            expr = f"subc {a} {b} {cin}"
            self.zero_condition_valid = False
            if t[0] == "xzr":
                self.bind("c", f"({expr}).2", text, fact=("subs_carry", a, b, cin))
            else:
                self.bind("s", expr, text, fact=("subs", a, b, cin))
                self.bind(t[0], "s.1", text, reads=("s",), fact=("fst",), note=f"  `-> {t[0]}")
                self.bind("c", "s.2", text, reads=("s",), fact=("snd",), note="  `-> carry")
        elif op == "cmp":
            a, b = self.read(t[0]), self.read(t[1])
            self.bind("z", f"(cmp {a} {b}).z", text, fact=("cmp", a, b))
            self.zero_condition_valid = True
        elif op == "csel":
            a, b = self.read(t[1]), self.read(t[2])
            if t[3] in ("lo", "cc"):
                c = self.read("c")
                self.bind(t[0], f"cselLo {c} {a} {b}", text, fact=("select", c, a, b))
            elif t[3] in ("cs", "hs"):
                c = self.read("c")
                self.bind(t[0], f"cselCs {c} {a} {b}", text, fact=("select", c, b, a))
            elif t[3] == "ne":
                if not self.zero_condition_valid:
                    raise ValueError(f"NE condition read before cmp: {text}")
                z = self.read("z")
                self.bind(t[0], f"cselNe {z} {a} {b}", text, fact=("select", z, a, b))
            else:
                raise ValueError(f"unexpected condition: {text}")

    def run(self, start, end=None):
        pc = start
        end = len(self.ins) if end is None else end
        while pc < end:
            op, tokens, text = self.ins[pc]
            if op == "ret":
                self.end_pc = pc
                return
            if op.endswith(":") or op in ("cbnz",):
                raise ValueError(f"control flow must be factored before emission: {text}")
            self.pc = pc
            self.step(op, tokens, text)
            pc += 1
        self.end_pc = pc


# Fields of the argument structures, by argument name, for the skeleton's bound hypotheses.
LIMB_FIELDS = ["l0", "l1", "l2", "l3"]
ARG_FIELDS = {arg: LIMB_FIELDS for arg in ("t", "lhs", "rhs", "value", "modulus")}


def loop_routines(e, ins, name, doc, args, result, cfg):
    """Split the transcription of a routine that the assembly's generator emitted as prologue,
    repeated body, and epilogue (see `LOOPS`): the body becomes its own definition over the
    registers that cross its boundary, and the routine calls it once per round."""
    first_pc = min(en["pc"] for en in e.entries if en["pc"] is not None)
    ends = [p for p in range(first_pc, e.end_pc) if ins[p][2] == cfg["end"]]
    if len(ends) != cfg["count"] + 1:
        raise ValueError(f"{name}: expected {cfg['count'] + 1} `{cfg['end']}`, found {len(ends)}")
    count = cfg["count"]
    template = cfg["operand"]
    varying = [None] + [template.format(i=k) for k in range(1, count + 1)]
    bodies = []
    for k in range(1, count + 1):
        texts = [ins[p][2] for p in range(ends[k - 1] + 1, ends[k] + 1)]
        texts = [re.sub(rf"\b{re.escape(varying[k])}\b", varying[1], t) for t in texts]
        bodies.append(texts)
    if any(b != bodies[0] for b in bodies):
        raise ValueError(f"{name}: the round bodies differ beyond `{varying[1]}`")

    def part(en):
        pc = en["pc"]
        if pc is None or pc <= ends[0]:
            return "prologue"
        for k in range(1, count + 1):
            if ends[k - 1] < pc <= ends[k]:
                return ("body", k)
        return "epilogue"

    prologue = [en for en in e.entries if part(en) == "prologue"]
    body = [en for en in e.entries if part(en) == ("body", 1)]
    after = [en for en in e.entries if part(en) not in ("prologue", ("body", 1))]
    # The register holding the round's `rhs` limb: the operand.
    loaded = varying[1]
    body_entries = body
    # Registers the body reads before writing (its inputs), and registers it writes that a
    # later instruction reads before they are written again (its outputs).
    bound, live_in = set(), []
    for en in body_entries:
        for r in sorted(en["reads"]):
            if r not in bound and r not in live_in and r != loaded:
                live_in.append(r)
        bound.add(en["name"])
    rebound, live_out = set(), []
    for en in after:
        for r in sorted(en["reads"]):
            if r in bound and r not in rebound and r not in live_out:
                live_out.append(r)
        rebound.add(en["name"])
    regs = [r for r, _, _ in cfg["roles"]]
    fields = [f for _, f, _ in cfg["roles"]]
    if sorted(live_out) != sorted(regs):
        raise ValueError(f"{name}: registers carried between rounds are {sorted(live_out)}, "
                         f"`roles` lists {sorted(regs)}")
    # An input is an invariant argument if its value on entry is an argument limb or `inv`;
    # otherwise it is carried state.
    defs = {}
    for en in prologue:
        defs[en["name"]] = en
    invariant, carried = [], []
    for r in live_in:
        d = defs[r]
        if d["fact"][0] in ("load", "inv"):
            invariant.append((r, d))
        else:
            carried.append(r)
    if sorted(carried) != sorted(regs):
        raise ValueError(f"{name}: registers read from the previous round are {sorted(carried)}, "
                         f"`roles` lists {sorted(regs)}")
    limb_args = [arg for arg in args if any(d["fact"][0] == "load" and d["fact"][1] == arg
                                            for _, d in invariant)]
    uses_inv = any(d["fact"][0] == "inv" for _, d in invariant)
    param, sarg = cfg["param"], cfg["arg"]
    # The round: its inputs bound as arguments, then the body.
    re_ = Emitter(ins)
    order = {arg: i for i, arg in enumerate(limb_args)}

    def key(rd):
        d = rd[1]
        return (0, order[d["fact"][1]], d["fact"][2]) if d["fact"][0] == "load" else (1, 0, "")

    for r, d in sorted(invariant, key=key):
        re_.bind(r, d["expr"], "argument", reads=(), load=(d["fact"][0] == "load"), fact=d["fact"])
    re_.bind(loaded, param, "argument", reads=(), fact=("param", param))
    for r, f in zip(regs, fields):
        re_.bind(r, f"{sarg}.{f}", "argument", reads=(), load=True, fact=("load", sarg, f))
    re_.entries += [dict(en) for en in body_entries]
    re_.cur_reads = set()
    round_result = [re_.read(r) for r in regs]
    sig = (f"def {cfg['round']} ({' '.join(limb_args)} : Limbs) "
           f"({'inv ' if uses_inv else ''}{param} : Nat) "
           f"({sarg} : {cfg['state']}) : {cfg['state']} :=")
    where = f"the instructions between one `{cfg['end']}` and the next"
    round_doc = (f"One round of `{name}`: {where} in each of its {count} rounds, on the "
                 f"round's `rhs` limb `{param}` and the registers `{sarg}` carried from the "
                 "previous round.")
    struct = None
    if cfg["emit_struct"]:
        value = cfg["value"]
        lines = [f"/-- The registers that `{name}` carries from one round to the next. -/",
                 f"structure {cfg['state']} where"]
        for _, f, desc in cfg["roles"]:
            lines += [f"  /-- {desc} -/", f"  {f} : Nat"]
        lines += ["  deriving DecidableEq, Repr", "", f"namespace {cfg['state']}", "",
                  "/-- Every field is below `2^64`. -/",
                  f"def Bounded (s : {cfg['state']}) : Prop :="]
        lines += wrap_tactic("", [f"s.{f} < 2^64" + (" ∧" if i < len(fields) - 1 else "")
                                  for i, f in enumerate(fields)], "", indent="  ")
        lines += ["", f"/-- The accumulator's value: limbs `{'`, `'.join(value)}` with weights "
                  f"`2^0` to `2^{64 * (len(value) - 1)}`. -/",
                  f"def toNat (s : {cfg['state']}) : Nat :="]
        terms = [f"{'2^%d * ' % (64 * i) if i else ''}s.{f}" for i, f in enumerate(value)]
        lines += wrap_tactic("", [t + (" +" if i < len(value) - 1 else "")
                                  for i, t in enumerate(terms)], "", indent="  ")
        lines += ["", f"end {cfg['state']}", ""]
        struct = "\n".join(lines)
    rnd = Routine(round_doc, sig, re_.render(round_result), f"  ⟨{', '.join(round_result)}⟩",
                  cfg["round"], re_, round_result, struct=struct,
                  arg_fields={sarg: fields})
    # The block: prologue, then per round the call and the outputs.
    me = Emitter(ins)
    me.entries = [dict(en) for en in prologue]
    inv_regs = [r for r, _ in invariant if defs[r]["fact"][0] == "inv"]
    n_scalar = len(inv_regs) + 1
    fmt = (f"{cfg['round']} {' '.join(limb_args)} " + " ".join("{%d}" % i for i in range(n_scalar))
           + " ⟨" + ", ".join("{%d}" % (n_scalar + i) for i in range(len(regs))) + "⟩")
    for k in range(1, count + 1):
        call_regs = inv_regs + [varying[k]] + regs
        rname = f"round{k}"
        me.entries.append(dict(name=rname, expr=fmt.format(*call_regs), comment=f"round {k}",
                               reads=set(call_regs), load=False, fact=("call", fmt, call_regs),
                               pc=None))
        for r, f in zip(regs, fields):
            me.entries.append(dict(name=r, expr=f"{rname}.{f}", comment=f"round {k} output",
                                   reads={rname}, load=False, fact=("callout", rname, f), pc=None))
    me.entries += [dict(en) for en in e.entries if part(en) == "epilogue"]
    main = Routine(doc, f"def {name} ({' '.join(args)} : Limbs) (inv : Nat) : Limbs :=",
                   me.render(result), f"  ⟨{', '.join(result)}⟩", name, me, result)
    return [rnd, main]


def instruction_ir(templates):
    """Normalize parsed AArch64 templates to the backend's token representation."""
    ins = []
    for template in templates:
        text = re.sub(r"\{(\w+)\}", r"\1", template)
        text = re.sub(r"\s+", " ", text.replace(", ", ",")).strip()
        match = re.match(r"(\S+)\s*(.*)", text)
        ins.append((match.group(1), tokenize(match.group(2)), text))
    return ins


def parse_inline(path, fn, args):
    """Adapt the shared Rust asm parser to the AArch64 emitter's instruction representation."""
    rust_args = args + (["inv"] if fn in ("mul", "square") else [])
    parsed = asm_source.parse_function(
        path.read_text(), fn, rust_args, 4,
        allowed_options={"pure", "nomem", "nostack"},
        required_options={"pure", "nomem", "nostack"},
    )
    ins = instruction_ir(parsed.instructions) + [("ret", [], "ret")]
    asm_source.declaration_directions(parsed, fn)
    outputs = asm_source.output_bindings(parsed, fn)
    returned = asm_source.returned_registers(parsed, fn)
    decls = [(decl.name, decl.kind, decl.value) for decl in parsed.declarations]
    return ins, decls, parsed.locals, outputs, returned


def emit_inline(fn, name, doc, args):
    ins, decls, lets, named_outputs, returned = parse_inline(INLINE, fn, args)
    e = Emitter(ins, {n: kind for n, kind, _ in decls})
    outs = []
    for n, kind, v in decls:
        if kind in ("in", "inout"):
            m = re.fullmatch(r"(\w+)\[(\d)\]", v)
            if m:
                arg, i = m.group(1), m.group(2)
            elif v in lets:
                arg, i = lets[v][0], str(lets[v][1])
            elif v == "inv":
                e.bind(n, "inv", "argument", reads=(), fact=("inv",))
                continue
            else:
                raise ValueError(f"{name}: unexpected input operand {n} = {v}")
            if arg not in args:
                raise ValueError(f"{name}: operand {n} reads {v}, not an argument")
            e.bind(n, f"{arg}.l{i}", "argument", reads=(), load=True, fact=("load", arg, f"l{i}"))
            if kind == "inout":
                outs.append((n, n))
        elif kind == "out":
            if v != "_":
                if named_outputs.get(v) != n:
                    raise ValueError(f"{name}: output binding {v} does not name operand {n}")
                outs.append((v, n))
        else:
            raise ValueError(f"{name}: unsupported operand direction {kind}")
    ordered_outputs = tuple(reg for _, reg in sorted(outs))
    if ordered_outputs != returned:
        raise ValueError(
            f"{name}: source output order {returned} differs from legacy order {ordered_outputs}"
        )
    e.run(0)
    e.cur_reads = set()
    result = [e.read(reg) for reg in ordered_outputs]
    if len(result) != 4:
        raise ValueError(f"{name}: {len(result)} output operands")
    if name in LOOPS:
        return loop_routines(e, ins, name, doc, args, result, LOOPS[name])
    uses_inv = any(kind in ("in", "inout") and v == "inv" for _, kind, v in decls)
    return [Routine(doc, f"def {name} ({' '.join(args)} : Limbs){' (inv : Nat)' if uses_inv else ''} : Limbs :=",
                    e.render(result), f"  ⟨{', '.join(result)}⟩", name, e, result)]


def parse_word_literal(value):
    """A Rust u64/i64 literal as its unsigned 64-bit register bitpattern."""
    match = re.fullmatch(r"(0x[0-9a-fA-F_]+|[0-9][0-9_]*)_(?:u64|i64)", value)
    if not match:
        return None
    return int(match.group(1).replace("_", ""), 0) % (1 << 64)


def input_binding(value, args):
    """Resolve one inversion operand expression against its configured Rust arguments."""
    argument_types = dict(args)
    if value in argument_types and argument_types[value] == "Nat":
        return value, False, ("param", value)
    indexed = re.fullmatch(r"([A-Za-z_]\w*)\[(\d+)\]", value)
    projected = re.fullmatch(r"([A-Za-z_]\w*)\.l(\d+)", value)
    if indexed or projected:
        argument, index_text = (indexed or projected).groups()
        kind = argument_types.get(argument)
        limit = {"Limbs": 4, "WideLimbs": 9}.get(kind)
        index = int(index_text)
        if limit is None or index >= limit:
            raise ValueError(f"unsupported indexed operand {value}")
        field = f"l{index}"
        return f"{argument}.{field}", True, ("load", argument, field)
    literal = parse_word_literal(value)
    if literal is not None:
        return str(literal), False, ("const", literal)
    raise ValueError(f"unsupported input operand expression {value}")


def invert_arg_fields(config):
    fields = {}
    for name, kind in config.args:
        if kind == "Limbs":
            fields[name] = [f"l{index}" for index in range(4)]
        elif kind == "WideLimbs":
            fields[name] = [f"l{index}" for index in range(9)]
    return fields


def helper_signature(config):
    grouped, index = [], 0
    while index < len(config.args):
        name, kind = config.args[index]
        names = [name]
        index += 1
        while index < len(config.args) and config.args[index][1] == kind:
            names.append(config.args[index][0])
            index += 1
        grouped.append(f"({' '.join(names)} : {kind})")
    return f"def {config.lean_name} {' '.join(grouped)} : {config.result_type} :="


def bind_invert_inputs(emitter, declarations, config):
    """Bind every input/inout operand from configured arguments, locals, or typed constants."""
    locals_ = dict(config.local_inputs)
    directions = {declaration.name: declaration.kind for declaration in declarations}
    if len(directions) != len(declarations):
        raise ValueError(f"{config.rust_name}: duplicate operand declaration")
    for declaration in declarations:
        if declaration.kind not in ("in", "inout"):
            continue
        value = locals_.get(declaration.value, declaration.value)
        expression, load, fact = input_binding(value, config.args)
        emitter.bind(declaration.name, expression, "argument", reads=(), load=load, fact=fact)
    return directions


def parse_invert_helper(source, config):
    allowed_places = ({f"value[{index}]" for index in range(4)}
                      if config.rust_name == "reduce_once" else set())
    parsed = asm_source.parse_helper_function(
        source, config.rust_name, config.signature, config.regions,
        allowed_options={"pure", "nomem", "nostack"},
        required_options={"pure", "nomem", "nostack"},
        inout_expression_outputs=allowed_places,
    )
    if len(parsed.blocks) != 1:
        raise ValueError(f"{config.rust_name}: expected exactly one asm block")
    block = parsed.blocks[0]
    asm_source.validate_declarations(
        block.declarations, INVERT_DECLARATIONS[config.rust_name], config.rust_name
    )
    return block


def result_registers(declarations, config):
    """Resolve configured Rust return fields to source asm operands, in field order."""
    outputs = {}
    for declaration in declarations:
        output = declaration.output
        direct_place = re.fullmatch(r"value\[(\d+)\]", declaration.value)
        if output and output != "_":
            if direct_place and config.rust_name == "reduce_once":
                output = f"r{direct_place.group(1)}"
            if output in outputs:
                raise ValueError(f"{config.rust_name}: duplicate output {output}")
            outputs[output] = declaration.name
    missing = [field for field in config.result_fields if field not in outputs]
    if missing:
        raise ValueError(f"{config.rust_name}: result fields have no asm output: {missing}")
    unused = sorted(set(outputs) - set(config.result_fields))
    if unused:
        raise ValueError(f"{config.rust_name}: named asm outputs not returned: {unused}")
    return [outputs[field] for field in config.result_fields]


def invert_result(config, registers):
    if config.lean_name == "updateAB":
        return f"  ⟨⟨{', '.join(registers[:4])}⟩, {registers[4]}, {registers[5]}⟩"
    if config.lean_name == "normalizeCoefficient":
        return f"  ⟨⟨value.l0, value.l1, value.l2, value.l3⟩, ⟨{', '.join(registers)}⟩⟩"
    return f"  ⟨{', '.join(registers)}⟩"


def state_structure(name, fields, doc):
    lines = [f"/-- {doc} -/", f"structure {name} where"]
    for field in fields:
        field_name, field_type = (field, "Nat") if isinstance(field, str) else field
        lines.append(f"  {field_name} : {field_type}")
    lines.append("  deriving DecidableEq, Repr")
    return "\n".join(lines)


RESULT_STRUCTURES = "\n\n".join((
    state_structure("UpdateABResult", (("value", "Limbs"), "f", "g"),
                    "The updated GCD value and sign-corrected matrix-row coefficients."),
    state_structure("InvertRow", ("f1", "g1"),
                    "The second row returned by the final low-limb divsteps."),
    state_structure("CoefficientSplit", (("low", "Limbs"), ("high", "Limbs")),
                    "The low half and adjusted high half of the final coefficient."),
))


def emit_straight_invert(source, config, block=None):
    block = parse_invert_helper(source, config) if block is None else block
    ins = instruction_ir(block.instructions)
    directions = {declaration.name: declaration.kind for declaration in block.declarations}
    emitter = Emitter(ins, directions)
    bind_invert_inputs(emitter, block.declarations, config)
    emitter.run(0, len(ins))
    outputs = result_registers(block.declarations, config)
    emitter.cur_reads = set()
    for register in outputs:
        emitter.read(register)
    return Routine(
        config.doc, helper_signature(config), emitter.render(outputs),
        invert_result(config, outputs), config.lean_name, emitter, outputs,
        arg_fields=invert_arg_fields(config),
    )


def loop_boundaries(ins, config):
    labels = [index for index, (op, _tokens, text) in enumerate(ins)
              if op.endswith(":") and text == "2:"]
    branches = [index for index, (op, tokens, _text) in enumerate(ins)
                if op == "cbnz" and tokens == ["cnt", "2b"]]
    if len(labels) != 1 or len(branches) != 1 or branches[0] <= labels[0]:
        raise ValueError(f"{config.rust_name}: expected one `2:` / `cbnz cnt,2b` loop")
    label, branch = labels[0], branches[0]
    decrements = [index for index in range(label + 1, branch)
                  if ins[index][2] == "sub cnt,cnt,#1"]
    if len(decrements) != 1:
        raise ValueError(f"{config.rust_name}: expected one `sub cnt,cnt,#1` in loop")
    return label, branch


def loop_live_sets(entries):
    bound, live_in = set(), []
    for entry in entries:
        for register in sorted(entry["reads"]):
            if register not in bound and register not in live_in:
                live_in.append(register)
        bound.add(entry["name"])
    carried = [register for register in live_in if register in bound]
    invariant = [register for register in live_in if register not in bound]
    return carried, invariant


def loop_state_contract(config):
    if config.loop_count == 31:
        return ["a3", "cnt", "b3", "fg1", "fg0"], ["bias"]
    if config.loop_count == 47:
        return ["a", "cnt", "b", "f0", "g0", "f1", "g1"], []
    raise ValueError(f"{config.rust_name}: unsupported loop count {config.loop_count}")


def render_source_ssa(emitter, result_names):
    """Render live bindings under the wrapper skeleton's unambiguous SSA names.

    This is intentionally a source-rendering view: the emitter keeps source register names in its
    IR so liveness and skeleton facts continue to use the shared machinery.
    """
    live = emitter.liveness(result_names)
    live_entries = [entry for entry, keep in zip(emitter.entries, live) if keep]
    names = iter(gen.ssa_names(live_entries))
    current, lines = {}, []
    for entry, keep in zip(emitter.entries, live):
        if keep:
            name = next(names)
            expression = entry["expr"]
            for read in sorted(entry["reads"], key=len, reverse=True):
                expression = re.sub(
                    rf"(?<![A-Za-z0-9_']){re.escape(read)}(?![A-Za-z0-9_'])",
                    current.get(read, read),
                    expression,
                )
            lines.append((f"  let {name} := {expression}", entry.get("note") or entry["comment"]))
            current[entry["name"]] = name
        elif entry["load"]:
            lines.append((
                None,
                f"  -- {entry['comment']}: {entry['name']} = {entry['expr']} is never read",
            ))
        elif entry["name"] != "c":
            raise ValueError(
                f"dead computation: {entry['name']} := {entry['expr']} ({entry['comment']})"
            )
    return lines, [current[name] for name in result_names]


def emit_loop_invert(source, config):
    block = parse_invert_helper(source, config)
    ins = instruction_ir(block.instructions)
    label, branch = loop_boundaries(ins, config)
    directions = {declaration.name: declaration.kind for declaration in block.declarations}

    flattened = Emitter(ins, directions)
    bind_invert_inputs(flattened, block.declarations, config)
    flattened.run(0, label)
    for pc in range(label + 1, branch):
        flattened.pc = pc
        flattened.step(*ins[pc])
    flattened.run(branch + 1, len(ins))
    body_entries = [dict(entry) for entry in flattened.entries
                    if entry["pc"] is not None and label < entry["pc"] < branch]
    carried, invariant = loop_live_sets(body_entries)
    expected_carried, expected_invariant = loop_state_contract(config)
    if carried != expected_carried or invariant != expected_invariant:
        raise ValueError(
            f"{config.rust_name}: derived loop state {(carried, invariant)} differs from "
            f"contract {(expected_carried, expected_invariant)}"
        )

    count_decl = next((declaration for declaration in block.declarations
                       if declaration.name == "cnt"), None)
    if count_decl is None or parse_word_literal(count_decl.value) != config.loop_count:
        raise ValueError(f"{config.rust_name}: counter initializer must be {config.loop_count}")

    state_name = config.lean_name[0].upper() + config.lean_name[1:] + "State"
    round_name = config.lean_name + "Round"
    round_emitter = Emitter(ins, directions)
    for register in invariant:
        round_emitter.bind(register, register, "invariant argument", reads=(),
                           fact=("param", register))
    for register in carried:
        round_emitter.bind(register, f"acc.{register}", "loop state argument", reads=(),
                           load=True, fact=("load", "acc", register))
    round_emitter.entries.extend(body_entries)
    round_emitter.cur_reads = set()
    for register in carried:
        round_emitter.read(register)
    round_struct = state_structure(
        state_name, carried, f"Registers carried by one checked iteration of `{config.lean_name}`."
    )
    invariant_args = "" if not invariant else " (" + " ".join(invariant) + " : Nat)"
    round_routine = Routine(
        f"One source loop iteration of `{config.lean_name}`. The wrapper validates and calls it "
        f"exactly {config.loop_count} times.",
        f"def {round_name}{invariant_args} (acc : {state_name}) : {state_name} :=",
        round_emitter.render(carried), f"  ⟨{', '.join(carried)}⟩", round_name,
        round_emitter, carried, struct=round_struct, arg_fields={"acc": carried},
    )

    wrapper = Emitter(ins, directions)
    wrapper.entries = [dict(entry) for entry in flattened.entries
                       if entry["pc"] is None or entry["pc"] < label]
    call_fmt = round_name + (" " + " ".join("{%d}" % i for i in range(len(invariant)))
                             if invariant else "")
    first_state_index = len(invariant)
    call_fmt += " ⟨" + ", ".join("{%d}" % (first_state_index + i)
                                  for i in range(len(carried))) + "⟩"
    epilogue_entries = [dict(entry) for entry in flattened.entries
                        if entry["pc"] is not None and entry["pc"] > branch]
    outputs = result_registers(block.declarations, config)
    final_reads = set(outputs).union(*(entry["reads"] for entry in epilogue_entries))
    for iteration in range(1, config.loop_count + 1):
        call_args = invariant + carried
        call_name = f"round{iteration}"
        wrapper.entries.append(dict(
            name=call_name, expr=call_fmt.format(*call_args), comment=f"loop iteration {iteration}",
            note=None, reads=set(call_args), load=False, fact=("call", call_fmt, list(call_args)),
            pc=None,
        ))
        next_fields = carried if iteration < config.loop_count else [
            register for register in carried if register in final_reads
        ]
        for register in next_fields:
            wrapper.entries.append(dict(
                name=register, expr=f"{call_name}.{register}",
                comment=f"loop iteration {iteration} output", note=None,
                reads={call_name}, load=False, fact=("callout", call_name, register), pc=None,
            ))
    wrapper.entries.extend(epilogue_entries)
    wrapper.known = {entry["name"] for entry in wrapper.entries}
    outputs = result_registers(block.declarations, config)
    wrapper.cur_reads = set()
    for register in outputs:
        wrapper.read(register)
    # The 47-step wrapper's result fields have the same names as its initial register bindings.
    # Render that source term in SSA form so targeted let extraction cannot choose the final field
    # binding when the skeleton asks for the initial one. Keep the established 31-step output and
    # its proof unchanged.
    if config.loop_count == 47:
        wrapper.source_ssa = True
        lines, source_outputs = render_source_ssa(wrapper, outputs)
    else:
        lines, source_outputs = wrapper.render(outputs), outputs
    main = Routine(
        config.doc, helper_signature(config), lines,
        invert_result(config, source_outputs), config.lean_name, wrapper, outputs,
        arg_fields=invert_arg_fields(config),
    )
    return [round_routine, main]


class SkeletonBackend(gen.SkeletonBackend):
    """AArch64 grouping and proof facts used by the shared skeleton traversal."""

    def prepare(self, emitter, entries):
        history = [()] * len(entries)
        if getattr(emitter, "source_ssa", False):
            full_entries = entries
            full_names, keep, representatives, _expressions = gen.normalize_equal_lets(full_entries)
            kept_indices = [index for index, retained in enumerate(keep) if retained]
            entries = [dict(full_entries[index]) for index in kept_indices]
            history = []
            previous_full_index = -1
            for index in kept_indices:
                history.append([
                    (full_entries[skipped]["name"], full_names[representatives[skipped]])
                    for skipped in range(previous_full_index + 1, index)
                ])
                previous_full_index = index
            names = [full_names[index] for index in kept_indices]
        else:
            entries = [dict(entry) for entry in entries]
            names = gen.ssa_names(entries)
        i = 0
        while i < len(entries):
            kind = entries[i]["fact"][0]
            if kind not in ("adds", "subs"):
                i += 1
                continue
            # An `adds`/`subs` whose carry nothing reads has no carry binding (the inline
            # block's last shift), so its group is the pair and the carry is a ghost, as for
            # `adc`.
            dead_carry = (i + 2 >= len(entries) or entries[i + 2]["fact"] != ("snd",))
            group_count = 2 if dead_carry else 3
            entries[i]["group"] = [
                (entry, name, True)
                for entry, name in zip(entries[i:i + group_count], names[i:i + group_count])
            ]
            entries[i]["group_label"] = names[i + 1]
            entries[i]["dead_carry"] = dead_carry
            i += group_count
        return gen.SkeletonPreparation(entries, names, history=history)

    def fact(self, kind, ops, context):
        def operand_lt64(operand):
            shifted = re.fullmatch(r"\(?(lsr|asr|lsl) (\S+) ([0-9]+)\)?", str(operand))
            if shifted:
                function, _value, _amount = shifted.groups()
                if function == "lsr":
                    return f"(lt_of_le_of_lt (Nat.div_le_self _ _) {context.lt64(_value)})"
                if function == "asr":
                    return "asr_lt _ _"
                return "Nat.mod_lt _ (Nat.two_pow_pos _)"
            return context.lt64(operand)

        if kind == "const":
            (value,) = ops
            context.eq(context.name, str(value))
            context.lines.append(f"  have b_{context.name} : {context.name} < 2^64 := by rw [e_{context.name}]; decide")
            context.bnd[context.name] = f"b_{context.name}"
            return True
        simple = {
            "add": "add", "sub": "sub", "eor": "eor", "orr": "orr",
            "and": "bitAnd", "neg": "neg", "asr": "asr", "lslv": "lslv",
            "lsrv": "lsrv", "extr": "extr", "ubfx": "ubfx", "sbfx": "sbfx",
            "bfxil": "bfxil",
        }
        if kind in simple:
            function = simple[kind]
            rhs = f"{function} {' '.join(str(op) for op in ops)}"
            context.eq(context.name, rhs)
            context.lines.append(
                f"  have b_{context.name} : {context.name} < 2^64 := by "
                f"rw [e_{context.name}]; exact {function}_lt {' '.join('_' for _ in ops)}"
            )
            context.bnd[context.name] = f"b_{context.name}"
            return True
        if kind == "clz":
            (a,) = ops
            context.eq(context.name, f"clz {a}")
            context.lines.append(
                f"  have b_{context.name} : {context.name} < 2^64 := by "
                f"rw [e_{context.name}]; exact lt_of_le_of_lt (clz_le _) (by norm_num)"
            )
            context.bnd[context.name] = f"b_{context.name}"
            return True
        if kind == "cmp":
            a, b = ops
            context.eq(context.name, f"(cmp {a} {b}).z")
            context.lines.append(f"  have b_{context.name} : {context.name} ≤ 1 := calc")
            context.lines.append(f"    {context.name} = (cmp {a} {b}).z := e_{context.name}")
            context.lines.append(f"    _ ≤ 1 := cmp_z_le_one {a} {b}")
            context.bnd[context.name] = f"b_{context.name}"
            context.unit_bound.add(context.name)
            return True
        if kind == "lsr" and ops[1] != 2:
            a, k = ops
            context.eq(context.name, f"lsr {a} {k}")
            context.lines.append(
                f"  have b_{context.name} : {context.name} < 2^64 := by "
                f"rw [e_{context.name}]; exact lt_of_le_of_lt (Nat.div_le_self _ _) {context.lt64(a)}"
            )
            context.bnd[context.name] = f"b_{context.name}"
            return True
        if kind in ("adds", "subs"):
            a, b, cin = ops
            i, entries = context.index, context.entries
            xn = context.group_names[1]
            dead_carry = context.entry["dead_carry"]
            cn = f"k_{xn}" if dead_carry else context.group_names[2]
            if kind == "adds":
                val = f"({a} + {b} + {cin})"
                lin = f"{xn} + 2^64 * {cn} = {a} + {b} + {cin}"
                lin_proof = "Nat.mod_add_div _ _"
                carry_proof = f"addc_carry_le_one {a} {b} {cin} {operand_lt64(a)} {operand_lt64(b)} {context.le1(cin)}"
            else:
                val = f"({a} + 2^64 - {b} - (1 - {cin}))"
                lin = f"{xn} + 2^64 * {cn} + {b} + 1 = {a} + 2^64 + {cin}"
                lin_proof = f"subc_lin {a} {b} {cin} {operand_lt64(b)} {context.le1(cin)}"
                carry_proof = f"subc_carry_le_one {a} {b} {cin} {operand_lt64(a)}"
            context.eq(xn, f"{val} % 2^64")
            if dead_carry:
                context.lines.append(f"  have b_{xn} : {xn} < 2^64 := by rw [e_{xn}]; "
                                     "exact Nat.mod_lt _ (Nat.two_pow_pos _)")
                context.lines.append(f"  obtain ⟨{cn}, b_{cn}, l_{xn}⟩ :")
                context.lines.append(f"      ∃ k, k ≤ 1 ∧ {lin.replace(cn, 'k')} :=")
                context.lines.append(f"    ⟨{val} / 2^64, {carry_proof},")
                context.lines.append(f"      by rw [e_{xn}]; exact {lin_proof}⟩")
                context.lines.append(f"  clear e_{xn}")
                context.ren[entries[i + 1]["name"]] = xn
                context.bnd[xn] = f"b_{xn}"
                context.consumed = 2
            else:
                context.eq(cn, f"{val} / 2^64")
                context.lines.append(f"  have l_{xn} : {lin} := by")
                context.lines.append(f"    rw [e_{xn}, e_{cn}]; exact {lin_proof}")
                context.lines.append(f"  have b_{xn} : {xn} < 2^64 := by rw [e_{xn}]; exact Nat.mod_lt _ (Nat.two_pow_pos _)")
                context.lines.append(f"  have b_{cn} : {cn} ≤ 1 := by")
                context.lines.append(f"    rw [e_{cn}]; exact {carry_proof}")
                context.lines.append(f"  clear e_{xn} e_{cn}")
                context.ren[entries[i + 1]["name"]] = xn
                context.ren[entries[i + 2]["name"]] = cn
                context.bnd[xn], context.bnd[cn] = f"b_{xn}", f"b_{cn}"
                context.unit_bound.add(cn)
                context.consumed = 3
            return True
        if kind == "subs_carry":
            a, b, cin = ops
            nm = context.name
            context.eq(nm, f"({a} + 2^64 - {b} - (1 - {cin})) / 2^64")
            context.lines.append(f"  have b_{nm} : {nm} ≤ 1 := by rw [e_{nm}]; exact subc_carry_le_one {a} {b} {cin} {context.lt64(a)}")
            context.lines.append(f"  have l_{nm} : ({nm} = 1 ∧ {b} + 1 ≤ {a} + {cin}) ∨ ({nm} = 0 ∧ {a} + {cin} < {b} + 1) :=")
            context.lines.append(f"    subc_carry_cases {a} {b} {cin} _ e_{nm} {context.lt64(a)} {context.lt64(b)} {context.le1(cin)}")
            context.lines.append(f"  clear e_{nm}")
            context.bnd[nm] = f"b_{nm}"
            context.unit_bound.add(nm)
            return True
        return False


SKELETON_BACKEND = SkeletonBackend()


class Routine(gen.Routine):
    architecture = "AArch64"
    skeleton_backend = SKELETON_BACKEND


wrap_tactic = gen.wrap_tactic


def gen_program():
    parts = [HEADER, "import PastaAsm.Inversion\nimport PastaAsm.AArch64.Semantics\n", """
/-!
# The crate's inline Pasta field blocks, transcribed

GENERATED by `lean/scripts/gen.py` from the `asm!` blocks of `mul`, `square`, `add`, and `sub`
in `src/aarch64.rs`; do not edit by hand. Each definition follows its block instruction by
instruction (the instruction is the trailing comment; the two lines that unpack an
instruction's (result, carry) pair are marked as its continuation), over the semantics of
`PastaAsm.AArch64.Semantics`. Registers are rebound by the instructions that write them, `c`
is the carry flag, `s` is the (result, carry) pair of the instruction that last set both,
argument limbs are read where the block's operands bind them, and the output limbs are bound
where the block's output operands hold them. Bindings that nothing reads are left as
comments. See the generator's docstring for what it checks.
-/

namespace PastaAsm.AArch64

"""]
    routines = all_routines()
    legacy, inversion = routines[:5], routines[5:]

    def comment_column(selected):
        return 2 + max(len(code) for routine in selected for code, _ in routine.lines
                       if code is not None and len(code) <= COMMENT_COLUMN_MAX)

    # Preserve the historical definitions byte-for-byte: inversion has its own comment column,
    # so adding a longer binding cannot reflow any pre-existing transcription.
    parts.append("\n".join(routine.text(comment_column(legacy)) for routine in legacy))
    parts.extend(("\n", RESULT_STRUCTURES, "\n\n"))
    parts.append("\n".join(routine.text(comment_column(inversion)) for routine in inversion))
    parts.append("\nend PastaAsm.AArch64\n")
    return "".join(parts)


# Shared vector metadata remains available here for callers of the former backend API.
FIELDS = gen.FIELDS
MODULUS_INT = gen.MODULUS_INT


def in_contract(op, key, operands):
    """Whether the vector's operands satisfy the AArch64/public entry contract."""
    return gen.in_public_contract(op, key, operands)


def gen_vectors(lines):
    """Generate byte-for-byte-compatible AArch64 checks through the shared emitter."""
    return gen.render_vectors(
        lines,
        imports="import PastaAsm.AArch64.Compositions\nimport PastaAsm.Fields\n",
        introduction="""
/-!
# Reference vectors for the transcribed blocks

GENERATED by `lean/scripts/gen.py` from `test-vectors/pasta_mul-armv8-vectors.txt`; do not
edit by hand. Each vector is the output of the real assembly (Semolina's `mul_mont_pasta`,
`sqr_mont_pasta`, and `from_mont_pasta`, as vendored by pasta_curves at
`8ad85e9fab7929f6236960e472f432a4bd9ccd74` and run on an Apple M-series machine) on the
given operands, and each example asks the kernel to evaluate the transcription on the same
operands. The multiplication and squaring examples exercise the inline blocks, which
transcribe those routines; the conversion examples exercise `fromMont`, the multiplication
block with `1` as its right operand, as the crate composes it. The vectors file also records
the routines' outputs on operands outside the proved contracts (unreduced operands), where the
block's dropped fifth limb can change the result, and those are left out here, with their
number recorded at the end.

The modulus limbs and `inv` are `pallasBase` and `vestaBase` from `Fields.lean`, the crate's
constants for its `Fp` (the Pallas base field) and `Fq` (the Vesta base field).
-/

namespace PastaAsm.AArch64

""",
        namespace="PastaAsm.AArch64",
        in_contract=in_contract,
        omission_scope="the proved contracts",
    )


def gen_invert_vectors(lines):
    """Generate AArch64 inversion-composition checks from mathematical expectations."""
    return gen.render_inversion_vectors(
        lines,
        imports="import PastaAsm.AArch64.Compositions\nimport PastaAsm.Fields\n",
        introduction="""
/-!
# Mathematical reference vectors for the inversion composition

GENERATED by `lean/scripts/gen.py` from the distinct canonical operands in
`test-vectors/pasta_mul-armv8-vectors.txt`; do not edit by hand. Each example asks the
Lean kernel to evaluate the actual AArch64 `invert` composition, including all generated
assembly-block transcriptions used by the Rust driver.

Only the operands come from the AArch64 hardware corpus. The expected values are derived
independently by modular arithmetic, not captured from inversion hardware: zero maps to zero;
for nonzero Montgomery residues `input * result = R^2 (mod p)`, where `R = 2^256`. Thus these
concrete examples supplement, but do not replace, a universal inversion correctness proof.

The modulus limbs and `inv` are `pallasBase` and `vestaBase` from `Fields.lean`, the crate's
constants for its `Fp` (the Pallas base field) and `Fq` (the Vesta base field).
-/

namespace PastaAsm.AArch64

""",
        namespace="PastaAsm.AArch64",
    )


# Proof skeleton construction and checking are shared in gen.py.

def all_routines():
    routines = []
    for fn, name, doc, args in INLINE_ROUTINES:
        routines += emit_inline(fn, name, doc, args)
    invert_source = INVERT.read_text()
    for config in INVERT_ROUTINES:
        if config.loop_count is None:
            routines.append(emit_straight_invert(invert_source, config))
        else:
            routines += emit_loop_invert(invert_source, config)
    return routines


def generated_outputs():
    """Return the AArch64 generated paths and contents without writing files."""
    lines = VECTORS.read_text().splitlines()
    return [
        (OUT_PROGRAM, gen_program()),
        (OUT_VECTORS, gen_vectors(lines)),
        (OUT_INVERT_VECTORS, gen_invert_vectors(lines)),
    ]
