#!/usr/bin/env python3
# Copyright (c) 2026 the pasta-asm contributors.
# SPDX-License-Identifier: Apache-2.0
"""Regression tests for fail-closed Rust surrounding-code parsing."""

import dataclasses
from pathlib import Path
import re
import sys
import tempfile
import unittest
from unittest import mock

# Running this source-tree test should not leave lean/scripts/__pycache__ behind.
sys.dont_write_bytecode = True

import asm_source
import gen_aarch64
import gen_x86_64


class SurroundingCodeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.aarch64_source = gen_aarch64.INLINE.read_text()
        cls.x86_64_source = gen_x86_64.SOURCE.read_text()

    @staticmethod
    def mutate_function(source, name, old, new):
        masked = asm_source.masked_noncode(source)
        match = re.search(rf"(?m)^.*\bfn\s+{re.escape(name)}\s*\(", masked)
        if match is None:
            raise AssertionError(f"function {name} not found")
        signature_open = masked.find("(", match.start())
        signature_close = asm_source.matching_delimiter(
            source, signature_open, "(", ")"
        )
        body_open = masked.find("{", signature_close)
        body_close = asm_source.matching_delimiter(source, body_open, "{", "}")
        function_source = source[match.start():body_close + 1]
        if function_source.count(old) != 1:
            raise AssertionError(f"expected one {old!r} in {name}")
        return (
            source[:match.start()]
            + function_source.replace(old, new)
            + source[body_close + 1:]
        )

    @staticmethod
    def generate_aarch64(source):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "aarch64.rs"
            path.write_text(source)
            with mock.patch.object(gen_aarch64, "INLINE", path):
                return gen_aarch64.gen_program()

    def test_current_sources_generate_committed_output(self):
        self.assertEqual(
            self.generate_aarch64(self.aarch64_source),
            gen_aarch64.OUT_PROGRAM.read_text(),
        )
        self.assertEqual(
            gen_x86_64.gen_program(self.x86_64_source),
            gen_x86_64.OUTPUT.read_text(),
        )

    def test_inv_shadowing_is_rejected_by_both_backends(self):
        for architecture, source, generate in (
            ("aarch64", self.aarch64_source, self.generate_aarch64),
            ("x86_64", self.x86_64_source, gen_x86_64.gen_program),
        ):
            with self.subTest(architecture=architecture):
                mutated = self.mutate_function(
                    source,
                    "mul",
                    "    let (o0, o1, o2, o3): (u64, u64, u64, u64);",
                    "    let inv = 0;\n"
                    "    let (o0, o1, o2, o3): (u64, u64, u64, u64);",
                )
                with self.assertRaisesRegex(
                    asm_source.GenerationError,
                    "local inv shadows a function argument",
                ):
                    generate(mutated)

    def test_postasm_output_mutation_is_rejected_by_both_backends(self):
        for architecture, source, generate in (
            ("aarch64", self.aarch64_source, self.generate_aarch64),
            ("x86_64", self.x86_64_source, gen_x86_64.gen_program),
        ):
            with self.subTest(architecture=architecture):
                mutated = self.mutate_function(
                    source,
                    "add",
                    "    }\n    [r0, r1, r2, r3]",
                    "    }\n    r0 = 0;\n    [r0, r1, r2, r3]",
                )
                with self.assertRaisesRegex(
                    asm_source.GenerationError,
                    "unsupported code after asm!",
                ):
                    generate(mutated)

    def test_comments_are_allowed_between_surrounding_grammar_tokens(self):
        for architecture, source, generate, expected in (
            (
                "aarch64",
                self.aarch64_source,
                self.generate_aarch64,
                gen_aarch64.OUT_PROGRAM.read_text(),
            ),
            (
                "x86_64",
                self.x86_64_source,
                gen_x86_64.gen_program,
                gen_x86_64.OUTPUT.read_text(),
            ),
        ):
            with self.subTest(architecture=architecture):
                commented = self.mutate_function(
                    source,
                    "add",
                    "    let [mut r0, mut r1, mut r2, mut r3] = *lhs;",
                    "    let /* outputs */ [mut r0, mut r1, mut r2, mut r3] "
                    "= * /* input */ lhs;",
                )
                self.assertEqual(generate(commented), expected)


AARCH64_HELPERS = {
    "divsteps_31": (
        "fn divsteps_31(a: &Limbs, b: &Limbs) -> Matrix",
        (("prefix", """
            let [a0, a1, a2, a3] = *a;
            let [b0, b1, b2, b3] = *b;
            let (f0, g0, f1, g1): (i64, i64, i64, i64);
            unsafe {
        """), ("return", "; } Matrix { f0, g0, f1, g1 }")),
    ),
    "update_ab": (
        "fn update_ab(a: &Limbs, b: &Limbs, mut f: i64, mut g: i64) -> (Limbs, i64, i64)",
        (("prefix", """
            let [mut a0, mut a1, mut a2, mut a3] = *a;
            let [b0, b1, b2, b3] = *b;
            unsafe {
        """), ("return", "; } ([a0, a1, a2, a3], f, g)")),
    ),
    "add_words": (
        "fn add_words(lhs: &Wide, rhs: &Wide) -> Wide",
        (("prefix", """
            let (o0, o1, o2, o3, o4, o5, o6, o7, o8):
                (u64, u64, u64, u64, u64, u64, u64, u64, u64);
            unsafe {
        """), ("return", "; } [o0, o1, o2, o3, o4, o5, o6, o7, o8]")),
    ),
    "mul_signed": (
        "fn mul_signed(value: &Wide, scalar: i64) -> Wide",
        (("prefix", """
            let (o0, o1, o2, o3, o4, o5, o6, o7, o8):
                (u64, u64, u64, u64, u64, u64, u64, u64, u64);
            unsafe {
        """), ("return", "; } [o0, o1, o2, o3, o4, o5, o6, o7, o8]")),
    ),
    "divsteps_47": (
        "fn divsteps_47(a: u64, b: u64) -> (i64, i64)",
        (("prefix", "let (f1, g1): (i64, i64); unsafe {"),
         ("return", "; } (f1, g1)")),
    ),
    "normalize_coefficient": (
        "fn normalize_coefficient(value: &Wide, modulus: &Limbs) -> (Limbs, Limbs)",
        (("prefix", """
            let low = [value[0], value[1], value[2], value[3]];
            let (w4, w5, w6, w7): (u64, u64, u64, u64);
            unsafe {
        """), ("return", "; } (low, [w4, w5, w6, w7])")),
    ),
    "reduce_once": (
        "fn reduce_once(mut value: Limbs, modulus: &Limbs) -> Limbs",
        (("prefix", "unsafe {"), ("return", "; } value")),
    ),
}


X86_64_HELPERS = {
    "divsteps_31": (
        "fn divsteps_31(a: &Limbs, b: &Limbs) -> Matrix",
        (("prefix", """
            let mut a0 = a[0]; let mut a1 = a[1]; let mut a2 = a[2]; let a3 = a[3];
            let mut b0 = b[0]; let b1 = b[1]; let b2 = b[2]; let b3 = b[3];
            unsafe {
        """), ("return", """
            ; }
            Matrix { f0: a0 as i64, g0: a1 as i64, f1: b0 as i64, g1: a2 as i64, }
        """)),
    ),
    "update_ab": (
        "fn update_ab(a: &Limbs, b: &Limbs, f: i64, g: i64) -> (Limbs, i64, i64)",
        (("prefix", """
            let aa = [a[0], a[1], a[2], a[3], 0];
            let bb = [b[0], b[1], b[2], b[3], 0];
            let [mut r0, mut r1, mut r2, mut r3, r4] = lincomb(&aa, &bb, f, g);
            let mask: u64; let bit: u64;
            unsafe {
        """), ("wrapping correction", """
            ; }
            let corrected_f = ((f as u64) ^ mask).wrapping_add(bit) as i64;
            let corrected_g = ((g as u64) ^ mask).wrapping_add(bit) as i64;
            ([r0, r1, r2, r3], corrected_f, corrected_g)
        """)),
    ),
    "add_words": (
        "fn add_words<const N: usize>(mut lhs: [u64; N], rhs: &[u64; N]) -> [u64; N]",
        (("loop prefix", """
            let mut carry = 0u64;
            for i in 0..N { unsafe {
        """), ("loop suffix", "; } } lhs")),
    ),
    "mul_signed": (
        "fn mul_signed<const N: usize>(value: &[u64; N], scalar: i64) -> [u64; N]",
        (("wrapping prefix", """
            let scalar = scalar as u64;
            let sign = (scalar as i64 >> 63) as u64;
            let sign_bit = sign & 1;
            let magnitude = (scalar ^ sign).wrapping_add(sign_bit);
            let mut out = [0; N];
            let mut negate_carry = sign_bit;
            let mut product_carry = 0u64;
            for i in 0..N {
                let limb = value[i];
                let next_negate_carry: u8;
                let low: u64;
                let high: u64;
                unsafe {
        """), ("loop suffix", """
            ; }
            out[i] = low;
            negate_carry = u64::from(next_negate_carry);
            product_carry = high;
            }
            out
        """)),
    ),
    "divsteps_47": (
        "fn divsteps_47(a: u64, b: u64) -> Matrix",
        (("prefix", """
            let mut f0 = 1u64; let mut g0 = 0u64;
            let mut f1 = 0u64; let mut g1 = 1u64;
            unsafe {
        """), ("return", """
            ; }
            Matrix { f0: f0 as i64, g0: g0 as i64, f1: f1 as i64, g1: g1 as i64, }
        """)),
    ),
    "normalize": (
        "fn normalize(mut value: [u64; 9], modulus: &Limbs) -> [u64; 8]",
        (("prefix", """
            let modx = [
                modulus[0] << 1,
                (modulus[1] << 1) | (modulus[0] >> 63),
                (modulus[2] << 1) | (modulus[1] >> 63),
                (modulus[3] << 1) | (modulus[2] >> 63),
            ];
            let [mut h0, mut h1, mut h2, mut h3] =
                [value[4], value[5], value[6], value[7]];
            let mut excess = value[8];
            let [m0, m1, m2, m3] = modx;
            unsafe {
        """), ("between adjustments", """
            ; }
            let [m0, m1, m2, m3] = modx;
            unsafe {
        """), ("return", """
            ; }
            value[4] = h0; value[5] = h1; value[6] = h2; value[7] = h3;
            [value[0], value[1], value[2], value[3], value[4], value[5], value[6], value[7],]
        """)),
    ),
    "reduce_once": (
        "fn reduce_once(mut value: Limbs, modulus: &Limbs) -> Limbs",
        (("prefix", """
            let p0 = modulus[0]; let p1 = modulus[1]; let p3 = modulus[3];
            unsafe {
        """), ("return", "; } value")),
    ),
}


class InversionHelperTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        root = Path(__file__).resolve().parents[2]
        cls.aarch64_source = (root / "src/aarch64/invert.rs").read_text()
        cls.x86_64_source = (root / "src/x86_64/invert.rs").read_text()

    def parse_aarch64(self, name, source=None):
        signature, regions = AARCH64_HELPERS[name]
        expression_outputs = (
            {f"value[{index}]" for index in range(4)}
            if name == "reduce_once" else set()
        )
        return asm_source.parse_helper_function(
            self.aarch64_source if source is None else source,
            name,
            signature,
            regions,
            allowed_options={"pure", "nomem", "nostack"},
            required_options={"pure", "nomem", "nostack"},
            inout_expression_outputs=expression_outputs,
        )

    def parse_x86_64(self, name, source=None):
        signature, regions = X86_64_HELPERS[name]
        expression_outputs = {
            "add_words": {"lhs[i]"},
            "reduce_once": {f"value[{index}]" for index in range(4)},
        }.get(name, set())
        return asm_source.parse_helper_function(
            self.x86_64_source if source is None else source,
            name,
            signature,
            regions,
            fixed_registers={"rax", "rcx", "rdx"},
            allowed_options={"pure", "nomem", "nostack"},
            required_options={"pure", "nomem", "nostack"},
            allowed_kinds={"in", "out", "inout", "lateout"},
            allowed_constraints={"reg", "reg_byte"},
            named_fixed_outputs={"rax", "rdx"},
            inout_expression_outputs=expression_outputs,
        )

    def assert_spans_partition_body(self, source, parsed):
        pieces = []
        for index, block in enumerate(parsed.blocks):
            pieces.append(parsed.rust_regions[index].source)
            pieces.append(source[block.start:block.end])
        pieces.append(parsed.rust_regions[-1].source)
        self.assertEqual("".join(pieces), source[parsed.body_start:parsed.body_end])

    def test_all_actual_aarch64_helper_blocks_and_boundaries_are_parsed(self):
        block_count = 0
        for name in AARCH64_HELPERS:
            with self.subTest(helper=name):
                parsed = self.parse_aarch64(name)
                self.assertEqual(len(parsed.rust_regions), len(parsed.blocks) + 1)
                self.assert_spans_partition_body(self.aarch64_source, parsed)
                block_count += len(parsed.blocks)
        self.assertEqual(block_count, 7)

    def test_all_actual_x86_64_helper_blocks_and_boundaries_are_parsed(self):
        block_count = 0
        for name in X86_64_HELPERS:
            with self.subTest(helper=name):
                parsed = self.parse_x86_64(name)
                self.assertEqual(len(parsed.rust_regions), len(parsed.blocks) + 1)
                self.assert_spans_partition_body(self.x86_64_source, parsed)
                block_count += len(parsed.blocks)
        self.assertEqual(block_count, 8)

    def test_signed_constants_tuple_struct_returns_and_special_operands(self):
        aarch64_final = self.parse_aarch64("divsteps_47")
        declarations = {item.name: item for item in aarch64_final.blocks[0].declarations}
        self.assertEqual(declarations["f0"].value, "1_i64")
        self.assertEqual(declarations["f1"].output, "f1")
        self.assertIn("(f1, g1)", aarch64_final.rust_regions[-1].source)

        x86_update = self.parse_x86_64("update_ab")
        kinds = {item.name: item.kind for item in x86_update.blocks[0].declarations}
        self.assertEqual(kinds["mask"], "lateout")
        self.assertIn("wrapping_add", x86_update.rust_regions[-1].source)

        x86_multiply = self.parse_x86_64("mul_signed")
        declarations = {item.name: item for item in x86_multiply.blocks[0].declarations}
        self.assertEqual(declarations["next_negate_carry"].kind, "out")
        self.assertEqual(declarations["rax"].output, "low")
        self.assertEqual(declarations["rdx"].output, "high")

        struct_return = self.parse_x86_64("divsteps_31")
        self.assertIn("Matrix {", struct_return.rust_regions[-1].source)

    def test_declaration_retains_constraint_with_backward_compatible_default(self):
        self.assertEqual(
            asm_source.Declaration("x", "in", "value", None).constraint, "reg"
        )
        parsed = self.parse_x86_64("mul_signed").blocks[0].declarations
        declarations = {declaration.name: declaration for declaration in parsed}
        self.assertEqual(declarations["next_negate_carry"].constraint, "reg_byte")
        self.assertEqual(declarations["rax"].constraint, "rax")
        self.assertTrue(declarations["rax"].fixed)

    def test_exact_declaration_validator_covers_every_field_and_order(self):
        declaration = asm_source.Declaration("x", "in", "value", None)
        mutations = (
            dataclasses.replace(declaration, name="y"),
            dataclasses.replace(declaration, kind="inout"),
            dataclasses.replace(declaration, value="other"),
            dataclasses.replace(declaration, output="value"),
            dataclasses.replace(declaration, fixed=True),
            dataclasses.replace(declaration, constraint="reg_byte"),
        )
        for mutated in mutations:
            with self.subTest(mutated=mutated):
                with self.assertRaisesRegex(
                    asm_source.GenerationError, "declaration 0 does not match expected"
                ):
                    asm_source.validate_declarations((mutated,), (declaration,), "test")
        with self.assertRaisesRegex(
            asm_source.GenerationError, "declaration 1 does not match expected"
        ):
            asm_source.validate_declarations(
                (declaration,), (declaration, declaration), "test"
            )

    def test_exact_declaration_validator_rejects_compile_valid_wiring_mutations(self):
        expected = (
            asm_source.Declaration("limb", "inout", "limb", "_"),
            asm_source.Declaration("sign", "in", "sign", None),
            asm_source.Declaration("negate_carry", "in", "negate_carry", None),
            asm_source.Declaration(
                "next_negate_carry", "out", "next_negate_carry", "next_negate_carry",
                constraint="reg_byte",
            ),
            asm_source.Declaration("magnitude", "in", "magnitude", None),
            asm_source.Declaration("product_carry", "in", "product_carry", None),
            asm_source.Declaration(
                "rax", "out", "low", "low", fixed=True, constraint="rax"
            ),
            asm_source.Declaration(
                "rdx", "out", "high", "high", fixed=True, constraint="rdx"
            ),
        )
        mutations = (
            ("sign = in(reg) sign,", "sign = in(reg) magnitude,"),
            ('out("rax") low,\n                out("rdx") high,',
             'out("rax") high,\n                out("rdx") low,'),
        )
        for old, new in mutations:
            with self.subTest(mutation=new):
                source = self.x86_64_source.replace(old, new, 1)
                self.assertNotEqual(source, self.x86_64_source)
                actual = self.parse_x86_64("mul_signed", source).blocks[0].declarations
                with self.assertRaisesRegex(
                    asm_source.GenerationError,
                    r"mul_signed: declaration \d+ does not match expected",
                ):
                    asm_source.validate_declarations(actual, expected, "mul_signed")

    def test_multiple_blocks_and_loop_boundaries_are_explicit(self):
        normalize = self.parse_x86_64("normalize")
        self.assertEqual(len(normalize.blocks), 2)
        self.assertEqual(
            [region.name for region in normalize.rust_regions],
            ["prefix", "between adjustments", "return"],
        )
        loop = self.parse_x86_64("mul_signed")
        self.assertIn("for i in 0..N", loop.rust_regions[0].source)
        self.assertIn("product_carry = high", loop.rust_regions[1].source)

    def test_unmodeled_rust_and_changed_signatures_are_rejected(self):
        mutated = self.aarch64_source.replace(
            "    ([a0, a1, a2, a3], f, g)",
            "    f = 0;\n    ([a0, a1, a2, a3], f, g)",
            1,
        )
        with self.assertRaisesRegex(
            asm_source.GenerationError, "Rust region 'return' does not match expected"
        ):
            self.parse_aarch64("update_ab", mutated)

        mutated = self.x86_64_source.replace(
            "fn add_words<const N: usize>", "fn add_words<const N: u64>", 1
        )
        with self.assertRaisesRegex(
            asm_source.GenerationError, "function signature does not match expected"
        ):
            self.parse_x86_64("add_words", mutated)

    def test_extra_asm_block_and_unsupported_operand_are_rejected(self):
        parsed = self.parse_x86_64("mul_signed")
        helper = self.x86_64_source[parsed.start:parsed.end]
        old = "        out[i] = low;"
        self.assertEqual(helper.count(old), 1)
        helper = helper.replace(
            old,
            "        unsafe { asm!(\"nop\", options(pure, nomem, nostack)); }\n"
            + old,
        )
        mutated = (
            self.x86_64_source[:parsed.start]
            + helper
            + self.x86_64_source[parsed.end:]
        )
        with self.assertRaisesRegex(asm_source.GenerationError, "Rust regions"):
            self.parse_x86_64("mul_signed", mutated)

        mutated = self.x86_64_source.replace(
            "mask = lateout(reg) mask,", "mask = mystery(reg) mask,", 1
        )
        with self.assertRaisesRegex(asm_source.GenerationError, "unsupported operand kind"):
            self.parse_x86_64("update_ab", mutated)

    def test_main_parse_function_remains_strict_for_helpers(self):
        with self.assertRaisesRegex(
            asm_source.GenerationError,
            "unsupported operand kind|unsupported code before asm!",
        ):
            asm_source.parse_function(
                self.x86_64_source, "update_ab", ["a", "b", "f", "g"], 3
            )


if __name__ == "__main__":
    unittest.main()
