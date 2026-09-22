#!/usr/bin/env python3
# Copyright (c) 2026 the pasta-asm contributors.
# SPDX-License-Identifier: Apache-2.0
"""Focused tests for mechanical x86-64 inversion-helper generation."""

from collections import Counter
import re
import sys
import unittest

# Running this source-tree test should not leave lean/scripts/__pycache__ behind.
sys.dont_write_bytecode = True

import gen
import gen_x86_64


class InvertParserTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = gen_x86_64.INVERT_SOURCE.read_text()

    def mutate(self, old, new):
        self.assertEqual(self.source.count(old), 1, old)
        return self.source.replace(old, new)

    def test_all_eight_asm_blocks_use_shared_helper_parser(self):
        parsed = [
            gen_x86_64.parse_invert_helper(self.source, config)
            for config in gen_x86_64.INVERT_ROUTINES
        ]
        self.assertEqual(sum(len(helper.blocks) for helper in parsed), 8)
        self.assertEqual(
            [len(block.instructions) for helper in parsed for block in helper.blocks],
            [68, 16, 4, 7, 29, 11, 23, 12],
        )
        normalize = next(
            helper for config, helper in zip(gen_x86_64.INVERT_ROUTINES, parsed)
            if config.rust_name == "normalize"
        )
        self.assertEqual([region.name for region in normalize.rust_regions],
                         ["first-inputs", "second-inputs", "result"])

    def test_non_asm_rust_mutation_is_rejected(self):
        source = self.mutate(
            "let sign_bit = sign & 1;",
            "let sign_bit = sign & 2;",
        )
        config = next(c for c in gen_x86_64.INVERT_ROUTINES
                      if c.rust_name == "mul_signed")
        with self.assertRaisesRegex(gen_x86_64.GenerationError, "Rust region 'loop'"):
            gen_x86_64.parse_invert_helper(source, config)

    def test_unapproved_indexed_inout_is_rejected(self):
        source = self.mutate(
            "lhs = inout(reg) lhs[i],",
            "lhs = inout(reg) lhs[0],",
        )
        config = next(c for c in gen_x86_64.INVERT_ROUTINES
                      if c.rust_name == "add_words")
        with self.assertRaisesRegex(gen_x86_64.GenerationError, "allowed output"):
            gen_x86_64.parse_invert_helper(source, config)

    def test_semantically_rewired_input_declaration_is_rejected(self):
        source = self.mutate(
            "sign = in(reg) sign,",
            "sign = in(reg) magnitude,",
        )
        config = next(c for c in gen_x86_64.INVERT_ROUTINES
                      if c.rust_name == "mul_signed")
        with self.assertRaisesRegex(gen_x86_64.GenerationError,
                                    "declaration 1 does not match expected"):
            gen_x86_64.parse_invert_helper(source, config)

    def test_swapped_fixed_mul_outputs_are_rejected(self):
        source = self.mutate(
            'out("rax") low,\n                out("rdx") high,',
            'out("rax") high,\n                out("rdx") low,',
        )
        config = next(c for c in gen_x86_64.INVERT_ROUTINES
                      if c.rust_name == "mul_signed")
        with self.assertRaisesRegex(gen_x86_64.GenerationError,
                                    "declaration 6 does not match expected"):
            gen_x86_64.parse_invert_helper(source, config)


class FixedLoopTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = gen_x86_64.INVERT_SOURCE.read_text()

    def assert_loop_mutation_rejected(self, old, new, message):
        self.assertEqual(self.source.count(old), 1, old)
        source = self.source.replace(old, new)
        with self.assertRaisesRegex(gen_x86_64.GenerationError, message):
            gen_x86_64.all_invert_routines(source)

    def test_source_loop_controls_are_factored_not_flattened(self):
        routines = {routine.name: routine for routine in gen_x86_64.all_invert_routines(self.source)}
        self.assertIn("iterate divsteps31Round 31", routines["divsteps31"].text(120))
        self.assertIn("iterate divsteps47Round 47", routines["divsteps47"].text(120))
        self.assertEqual(
            {entry["pc"] for entry in routines["divsteps31Round"].emitter.entries
             if entry["pc"] is not None},
            set(range(20)),
        )
        self.assertEqual(
            {entry["pc"] for entry in routines["divsteps47Round"].emitter.entries
             if entry["pc"] is not None},
            set(range(25)),
        )

    def test_changed_count_is_rejected(self):
        self.assert_loop_mutation_rejected(
            '"mov {count:e}, 47",', '"mov {count:e}, 46",',
            "count initializer",
        )

    def test_changed_label_is_rejected(self):
        # There are two `2:` labels; change only the one in divsteps_47 by anchoring its prefix.
        old = '"mov {count:e}, 47",\n            "2:",'
        new = '"mov {count:e}, 47",\n            "3:",'
        self.assert_loop_mutation_rejected(old, new, "loop control|exactly one")

    def test_changed_decrement_is_rejected(self):
        self.assert_loop_mutation_rejected(
            '"sub {count:e}, 1",', '"sub {count:e}, 2",',
            "loop control",
        )

    def test_changed_backedge_is_rejected(self):
        old = '"sub {count:e}, 1",\n            "jnz 2b",'
        new = '"sub {count:e}, 1",\n            "jnz 3b",'
        self.assert_loop_mutation_rejected(old, new, "loop control|exactly one")

    def test_extra_counter_use_is_rejected(self):
        old = '"xor {t0:e}, {t0:e}",\n            "test {a}, 1",'
        new = '"mov {t0:e}, {count:e}",\n            "test {a}, 1",'
        self.assert_loop_mutation_rejected(old, new, "counter may appear only")


class InvertEmitterTests(unittest.TestCase):
    @staticmethod
    def emitter(*registers):
        emitter = gen_x86_64.Emitter(
            {register: "inout" for register in registers}, {}, inversion=True,
        )
        for register in registers:
            emitter.bind_argument(register, "0", "test input")
        return emitter

    def test_cmov_conditions_require_their_own_valid_flag(self):
        emitter = self.emitter("a", "b")
        with self.assertRaisesRegex(gen_x86_64.GenerationError, "ZF read while invalid"):
            emitter.emit_instruction("cmovz {a}, {b}")
        with self.assertRaisesRegex(gen_x86_64.GenerationError, "CF read while invalid"):
            emitter.emit_instruction("cmovc {a}, {b}")

    def test_cmp_and_test_drive_distinct_condition_moves(self):
        emitter = self.emitter("a", "b")
        emitter.emit_instruction("cmp {a}, {b}")
        emitter.emit_instruction("cmovc {a}, {b}")
        emitter.emit_instruction("test {a}, 1")
        emitter.emit_instruction("cmovz {a}, {b}")

    def test_bt_invalidates_zf_but_preserves_defined_cf(self):
        emitter = self.emitter("a", "b")
        emitter.emit_instruction("test {a}, {b}")
        emitter.emit_instruction("bt {a}, 0")
        emitter.emit_instruction("cmovc {a}, {b}")
        with self.assertRaisesRegex(gen_x86_64.GenerationError, "ZF read while invalid"):
            emitter.emit_instruction("cmovz {a}, {b}")

    def test_xor_self_initializes_output_without_read(self):
        emitter = gen_x86_64.Emitter({"z": "out"}, {}, inversion=True)
        emitter.emit_instruction("xor {z:e}, {z:e}")
        self.assertIn("z", emitter.known)
        self.assertTrue(emitter.cf_valid and emitter.of_valid and emitter.zf_valid)

    def test_arithmetic_preserves_only_defined_cf(self):
        emitter = self.emitter("a", "b")
        emitter.emit_instruction("add {a}, {b}")
        self.assertTrue(emitter.cf_valid)
        self.assertFalse(emitter.of_valid or emitter.zf_valid)
        emitter.emit_instruction("adc {a}, {b}")
        with self.assertRaisesRegex(gen_x86_64.GenerationError, "ZF read while invalid"):
            emitter.emit_instruction("cmovz {a}, {b}")

    def test_logic_defines_cleared_cf_of_and_derived_zf(self):
        emitter = self.emitter("a", "b")
        emitter.emit_instruction("and {a}, {b}")
        self.assertTrue(emitter.cf_valid and emitter.of_valid and emitter.zf_valid)
        emitter.emit_instruction("cmovc {a}, {b}")
        emitter.emit_instruction("cmovz {a}, {b}")

    def test_double_shift_and_mul_invalidate_all_flags(self):
        for instruction, registers in (
            ("shld {a}, {b}, cl", ("a", "b", "rcx")),
            ("mul {b}", ("a", "b", "rax", "rdx")),
        ):
            with self.subTest(instruction=instruction):
                emitter = self.emitter(*registers)
                emitter.emit_instruction("test {a}, {b}")
                emitter.emit_instruction(instruction)
                self.assertFalse(emitter.cf_valid or emitter.of_valid or emitter.zf_valid)


class InvertGenerationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = gen_x86_64.INVERT_SOURCE.read_text()
        cls.routines = gen_x86_64.all_invert_routines(cls.source)
        cls.generated = "\n".join(
            routine.text(gen_x86_64.comment_column([routine]))
            for routine in cls.routines
        )

    def test_all_helpers_and_factored_rounds_generate(self):
        self.assertEqual(
            [routine.name for routine in self.routines],
            [
                "divsteps31Round", "divsteps31", "updateAbShift", "addWordsLimb",
                "mulSignedLimb", "normalizeNegative", "normalizeExcess", "reduceOnce",
                "divsteps47Round", "divsteps47",
            ],
        )

    def test_nine_limb_type_is_fully_qualified(self):
        signatures = [routine.signature for routine in self.routines]
        wide = [signature for signature in signatures if "WideLimbs" in signature]
        self.assertEqual(len(wide), 2)
        self.assertTrue(all("PastaAsm.WideLimbs" in signature for signature in wide))
        self.assertNotIn("(value : WideLimbs)", "\n".join(wide))

    def test_every_semantic_source_instruction_has_one_comment(self):
        comments = Counter(re.findall(r"-- (.+)$", self.generated, re.MULTILINE))
        controls = {
            "2:", "mov ecx, 31", "sub ecx, 1", "jnz 2b",
            "mov {count:e}, 47", "sub {count:e}, 1",
        }
        expected = Counter()
        for config in gen_x86_64.INVERT_ROUTINES:
            helper = gen_x86_64.parse_invert_helper(self.source, config)
            for block in helper.blocks:
                expected.update(instruction for instruction in block.instructions
                                if instruction not in controls)
        actual = Counter({instruction: comments[instruction] for instruction in expected})
        self.assertEqual(expected, actual)

    def test_core_routines_still_precede_inversion_routines(self):
        names = [routine.name for routine in gen_x86_64.all_routines()]
        self.assertEqual(
            names[:7],
            ["addMod", "subMod", "mulMontRound", "mulMont", "squareLo", "squareHi", "fromMont"],
        )
        self.assertEqual(names[7:], [routine.name for routine in self.routines])

    def test_update_ab_row_correction_preserves_rust_operation_order(self):
        routine = next(routine for routine in self.routines if routine.name == "updateAbShift")
        generated = routine.text(gen_x86_64.comment_column([routine]))
        self.assertIn("word ((word f ^^^ mask) + bit)", generated)
        self.assertIn("word ((word g ^^^ mask) + bit)", generated)
        self.assertNotIn("word (word f ^^^ mask + bit)", generated)
        self.assertNotIn("word (word g ^^^ mask + bit)", generated)

    def test_fixed_loop_skeleton_post_callout_reads_use_loop_outputs(self):
        routine = next(routine for routine in self.routines if routine.name == "divsteps31")
        skeleton = "\n".join(gen.skeleton(routine))
        self.assertIn(
            "have e_a0_4 : a0_4 = word32 (word32 a1_3) := rfl",
            skeleton,
        )
        self.assertIn(
            "have e_b0_4 : b0_4 = word32 (word32 a2_4) := rfl",
            skeleton,
        )
        self.assertNotIn(
            "have e_a0_4 : a0_4 = word32 (word32 a1) := rfl",
            skeleton,
        )
        self.assertNotIn(
            "have e_b0_4 : b0_4 = word32 (word32 a2) := rfl",
            skeleton,
        )

    def test_all_inversion_routines_generate_shared_skeletons(self):
        for routine in self.routines:
            with self.subTest(routine=routine.name):
                skeleton = gen.skeleton(routine)
                self.assertEqual(
                    skeleton[0],
                    f"  -- generated skeleton for `{routine.name}`: do not edit between the annotations",
                )
                self.assertEqual(skeleton[-1], "  subst hr")
                has_clear = any(line.startswith("  clear_value ") for line in skeleton)
                self.assertEqual(has_clear, routine.name.startswith("divsteps"))


if __name__ == "__main__":
    unittest.main()
