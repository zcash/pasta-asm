#!/usr/bin/env python3
# Copyright (c) 2026 the pasta-asm contributors.
# SPDX-License-Identifier: Apache-2.0
"""Focused fail-closed tests for the AArch64 inversion transcription generator."""

from pathlib import Path
import re
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))

import asm_source
import gen
import gen_aarch64


class AArch64InvertGeneratorTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = gen_aarch64.INVERT.read_text()
        cls.configs = {config.rust_name: config for config in gen_aarch64.INVERT_ROUTINES}

    def mutate_function(self, name, old, new):
        config = self.configs[name]
        parsed = asm_source.parse_helper_function(
            self.source, name, config.signature, config.regions,
            allowed_options={"pure", "nomem", "nostack"},
            required_options={"pure", "nomem", "nostack"},
            inout_expression_outputs=(
                {f"value[{index}]" for index in range(4)} if name == "reduce_once" else set()
            ),
        )
        function = self.source[parsed.start:parsed.end]
        self.assertEqual(function.count(old), 1, old)
        return self.source[:parsed.start] + function.replace(old, new) + self.source[parsed.end:]

    def emit(self, name, source=None):
        config = self.configs[name]
        source = self.source if source is None else source
        return (gen_aarch64.emit_loop_invert(source, config) if config.loop_count
                else [gen_aarch64.emit_straight_invert(source, config)])

    def test_all_eight_source_blocks_and_two_round_helpers_are_registered(self):
        names = [routine.name for routine in gen_aarch64.all_routines()]
        self.assertEqual(names[5:], [
            "divsteps31Round", "divsteps31", "updateAB", "addWords", "mulSigned",
            "divsteps47Round", "divsteps47", "normalizeCoefficient", "redcMont",
            "reduceOnce",
        ])
        self.assertEqual([config.rust_name for config in gen_aarch64.INVERT_ROUTINES], [
            "divsteps_31", "update_ab", "add_words", "mul_signed", "divsteps_47",
            "normalize_coefficient", "redc", "reduce_once",
        ])

    def test_composition_facing_signatures_and_shared_bitpattern_types(self):
        routines = {routine.name: routine for routine in gen_aarch64.all_routines()}
        expected = {
            "divsteps31Round": "def divsteps31Round (bias : Nat) (acc : Divsteps31State) : Divsteps31State :=",
            "divsteps31": "def divsteps31 (a b : Limbs) : InvertMatrix :=",
            "updateAB": "def updateAB (a b : Limbs) (f g : Nat) : UpdateABResult :=",
            "addWords": "def addWords (lhs rhs : WideLimbs) : WideLimbs :=",
            "mulSigned": "def mulSigned (value : WideLimbs) (scalar : Nat) : WideLimbs :=",
            "divsteps47Round": "def divsteps47Round (acc : Divsteps47State) : Divsteps47State :=",
            "divsteps47": "def divsteps47 (a b : Nat) : InvertRow :=",
            "normalizeCoefficient": (
                "def normalizeCoefficient (value : WideLimbs) (modulus : Limbs) : "
                "CoefficientSplit :="
            ),
            "redcMont": "def redcMont (low high modulus : Limbs) (inv : Nat) : Limbs :=",
            "reduceOnce": "def reduceOnce (value modulus : Limbs) : Limbs :=",
        }
        self.assertEqual({name: routines[name].signature for name in expected}, expected)
        generated = gen_aarch64.gen_program()
        self.assertIn("import PastaAsm.Inversion", generated)
        self.assertNotIn("structure WideLimbs", generated)
        self.assertNotIn("structure InvertMatrix", generated)

    def test_every_real_helper_parses_with_exact_surrounding_rust(self):
        for config in gen_aarch64.INVERT_ROUTINES:
            with self.subTest(helper=config.rust_name):
                block = gen_aarch64.parse_invert_helper(self.source, config)
                self.assertGreater(len(block.instructions), 0)
                self.assertEqual(block.options, {"pure", "nomem", "nostack"})

    def test_redc_registers_all_74_upstream_instructions_and_critical_epilogue(self):
        block = gen_aarch64.parse_invert_helper(self.source, self.configs["redc"])
        self.assertEqual(len(block.instructions), 74)
        self.assertEqual(block.instructions[-9:], (
            "subs {t0}, {r0}, {p0}",
            "sbcs {t1}, {r1}, {p1}",
            "sbcs {t2}, {r2}, {p2}",
            "sbcs {t3}, {r3}, {p3}",
            "sbcs xzr, {r4}, xzr",
            "csel {r0}, {r0}, {t0}, lo",
            "csel {r1}, {r1}, {t1}, lo",
            "csel {r2}, {r2}, {t2}, lo",
            "csel {r3}, {r3}, {t3}, lo",
        ))
        routine = self.emit("redc")[0]
        self.assertEqual(routine.signature,
                         "def redcMont (low high modulus : Limbs) (inv : Nat) : Limbs :=")
        self.assertEqual(routine.result, "  ⟨r0, r1, r2, r3⟩")
        argument_bindings = {
            entry["name"]: entry["expr"] for entry in routine.emitter.entries
            if entry["pc"] is None
        }
        self.assertEqual(argument_bindings, {
            **{f"r{i}": f"low.l{i}" for i in range(4)},
            **{f"h{i}": f"high.l{i}" for i in range(4)},
            **{f"p{i}": f"modulus.l{i}" for i in range(4)},
            "inv": "inv",
        })
        generated_pcs = {entry["pc"] for entry in routine.emitter.entries
                         if entry["pc"] is not None}
        self.assertEqual(generated_pcs, set(range(74)))

    def test_fixed_loops_are_factored_from_one_source_body_and_called_exactly(self):
        for rust_name, count in (("divsteps_31", 31), ("divsteps_47", 47)):
            with self.subTest(helper=rust_name):
                round_routine, wrapper = self.emit(rust_name)
                calls = [entry for entry in wrapper.emitter.entries if entry["fact"][0] == "call"]
                self.assertEqual(len(calls), count)
                self.assertEqual(
                    sum(entry["fact"][0] == "call" for entry in round_routine.emitter.entries), 0
                )
                block = gen_aarch64.parse_invert_helper(self.source, self.configs[rust_name])
                instructions = gen_aarch64.instruction_ir(block.instructions)
                label, branch = gen_aarch64.loop_boundaries(instructions, self.configs[rust_name])
                body_pcs = set(range(label + 1, branch))
                generated_pcs = {entry["pc"] for entry in round_routine.emitter.entries
                                 if entry["pc"] is not None}
                self.assertEqual(generated_pcs, body_pcs)
                for pc in body_pcs:
                    self.assertTrue(any(entry["comment"] == instructions[pc][2]
                                        for entry in round_routine.emitter.entries
                                        if entry["pc"] == pc))

    def test_divsteps47_wrapper_source_names_match_skeleton_ssa(self):
        _round, wrapper = self.emit("divsteps_47")
        source = "\n".join(code for code, _comment in wrapper.lines if code is not None)
        binders = re.findall(r"^  let ([A-Za-z0-9_']+) :=", source, re.MULTILINE)
        extracted = []
        for line in gen.skeleton(wrapper):
            match = re.match(r"  extract_lets \+onlyGivenNames (.*?) at hr$", line)
            if match:
                extracted.extend(match.group(1).split())

        self.assertEqual(len(binders), len(set(binders)))
        self.assertEqual(
            extracted,
            [name for name in binders if name not in {"f1", "g1"}],
        )
        self.assertIn("let a' := a", source)
        self.assertIn(
            "let round1 := divsteps47Round ⟨a', cnt, b', f0, g0, f1, g1⟩", source
        )
        skeleton = "\n".join(gen.skeleton(wrapper))
        self.assertIn("let f1 := 0", source)
        self.assertNotIn("extract_lets +onlyGivenNames f1 at hr", skeleton)
        self.assertNotIn("have e_f1 : f1 = 0 := rfl", skeleton)
        self.assertIn(
            "have e_round1 : round1 = divsteps47Round ⟨a', cnt, b', f0, g0, g0, f0⟩ := rfl",
            skeleton,
        )
        self.assertIn("let f1_1 := round1.f1", source)
        self.assertIn(
            "let round2 := divsteps47Round ⟨a_1, cnt_1, b_1, f0_1, g0_1, f1_1, g1_1⟩",
            source,
        )
        self.assertEqual(wrapper.result, "  ⟨f1_47, g1_47⟩")

    def test_divsteps31_wrapper_retains_historical_register_rebinding(self):
        _round, wrapper = self.emit("divsteps_31")
        source = "\n".join(code for code, _comment in wrapper.lines if code is not None)
        self.assertIn("let a3 := cselNe z a3 a2", source)
        self.assertNotIn("let a3_1 := cselNe z a3 a2", source)
        self.assertEqual(wrapper.result, "  ⟨f0, g0, f1, g1⟩")

    def test_counter_branch_and_decrement_mutations_are_rejected(self):
        mutations = (
            ("divsteps_31", "cnt = inout(reg) 31_u64 => _,", "cnt = inout(reg) 30_u64 => _,",
             "declaration 11 does not match expected"),
            ("divsteps_47", '"cbnz {cnt}, 2b",', '"cbnz {cnt}, 3b",',
             "expected one `2:` / `cbnz cnt,2b` loop"),
            ("divsteps_47", '"sub {cnt}, {cnt}, #1",', '"sub {cnt}, {cnt}, #2",',
             "expected one `sub cnt,cnt,#1` in loop"),
        )
        for name, old, new, message in mutations:
            with self.subTest(helper=name, mutation=message):
                source = self.mutate_function(name, old, new)
                with self.assertRaisesRegex(ValueError, re.escape(message)):
                    self.emit(name, source)

    def test_loop_body_state_change_is_rejected(self):
        source = self.mutate_function(
            "divsteps_47", '"and {t0}, {b}, {odd}",', '"and {t0}, {f0}, {odd}",'
        )
        with self.assertRaisesRegex(ValueError, "derived loop state .* differs from contract"):
            self.emit("divsteps_47", source)

    def test_operand_wiring_mutations_are_rejected(self):
        mutations = (
            ("mul_signed", "scalar = in(reg) scalar,", "scalar = in(reg) value[0],"),
            ("add_words", "r0 = in(reg) rhs[0],", "r0 = in(reg) lhs[0],"),
            ("normalize_coefficient", "w4 = inout(reg) value[4] => w4,",
             "w4 = inout(reg) value[5] => w4,"),
            ("redc", "h0 = in(reg) high[0],", "h0 = in(reg) low[0],"),
            ("redc", "p2 = in(reg) modulus[2],", "p2 = in(reg) modulus[3],"),
            ("redc", "inv = in(reg) inv,", "inv = in(reg) modulus[0],"),
        )
        for name, old, new in mutations:
            with self.subTest(helper=name):
                source = self.mutate_function(name, old, new)
                with self.assertRaisesRegex(
                    asm_source.GenerationError, rf"{name}: declaration \d+ does not match expected"
                ):
                    self.emit(name, source)

    def test_surrounding_rust_mutation_is_rejected(self):
        source = self.mutate_function(
            "normalize_coefficient",
            "let low = [value[0], value[1], value[2], value[3]];",
            "let low = [value[1], value[0], value[2], value[3]];",
        )
        with self.assertRaisesRegex(asm_source.GenerationError, "Rust region 'before asm'"):
            self.emit("normalize_coefficient", source)
        source = self.mutate_function(
            "redc",
            "let (mut r0, mut r1, mut r2, mut r3) = (low[0], low[1], low[2], low[3]);",
            "let (mut r0, mut r1, mut r2, mut r3) = (low[1], low[0], low[2], low[3]);",
        )
        with self.assertRaisesRegex(asm_source.GenerationError, "Rust region 'before asm'"):
            self.emit("redc", source)
        source = self.mutate_function(
            "redc", "[r0, r1, r2, r3]", "[r1, r0, r2, r3]"
        )
        with self.assertRaisesRegex(asm_source.GenerationError, "Rust region 'after asm'"):
            self.emit("redc", source)

    def test_uninitialized_read_and_input_only_write_are_rejected(self):
        source = self.mutate_function(
            "add_words", '"adds {o0}, {o0}, {r0}",', '"adds {o0}, {o0}, {missing}",'
        )
        with self.assertRaisesRegex(ValueError, "missing read before being written"):
            self.emit("add_words", source)
        source = self.mutate_function(
            "add_words", '"adds {o0}, {o0}, {r0}",', '"adds {r0}, {o0}, {r0}",'
        )
        with self.assertRaisesRegex(ValueError, "input-only register r0"):
            self.emit("add_words", source)

    def test_illegal_shift_and_bitfield_encodings_are_rejected(self):
        emitter = gen_aarch64.Emitter([], {"d": "out", "a": "in", "b": "in"})
        emitter.bind("a", "1", "argument", reads=(), fact=("const", 1))
        emitter.bind("b", "1", "argument", reads=(), fact=("const", 1))
        cases = (
            ("lsl", ["d", "a", "#64"], "shift immediate outside 0..63"),
            ("extr", ["d", "a", "b", "#64"], "shift immediate outside 0..63"),
            ("ubfx", ["d", "a", "#0", "#0"], "invalid bitfield range"),
            ("sbfx", ["d", "a", "#63", "#2"], "invalid bitfield range"),
            ("bfxil", ["d", "a", "#32", "#33"], "invalid bitfield range"),
        )
        emitter.bind("d", "0", "argument", reads=(), fact=("const", 0))
        for op, operands, message in cases:
            with self.subTest(op=op, operands=operands):
                with self.assertRaisesRegex(ValueError, message):
                    emitter.step(op, operands, op)
        with self.assertRaisesRegex(ValueError, "unsupported shifted operand"):
            emitter.step("adds", ["d", "a", "b", "ror", "#1"], "adds d,a,b,ror #1")

    def test_reduce_once_direct_places_are_narrowly_allowlisted(self):
        self.emit("reduce_once")
        source = self.mutate_function(
            "reduce_once", "r0 = inout(reg) value[0],", "r0 = inout(reg) value[4],"
        )
        with self.assertRaisesRegex(asm_source.GenerationError, "must bind an allowed output"):
            self.emit("reduce_once", source)

    def test_all_inversion_routines_generate_shared_skeletons(self):
        for routine in gen_aarch64.all_routines()[5:]:
            with self.subTest(routine=routine.name):
                skeleton = gen.skeleton(routine)
                self.assertEqual(
                    skeleton[0],
                    f"  -- generated skeleton for `{routine.name}`: do not edit between the annotations",
                )
                self.assertEqual(skeleton[-1], "  subst hr")

    def test_generated_outputs_register_transcription_and_vectors(self):
        outputs = dict(gen_aarch64.generated_outputs())
        self.assertIn(gen_aarch64.OUT_PROGRAM, outputs)
        self.assertIn(gen_aarch64.OUT_VECTORS, outputs)
        self.assertIn(gen_aarch64.OUT_INVERT_VECTORS, outputs)
        for name in ("divsteps31", "updateAB", "addWords", "mulSigned", "divsteps47",
                     "normalizeCoefficient", "redcMont", "reduceOnce"):
            self.assertIn(f"def {name} ", outputs[gen_aarch64.OUT_PROGRAM])


if __name__ == "__main__":
    unittest.main()
