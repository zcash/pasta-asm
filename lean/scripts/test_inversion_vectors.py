#!/usr/bin/env python3
# Copyright (c) 2026 the pasta-asm contributors.
# SPDX-License-Identifier: Apache-2.0
"""Independent expected inversion outputs, not hardware inversion captures."""
import sys
import unittest

# Running this source-tree test should not leave lean/scripts/__pycache__ behind.
sys.dont_write_bytecode = True

import gen
import gen_aarch64
import gen_x86_64


class InversionVectorTests(unittest.TestCase):
    def test_corpus_contract_and_montgomery_relation(self):
        vectors = gen.inversion_vectors(gen.VECTORS.read_text().splitlines())
        self.assertEqual({key for key, _, _ in vectors}, set(gen.FIELDS))
        self.assertEqual(len(vectors), len({(key, value) for key, value, _ in vectors}))
        for key, value, result in vectors:
            p = gen.MODULUS_INT[key]
            self.assertLess(value, p)
            self.assertLess(result, p)
            if value == 0:
                self.assertEqual(result, 0)
            else:
                self.assertEqual(value * result % p, pow(2, 512, p))
                # Independent Fermat exponentiation checks the inverse calculation.
                self.assertEqual(result, pow(value, p - 2, p) * pow(2, 512, p) % p)

    def test_filters_and_deduplicates_operands_not_expected_results(self):
        p = gen.MODULUS_INT['Fp']
        row = lambda op, values: ' '.join([op, 'Fp'] + [f'{x:064x}' for x in values])
        lines = [row('MUL', [0, 1, 42]), row('SQR', [1, 43]),
                 row('FROM', [p, 44]), row('FROM', [p - 1, 45])]
        vectors = gen.inversion_vectors(lines)
        self.assertEqual([value for _, value, _ in vectors], [0, 1, p - 1])
        self.assertEqual(vectors[0][2], 0)
        self.assertEqual(vectors[1][2], pow(2, 512, p))
        self.assertEqual(vectors[2][2], -pow(2, 512, p) % p)

    def test_generated_composition_checks_for_both_architectures(self):
        lines = gen.VECTORS.read_text().splitlines()
        cases = (
            (gen_aarch64, gen_aarch64.OUT_INVERT_VECTORS, "AArch64"),
            (gen_x86_64, gen_x86_64.OUTPUT_INVERT_VECTORS, "x86-64"),
        )
        for backend, path, architecture in cases:
            with self.subTest(backend=backend.__name__):
                generated = backend.gen_invert_vectors(lines)
                outputs = dict(backend.generated_outputs())
                self.assertEqual(generated.count("example :"), 34)
                self.assertEqual(generated.count("decide +kernel"), 34)
                self.assertIn(f"actual {architecture} `invert` composition", generated)
                self.assertIn("expected values are derived", generated)
                self.assertIn("independently by modular arithmetic", generated)
                self.assertIn("not captured from", generated)
                self.assertIn("input * result = R^2 (mod p)", generated)
                self.assertIn("supplement, but do not replace", generated)
                self.assertIn("every distinct canonical corpus operand is included", generated)
                self.assertEqual(outputs[path], generated)
                self.assertEqual(path.read_text(), generated)

    def test_malformed_corpus_rejected(self):
        with self.assertRaises(ValueError):
            gen.inversion_vectors(['INVERT Fp 0'])


if __name__ == '__main__':
    unittest.main()
