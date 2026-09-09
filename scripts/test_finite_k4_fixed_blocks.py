#!/usr/bin/env python3
"""Exact block reconstruction, cardinal boundary, and corruption controls."""
from copy import deepcopy
from fractions import Fraction as Q
import json
from pathlib import Path
import tempfile
import unittest

import generate_finite_k4_fixed_blocks as generator
from generate_finite_k4_fixed_seeds import DATA


class FixedBlockTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data=json.loads(DATA.read_text())

    def test_all_twenty_blocks_and_three_hundred_pivots(self):
        counts=[]
        for c in self.data['cases']:
            seeds=[generator.blocks(c,self.data['role_keys'],s) for s in range(10)]
            self.assertEqual(len(seeds),10)
            self.assertEqual(sum(len(x['certificates']) for x in seeds),40)
            counts.append(sum(len(d) for x in seeds for L,d in x['certificates'].values()))
        self.assertEqual(counts,[150,150])

    def test_actual_weights_principal_deletion_and_small_entries(self):
        x=generator.blocks(self.data['cases'][0],self.data['role_keys'],0)
        self.assertEqual(x['weight'],[Q(1),Q(4),Q(4),Q(16)])
        self.assertEqual(x['full'][0][0],Q(5424,15625))
        self.assertEqual(x['full'][-1][-1],Q(8581,125000))
        self.assertEqual(x['blocks']['principal'],[r[:-1] for r in x['full'][:-1]])
        self.assertEqual(x['blocks']['interaction'],[[Q(130603,93750)]])
        y=generator.blocks(self.data['cases'][1],self.data['role_keys'],9)
        self.assertEqual(y['weight'][-1],Q(17*17))
        self.assertEqual([len(y['blocks'][k]) for k in ['principal','row','column','interaction']],
                         [15,4,4,1])

    def test_singular_negative_asymmetric_and_inexact_rejections(self):
        for matrix in [[[Q(0)]],[[Q(-1)]],[[Q(1),Q(2)],[Q(0),Q(1)]],
                       [[Q(1),Q(1)],[Q(1),Q(1)]],[[1.0]],[[True]],[],[[Q(1),Q(0)]]]:
            with self.subTest(matrix=matrix),self.assertRaises(ArithmeticError):
                generator.strict_ldl(matrix)

    def test_changed_coefficient_dimension_and_kernel_rejections(self):
        for mutate in [lambda c:c['seed'].__setitem__(0,'0'),
                       lambda c:c.update(n=4),lambda c:c.update(n=1)]:
            c=deepcopy(self.data['cases'][0]);mutate(c)
            with self.assertRaises(ArithmeticError):
                generator.blocks(c,self.data['role_keys'],0)

    def test_exact_ldl_reconstruction_with_signed_off_diagonal(self):
        matrix=[[Q(2),Q(-1)],[Q(-1),Q(2)]]
        lower,diagonal=generator.strict_ldl(matrix)
        self.assertEqual(lower,[[Q(1),Q(0)],[Q(-1,2),Q(1)]])
        self.assertEqual(diagonal,[Q(2),Q(3,2)])

    def test_exact_separate_board_interfaces(self):
        for n in [5,20]:
            text=generator.render_checked(n)
            imports=[line for line in text.splitlines()
                     if line.startswith('import DR.Certificates.FiniteK4FixedCases.')]
            self.assertEqual(imports,[f'import DR.Certificates.FiniteK4FixedCases.M{n}S{s}'
                                      for s in range(10)])
            self.assertEqual(text.count('Gram.strictValid_posDef'),40)
            self.assertEqual(text.count('.full_kernel\n'),10)
        with self.assertRaisesRegex(ArithmeticError,'unsupported fixed board'):
            generator.render_checked(4)

    def test_literal_and_lookup_output_corruption(self):
        x=generator.blocks(self.data['cases'][0],self.data['role_keys'],0)
        for text in [generator.render_lookup(self.data['role_keys']),generator.render_case(x)]:
            with tempfile.TemporaryDirectory() as directory:
                target=Path(directory)/'generated.lean'
                generator.output(target,text,False);generator.output(target,text,True)
                target.write_text(text+'-- changed\n')
                with self.assertRaisesRegex(ArithmeticError,'generated output differs'):
                    generator.output(target,text,True)


if __name__=='__main__':
    unittest.main()
