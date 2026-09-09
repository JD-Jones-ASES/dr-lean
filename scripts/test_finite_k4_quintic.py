#!/usr/bin/env python3
"""Persistent exact counting, boundary and corruption controls; works under -O."""
from copy import deepcopy
from pathlib import Path
import tempfile
import unittest

import generate_finite_k4_quintic as generator


class QuinticTemplateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = generator.build_data()

    def reject(self, mutate):
        damaged = deepcopy(self.data)
        mutate(damaged)
        with self.assertRaises(ArithmeticError):
            generator.validate_data(damaged)

    def test_complete_literal_coverage(self):
        d = self.data
        self.assertEqual((len(d['patterns']), len(d['role_keys']), len(d['rows'])), (52,407,91))
        self.assertEqual(sum(map(len,d['rows'])),407)
        self.assertEqual(max(map(len,d['rows'])),10)
        self.assertEqual(sorted(i for row in d['rows'] for i,_ in row),list(range(407)))
        generator.check_four_row_catalogue(d)

    def test_repetition_corrections(self):
        same = ((0,0),)*5
        self.assertEqual(generator.weight6(same),6)
        self.assertEqual(generator.weight6(((0,0),(0,0),(1,0),(2,0),(3,0))),2)
        self.assertEqual(generator.weight6(((0,0),(0,1),(1,0),(2,0),(3,0))),1)
        self.assertEqual(self.data['triple_weights'][0],[6]*10)
        self.assertEqual(self.data['multiplicity'][0],1)
        self.assertEqual(self.data['successes'][0],0)
        self.assertEqual(self.data['deleted_successes'][0],0)

    def test_fully_distinct_and_inclusive_or_boundaries(self):
        d = self.data
        flat = 52*51+51
        eq = d['pattern_equation'][51][51]
        self.assertEqual((d['multiplicity'][eq],d['successes'][eq],d['deleted_successes'][flat]),
                         (120,120,5))
        self.assertEqual(d['triple_weights'][flat],[1]*10)
        self.assertEqual(generator.success([(0,j) for j in range(4)]),1)
        self.assertEqual(generator.success([(i,0) for i in range(4)]),1)
        self.assertEqual(generator.success([(0,0),(0,1),(1,0),(1,1)]),0)

    def test_first_position_and_choice_order(self):
        self.assertEqual(generator.first_position_pattern((7,9,7,12,9)),(0,1,0,3,1))
        self.assertEqual(generator.TRIPLE_ORDERS[0],(0,1,2,3,4))
        self.assertEqual(generator.TRIPLE_ORDERS[-1],(2,3,4,0,1))
        self.assertEqual(len(set(generator.TRIPLE_ORDERS)),10)

    def test_missing_extra_duplicate_and_type_controls(self):
        mutations = [lambda d:d.pop('rows'), lambda d:d.update(extra=0),
                     lambda d:d.update(scope='endpoint proof'),
                     lambda d:d['patterns'].pop(),
                     lambda d:d['triple_orders'].__setitem__(1,d['triple_orders'][0]),
                     lambda d:d['triple_roles'].append(d['triple_roles'][0]),
                     lambda d:d['multiplicity'].__setitem__(0,True),
                     lambda d:d['successes'].__setitem__(0,0.0)]
        for mutate in mutations:
            with self.subTest(mutation=mutate):
                self.reject(mutate)

    def test_source_and_literal_equation_mutations(self):
        for mutate in [lambda d:d['source_sha256'].update({'quintic_certificate.py':'0'*64}),
                       lambda d:d['rows'][0][0].__setitem__(1,d['rows'][0][0][1]+1),
                       lambda d:d['multiplicity'].__setitem__(0,2),
                       lambda d:d['successes'].__setitem__(0,1),
                       lambda d:d['role_coefficient'].__setitem__(0,100)]:
            with self.subTest(mutation=mutate):
                self.reject(mutate)

    def test_actual_local_relation_mutations(self):
        for mutate in [lambda d:d['triple_patterns'][0].__setitem__(0,1),
                       lambda d:d['pattern_equation'][0].__setitem__(0,1),
                       lambda d:d['triple_roles'][0].__setitem__(0,1),
                       lambda d:d['triple_weights'][0].__setitem__(0,1),
                       lambda d:d['deleted_successes'].__setitem__(0,1)]:
            with self.subTest(mutation=mutate):
                self.reject(mutate)

    def test_restricted_coverage_mutations(self):
        for mutate in [lambda d:d['four_row_equations'].pop(),
                       lambda d:d['four_row_equations'].__setitem__(1,d['four_row_equations'][0]),
                       lambda d:d['four_square_equations'].reverse(),
                       lambda d:d['four_row_roles'].pop()]:
            with self.subTest(mutation=mutate):
                self.reject(mutate)

    def test_sparse_selector_and_padding_controls(self):
        self.assertEqual(self.data['row_terms'][0][1:],[ [0,0] for _ in range(9)])
        self.assertEqual(self.data['triple_slots'][0],[0]*10)
        for mutate in [lambda d:d['row_terms'][0][1].__setitem__(1,1),
                       lambda d:d['triple_slots'][0].__setitem__(0,1),
                       lambda d:d['triple_slots'][0].__setitem__(0,10)]:
            with self.subTest(mutation=mutate):
                self.reject(mutate)

    def test_pinned_source_bytes_and_output_change(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            (path/'quintic_certificate.py').write_text('changed source\n')
            with self.assertRaisesRegex(ArithmeticError,'pinned source hash'):
                generator.audit_source(self.data,path)
            target = path/'output.json'
            generator.output(target,'exact\n',False)
            generator.output(target,'exact\n',True)
            target.write_text('changed\n')
            with self.assertRaisesRegex(ArithmeticError,'generated output differs'):
                generator.output(target,'exact\n',True)


if __name__ == '__main__':
    unittest.main()
