#!/usr/bin/env python3
"""Fixed-seed provenance, exact coverage, and mutation controls, including -O."""
from copy import deepcopy
import json
from pathlib import Path
import tempfile
import unittest

import generate_finite_k4_fixed_seeds as generator


class FixedSeedTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = json.loads(generator.DATA.read_text())

    def reject(self, mutate):
        data = deepcopy(self.data)
        mutate(data)
        with self.assertRaises(ArithmeticError):
            generator.validate(data)

    def test_exact_two_case_and_source_order_coverage(self):
        generator.validate(self.data)
        self.assertEqual([(c['m'], c['n']) for c in self.data['cases']], [(5,5),(20,20)])
        self.assertEqual(self.data['role_keys'], generator.independent_role_catalogue())
        self.assertEqual(len(set(self.data['role_keys'])),407)
        self.assertEqual(sum(len(c['seed']) for c in self.data['cases']),814)

    def test_uniform_constants_and_signed_coefficients(self):
        self.assertEqual(str(generator.alpha(5)), '5424/15625')
        self.assertEqual(str(generator.alpha(20)), '14805351/16000000')
        self.assertEqual(self.data['cases'][0]['seed'][-1], '-61206/15625')
        self.assertTrue(all(any(generator.rational(q)<0 for q in c['seed'])
                            for c in self.data['cases']))

    def test_missing_extra_duplicate_case_controls(self):
        mutations = [lambda d:d['cases'].pop(),
                     lambda d:d['cases'].append(deepcopy(d['cases'][0])),
                     lambda d:d['cases'].__setitem__(1,deepcopy(d['cases'][0])),
                     lambda d:d['cases'].reverse(),
                     lambda d:d['cases'][0].update(m=True),
                     lambda d:d['cases'][0].update(extra=0),
                     lambda d:d.update(extra=0)]
        for mutate in mutations:
            with self.subTest(mutation=mutate):
                self.reject(mutate)

    def test_coefficient_precision_and_coverage_controls(self):
        mutations = [lambda d:d['cases'][0]['seed'].pop(),
                     lambda d:d['cases'][1]['seed'].append('0'),
                     lambda d:d['cases'][0]['seed'].__setitem__(1,0.5),
                     lambda d:d['cases'][0]['seed'].__setitem__(1,True),
                     lambda d:d['cases'][0]['seed'].__setitem__(1,'2/4'),
                     lambda d:d['cases'][0]['seed'].__setitem__(1,'1/0')]
        for mutate in mutations:
            with self.subTest(mutation=mutate):
                self.reject(mutate)

    def test_equation_and_role_order_mutations(self):
        for mutate in [lambda d:d['cases'][0]['seed'].__setitem__(0,'0'),
                       lambda d:d['cases'][1]['seed'].__setitem__(0,'0'),
                       lambda d:d['cases'][0].update(alpha='0'),
                       lambda d:d['role_keys'].reverse(),
                       lambda d:d['role_keys'].__setitem__(1,d['role_keys'][0])]:
            with self.subTest(mutation=mutate):
                self.reject(mutate)

    def test_provenance_and_claim_boundary_controls(self):
        for mutate in [lambda d:d.update(scope='PSD and uniform maximum'),
                       lambda d:d.update(template_sha256='0'*64),
                       lambda d:d['source_sha256'].update({'K4_FIVE_BY_FIVE.md':'0'*64})]:
            with self.subTest(mutation=mutate):
                self.reject(mutate)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            (path/'K4_FIVE_BY_FIVE.md').write_text('changed source\n')
            with self.assertRaisesRegex(ArithmeticError,'pinned source hash'):
                generator.extract_sources(path)

    def test_literal_only_extraction(self):
        literal = repr(tuple(self.data['cases'][0]['seed']))
        wrap = lambda body: "```bash\npython - <<'PY'\n"+body+'\nPY\n```\n'
        self.assertEqual(generator.extract_markdown_seed(wrap('SEED = '+literal)),
                         self.data['cases'][0]['seed'])
        for body in ['SEED = tuple('+literal+')',
                     'SEED = '+literal+'\nSEED = '+literal,
                     'OTHER = '+literal,
                     'SEED = OTHER = '+literal,
                     'SEED = '+repr(self.data['cases'][0]['seed'])]:
            with self.subTest(body=body[:45]), self.assertRaises(ArithmeticError):
                generator.extract_markdown_seed(wrap(body))

    def test_generated_output_corruption(self):
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory)/'data.lean'
            content = generator.render(self.data)
            generator.output(target,content,False)
            generator.output(target,content,True)
            target.write_text(content.replace('5424/15625','0',1))
            with self.assertRaisesRegex(ArithmeticError,'generated output differs'):
                generator.output(target,content,True)


if __name__ == '__main__':
    unittest.main()
