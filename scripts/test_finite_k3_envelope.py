#!/usr/bin/env python3
"""Persistent exact coverage/corruption controls for finite K3 generation."""
import copy
import json
import unittest
from fractions import Fraction as F
from generate_finite_k3_envelope import SOURCE,load_cases,case_blocks,exact_ldl,EXPECTED,render_manifest,validate_manifest

class TextSource:
    def __init__(self,raw):self.raw=raw
    def read_text(self):return json.dumps(self.raw)

class FiniteK3EnvelopeControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.raw=json.loads(SOURCE.read_text())
        cls.cases=load_cases()
    def reject(self,change):
        raw=copy.deepcopy(self.raw);change(raw)
        with self.assertRaises(ArithmeticError):load_cases(TextSource(raw))
    def test_exact_coverage(self):
        self.assertEqual(tuple(self.cases),EXPECTED)
        self.assertEqual(len(self.cases),1330)
    def test_missing(self):self.reject(lambda r:r['cases'].pop())
    def test_extra(self):
        self.reject(lambda r:r['cases'].append({'m':10,'n':10,'seed':['0']*93}))
    def test_duplicate_with_same_count(self):
        self.reject(lambda r:r['cases'].__setitem__(1,r['cases'][0]))
    def test_reordered(self):
        def change(r):r['cases'][0],r['cases'][1]=r['cases'][1],r['cases'][0]
        self.reject(change)
    def test_wrong_coefficient_count(self):self.reject(lambda r:r['cases'][0]['seed'].pop())
    def test_float_dimension(self):self.reject(lambda r:r['cases'][0].__setitem__('m',4.0))
    def test_float_coefficient(self):self.reject(lambda r:r['cases'][0]['seed'].__setitem__(0,0.5))
    def test_changed_coefficient_breaks_actual_kernel(self):
        coeff=list(self.cases[(4,6)]);coeff[0]+=F(1,200)
        with self.assertRaises(ArithmeticError):case_blocks(4,6,coeff)
    def test_zero_pivot(self):
        with self.assertRaises(ArithmeticError):exact_ldl([[F(0)]])
    def test_negative_pivot(self):
        with self.assertRaises(ArithmeticError):exact_ldl([[F(-1)]])
    def test_nonsymmetric(self):
        with self.assertRaises(ArithmeticError):exact_ldl([[F(1),F(1)],[F(0),F(1)]])
    def test_manifest_exact(self):validate_manifest(json.loads(render_manifest()))
    def test_manifest_missing_case(self):
        raw=json.loads(render_manifest());raw['cases'].pop()
        with self.assertRaises(ArithmeticError):validate_manifest(raw)
    def test_manifest_duplicate_case(self):
        raw=json.loads(render_manifest());raw['cases'][1]=raw['cases'][0]
        with self.assertRaises(ArithmeticError):validate_manifest(raw)
    def test_manifest_extra_case(self):
        raw=json.loads(render_manifest());raw['cases'].append(raw['cases'][0])
        with self.assertRaises(ArithmeticError):validate_manifest(raw)
    def test_manifest_reordered(self):
        raw=json.loads(render_manifest());raw['cases'][0],raw['cases'][1]=raw['cases'][1],raw['cases'][0]
        with self.assertRaises(ArithmeticError):validate_manifest(raw)
    def test_manifest_shard_gap(self):
        raw=json.loads(render_manifest());raw['shards'][0]['upper']-=1
        with self.assertRaises(ArithmeticError):validate_manifest(raw)
    def test_exact_endpoint_blocks(self):
        for shape in ((4,6),(4,959)):
            blocks=case_blocks(*shape,self.cases[shape])
            self.assertEqual([len(x[0])for pair in blocks for x in pair],[4,7,4,11,4,7,4,11])

if __name__=='__main__':unittest.main()
