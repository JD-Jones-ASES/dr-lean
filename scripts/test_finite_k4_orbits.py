#!/usr/bin/env python3
"""Mutation checks for the finite K4 catalogue's reproducible input boundary."""
import unittest
from unittest.mock import patch
import generate_finite_k4_orbits as gen


class CatalogueBoundary(unittest.TestCase):
    def test_missing_pattern(self):
        with patch.object(gen, 'PATTERNS', gen.PATTERNS[:-1]):
            with self.assertRaises(ArithmeticError):
                gen.render()

    def test_missing_position_order(self):
        with patch.object(gen, 'ORDERS', gen.ORDERS[:-1]):
            with self.assertRaises(ArithmeticError):
                gen.render()

    def test_repeated_position_order(self):
        with patch.object(gen, 'ORDERS', gen.ORDERS[:-1] + (gen.ORDERS[0],)):
            with self.assertRaises(ArithmeticError):
                gen.render()

    def test_mixed_multiplier_and_quadratic(self):
        with patch.object(gen, 'ORDERS', ((3,1,2,0,4),) + gen.ORDERS[1:]):
            with self.assertRaises(ArithmeticError):
                gen.render()

    def test_transpose_remains_distinct(self):
        rows = tuple((i,0) for i in range(5))
        cols = tuple((0,i) for i in range(5))
        self.assertNotEqual(gen.role_key(rows), gen.role_key(cols))

    def test_relabel_and_multiplier_orders(self):
        cells = ((70,9),(70,9),(2,4),(70,4),(2,9))
        normalized = ((0,0),(0,0),(1,1),(0,1),(1,0))
        self.assertEqual(gen.role_key(cells), gen.role_key(normalized))
        for p in gen.ORDERS:
            self.assertEqual(gen.role_key(cells), gen.role_key(tuple(cells[i] for i in p)))


if __name__ == '__main__':
    unittest.main()
