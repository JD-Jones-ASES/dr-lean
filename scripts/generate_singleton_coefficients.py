#!/usr/bin/env python3
"""Reproduce the order-five singleton coefficient table using exact arithmetic.

This optional discovery/reproduction tool needs SymPy. Its output is not a
proof: Lean checks the literal polynomial identity, every coefficient
conversion, and every closed-interval positivity bound independently.
The input formula is the singleton numerator in the order-five proof,
recorded literally in SpectralFiveSingletonPolynomial.lean.
"""
from argparse import ArgumentParser
from fractions import Fraction
from math import comb
from pathlib import Path
import json
import sympy as sp


def coefficients():
    t, x, y = sp.symbols("t x y")
    gamma = sp.Rational(24, 625)
    u, v = sp.Rational(23, 50) * t * x, t * y / 2
    lower, q, height = 1 - sp.Rational(23, 50) * t, 1 - t, 1 + t / 2
    energy = height * (gamma - (1 - gamma) * t**2 / 5)
    denominator = sp.Rational(19, 100) * q - energy
    crossing = energy * (2 * q - energy)
    a = 2 * denominator * (2 + v - u) - crossing
    s = 2 * denominator * (8 + u - v) - crossing
    r = 2 * denominator * (2 - 3 * u - v) - crossing
    c = 2 * denominator * (2 * lower + u + v) - crossing
    common = (1 - u)**2 * lower * (1 + v)
    inner = (
        (5 + t**2) * 16384 * denominator**3
        * (r * lower * (1 + v) + c * (1 - u)**2)
        - t**2 * (16 * denominator)**4 * common
        - sp.Rational(61, 32) * s**4 * common * (5 + t**2)
    )
    polynomial = sp.Poly(sp.expand(
        a * inner - 4 * denominator * (gamma * (5 + t**2) - t**2)
        * (16 * denominator)**4 * common
    ), t, x, y)
    if polynomial.degree_list() != (36, 7, 6) or len(polynomial.terms()) != 1049:
        raise ValueError("Unexpected literal polynomial degree or support")
    scale = int(sp.ilcm(*(c.q for _, c in polynomial.terms())))
    power = {m: Fraction(int(c * scale)) for m, c in polynomial.terms()}
    rows = []
    for i in range(8):
        for j in range(7):
            row = [Fraction(0) for _ in range(37)]
            for (a, b, c), value in power.items():
                if b <= i and c <= j:
                    row[a] += value * Fraction(comb(i, b), comb(7, b)) * Fraction(comb(j, c), comb(6, c))
            rows.append(row)
    return {
        "scale": str(scale),
        "terms": [[*m, str(c)] for m, c in power.items()],
        "rows": [[str(c) for c in row] for row in rows],
    }


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    args.output.write_text(json.dumps(coefficients()) + "\n")
