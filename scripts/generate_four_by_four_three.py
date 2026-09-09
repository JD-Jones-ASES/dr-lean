#!/usr/bin/env python3
"""Reconstruct the Lab's 17-entry K=3 4x4 seed and its shifted exact LDL data.

Only integer/Fraction arithmetic is used. The generated Lean file contains
witness data; Gram validity against the formula-defined matrix is checked by
the Lean kernel separately. This script does not establish a probability bound.
"""
import argparse
from fractions import Fraction as F
from pathlib import Path


def cell_class(a):
    r, c = divmod(a, 4)
    return (0 if c == 0 else 1) if r == 0 else (2 if c == 0 else 3)


def entry(a, b):
    u, v = cell_class(a), cell_class(b)
    ra, ca = divmod(a, 4)
    rb, cb = divmod(b, 4)
    if u == 0 or v == 0:
        return 39 if u == v else (-3 if max(u, v) == 3 else -2)
    if u == v == 1:
        return 121 if ca == cb else -25
    if u == v == 2:
        return 121 if ra == rb else -25
    if {u, v} == {1, 2}:
        return 21
    if {u, v} == {1, 3}:
        return 48 if ca == cb else -46
    if {u, v} == {2, 3}:
        return 48 if ra == rb else -46
    return 123 if a == b else (17 if ra == rb or ca == cb else -25)


def rational(q):
    if q.denominator == 1:
        return str(q.numerator)
    return f"({q.numerator}/{q.denominator})"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    q = [[F(entry(i, j), 64) for j in range(16)] for i in range(16)]
    if not all(q[i][j] == q[j][i] for i in range(16) for j in range(16)):
        raise ArithmeticError("The 4x4 seed is not symmetric")
    if not all(sum(row) == 0 for row in q):
        raise ArithmeticError("The 4x4 seed does not have the constant kernel")
    shift = [[q[i][j] - F(1, 20) * (F(i == j) - F(1, 16))
              for j in range(16)] for i in range(16)]
    if not all(sum(row) == 0 for row in shift):
        raise ArithmeticError("The shifted 4x4 seed does not have the constant kernel")
    lower = [[F(0) for _ in range(15)] for _ in range(15)]
    weights = []
    for j in range(15):
        pivot = shift[j][j] - sum(lower[j][k] ** 2 * weights[k] for k in range(j))
        if pivot <= 0:
            raise ArithmeticError(f"Nonpositive 4x4 shifted LDL pivot {j}: {pivot}")
        weights.append(pivot)
        lower[j][j] = F(1)
        for i in range(j + 1, 15):
            lower[i][j] = (shift[i][j] - sum(lower[i][k] * weights[k] * lower[j][k]
                                          for k in range(j))) / pivot
    factor = list(zip(*lower))
    if not all(shift[i][j] == sum(weights[k] * factor[k][i] * factor[k][j]
                                for k in range(15))
               for i in range(15) for j in range(15)):
        raise ArithmeticError("The exact 4x4 principal Gram reconstruction failed")
    out = ["import DR.Certificates.Gram", "", "/-! Exact data generated from the 17 rational entries in Lab FOUR_BY_FOUR.md.",
           "Regenerate with scripts/generate_four_by_four_three.py; Lean separately checks every entry. -/",
           "namespace DittertRybin.Certificates", "", "def fourByFourThreeGram : GramCertificate 15 15 where",
           "  weights := ![" + ", ".join(map(rational, weights)) + "]",
           "  factor := ![" + ",\n    ".join("![" + ", ".join(map(rational, row)) + "]" for row in factor) + "]",
           "", "end DittertRybin.Certificates", ""]
    path = Path(__file__).resolve().parents[1] / "DR/Certificates/FourByFourThreeData.lean"
    content = "\n".join(out)
    if args.check:
        if not path.exists() or path.read_text() != content:
            raise ArithmeticError(f"Generated certificate changed: {path}")
    elif not path.exists() or path.read_text() != content:
        path.write_text(content)
    print("Reproduced 15 positive pivots, 225 exact principal entries, constant full kernel")


if __name__ == "__main__":
    main()
