#!/usr/bin/env python3
"""Exact shifted Gram witnesses for the four K=3 4x5 seeds in FOUR_BY_FIVE.md.

The 93 numerators are mathematical source data. Role canonicalization reuses
the project's checked source convention. Fractions, not numerical spectral
tests, construct and replay the four principal LDL identities; Lean checks
the witnesses against the actual formula-defined physical matrices.
"""
import argparse
from fractions import Fraction as F
from pathlib import Path
from generate_finite_k3_orbits import key, MARKS, PATTERNS

NUMERATORS = (
    135, 30, -1, -21, 411, -72, -19, 106, -54, 411, 102, -131,
    -60, 447, -28, -29, -35, 480, -6, 14, 202, 76, -150, 508,
    -130, 14, 108, -114, 840, 46, 74, 230, -320, -208, 620, 170,
    36, 18, 542, 60, -6, 44, 32, -127, 860, 276, -128, -424,
    4, 172, -124, 554, 34, -130, -164, 638, 0, 254, -36, 582,
    198, -48, 244, -42, -36, -22, -40, -101, 1134, 4, 892, 40,
    -12, 74, -454, 924, -146, 616, -280, -28, -204, 408, -250, 838,
    420, 226, -96, -322, -274, 894, 202, 352, -130,
)


def rational(q):
    return str(q.numerator) if q.denominator == 1 else f"({q.numerator}/{q.denominator})"


def vector(values):
    return "#v[" + ",".join(values) + "]"


def render():
    catalog = {}
    cells4 = [(i, j) for i in range(4) for j in range(4)]
    for e, f in MARKS:
        for a in cells4:
            for b in cells4:
                catalog.setdefault(key(e, f, a, b), len(catalog))
    if not len(catalog) == len(NUMERATORS) == 93:
        raise ArithmeticError("The 4x5 data require exactly 93 aligned coefficients")
    cells = [(i, j) for i in range(4) for j in range(5)]
    all_weights, all_factors = [], []
    for e, f in MARKS:
        q = [[F(NUMERATORS[catalog[key(e, f, a, b)]], 200) for b in cells] for a in cells]
        if not all(q[i][j] == q[j][i] for i in range(20) for j in range(20)):
            raise ArithmeticError(f"The 4x5 seed {(e, f)} is not symmetric")
        if not all(sum(row) == 0 for row in q):
            raise ArithmeticError(f"The 4x5 seed {(e, f)} does not have the constant kernel")
        shift = [[q[i][j] - F(2, 5) * (F(i == j) - F(1, 20))
                  for j in range(20)] for i in range(20)]
        if not all(sum(row) == 0 for row in shift):
            raise ArithmeticError(f"The shifted 4x5 seed {(e, f)} does not have the constant kernel")
        lower = [[F(0) for _ in range(19)] for _ in range(19)]
        weights = []
        for j in range(19):
            pivot = shift[j][j] - sum(lower[j][k] ** 2 * weights[k] for k in range(j))
            if pivot <= 0:
                raise ArithmeticError(f"Nonpositive 4x5 shifted LDL pivot {(e, f, j)}: {pivot}")
            weights.append(pivot)
            lower[j][j] = F(1)
            for i in range(j + 1, 19):
                lower[i][j] = (shift[i][j] - sum(lower[i][k] * weights[k] * lower[j][k]
                                              for k in range(j))) / pivot
        factors = list(zip(*lower))
        if not all(shift[i][j] == sum(weights[k] * factors[k][i] * factors[k][j]
                                    for k in range(19))
                   for i in range(19) for j in range(19)):
            raise ArithmeticError(f"The exact 4x5 principal Gram reconstruction failed for {(e, f)}")
        all_weights.append(vector(map(rational, weights)))
        all_factors.append("#v[" + ",\n    ".join(vector(map(rational, row)) for row in factors) + "]")
    return "\n".join([
        "import DR.Certificates.Gram", "import Mathlib.Data.Vector.Basic", "",
        "/-! Exact rational coefficient and Gram data for the 4×5, K=3 inequality. Regenerate with",
        "scripts/generate_four_by_five_three.py --check. Lean checks validity separately. -/",
        "namespace DittertRybin.Certificates", "",
        "def fourByFiveThreeNumerators : Vector ℤ 93 :=", "  " + vector(map(str, NUMERATORS)), "",
        "def fourByFiveThreeWeights : Vector (Vector ℚ 19) 4 :=",
        "  #v[" + ",\n    ".join(all_weights) + "]", "",
        "def fourByFiveThreeFactors : Vector (Vector (Vector ℚ 19) 19) 4 :=",
        "  #v[" + ",\n    ".join(all_factors) + "]", "",
        "end DittertRybin.Certificates", "",
    ])


def render_patterns():
    def pattern(a, b, c, d):
        values = (a, b, c, d)
        return PATTERNS.index(tuple(values.index(v) for v in values))
    def table(n):
        return vector(vector(vector(str(pattern(0, t, a, b)) for b in range(n))
                             for a in range(n)) for t in range(2))
    return "\n".join([
        "import DR.Certificates.FiniteK3OrbitData", "",
        "/-! Exact compressed lookups; all 82 values are independently checked in Lean. -/",
        "namespace DittertRybin.Certificates", "",
        "def fourByFiveThreeRowPatterns : Vector (Vector (Vector (Fin 15) 4) 4) 2 :=",
        "  " + table(4), "",
        "def fourByFiveThreeColPatterns : Vector (Vector (Vector (Fin 15) 5) 5) 2 :=",
        "  " + table(5), "", "end DittertRybin.Certificates", "",
    ])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    base = Path(__file__).resolve().parents[1] / "DR/Certificates"
    outputs = {base / "FourByFiveThreeData.lean": render(),
               base / "FourByFiveThreePatternData.lean": render_patterns()}
    for path, content in outputs.items():
        if args.check:
            if not path.exists() or path.read_text() != content:
                raise ArithmeticError(f"Generated data changed: {path}")
        elif not path.exists() or path.read_text() != content:
            path.write_text(content)
    print("Reproduced 93 numerators, four constant kernels, 76 positive pivots, 1444 exact principal entries and 82 compression lookups")


if __name__ == "__main__":
    main()
