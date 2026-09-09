#!/usr/bin/env python3
"""Rebuild exact four-row quintic family data; no Lab dependency after import.

This generator is not a proof. Lean checks must connect the literal role
catalogue, polynomial identities and reduced blocks to the physical matrices.
Block polynomials are formed by exact multiplication and cancellation, never
interpolation. The two input files are the rational research certificates.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as Q
from functools import cache
import hashlib
from itertools import permutations, product
import json
from math import comb, gcd, lcm
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'scripts/data/four_row_finite'
SOURCES = (
    ('quintic_four_row_family_coefficients.json',
     '9c7b984cd70fef7b5a43dc075491c67c39ca53bb1c673a92428e8aad85873f78', 5),
    ('quintic_four_row_family_50_500_coefficients.json',
     'e2cb3178c1be8372acf7e7cfb2f0f90ad177860a6b4732e08ac343cb76e297fc', 50),
)


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def verify_source(raw, digest, name):
    require(hashlib.sha256(raw).hexdigest() == digest, f'source SHA256 mismatch: {name}')


def expect_rejection(action, label):
    try:
        action()
    except ArithmeticError:
        return
    raise ArithmeticError(f'negative control was accepted: {label}')


def trim(p):
    p = list(map(Q, p))
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return tuple(p) or (Q(0),)


def add(*ps):
    return trim(sum((p[k] for p in ps if k < len(p)), Q(0))
                for k in range(max(map(len, ps))))


def scale(p, x):
    return trim(x*a for a in p)


def mul(p, q):
    r = [Q(0)]*(len(p)+len(q)-1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i+j] += a*b
    return trim(r)


def evaluate(p, u):
    result = Q(0)
    for a in reversed(p):
        result = result*u+a
    return result


def normalized(cells):
    row, col = {}, {}
    return tuple((row.setdefault(i, len(row)), col.setdefault(j, len(col)))
                 for i, j in cells)


@cache
def role(cells):
    return min(normalized(a+b) for a in permutations(cells[:3])
               for b in permutations(cells[3:]))


def patterns(length, cap, prefix=()):
    if len(prefix) == length:
        yield prefix
    else:
        for x in range(min(cap, 1+max(prefix, default=-1)+1)):
            yield from patterns(length, cap, prefix+(x,))


@cache
def catalogue():
    cells = tuple(tuple(zip(r, c)) for r in patterns(5, 4) for c in patterns(5, 5))
    keys = sorted({role(s) for s in cells})
    marks = sorted({min(normalized(p) for p in permutations(s[:3])) for s in cells})
    monomials = sorted({min(normalized(p) for p in permutations(s)) for s in cells})
    require((len(cells), len(keys), len(marks), len(monomials)) == (2652, 391, 10, 84),
            'equality-pattern, role, seed or monomial coverage mismatch')
    return keys, {s: i for i, s in enumerate(keys)}, marks, monomials


def key_number(cells):
    z = 0
    for i, j in cells:
        z = 25*z+5*i+j
    return z


def coefficient_equations():
    _, index, _, monomials = catalogue()
    out = []
    for cells in monomials:
        ordered = set(permutations(cells))
        weights = Counter()
        successes = 0
        for s in ordered:
            distinct = len(set(permutations(s[:3])))
            weights[index[role(s)]] += Q(1, distinct)
            successes += int(len({i for i, _ in s[:4]}) == 4 or
                             len({j for _, j in s[:4]}) == 4)
        require(all(x.denominator == 1 for x in weights.values()),
                'corrected multiplier coefficients must be integral')
        out.append((sorted((i, int(x)) for i, x in weights.items()), len(ordered), successes))
    return out


def kernel_equations():
    _, index, marks, _ = catalogue()
    rows = set()
    for mark in marks:
        for cell in product(range(4), range(5)):
            used_r = sorted({i for i, _ in mark+(cell,)})
            used_c = sorted({j for _, j in mark+(cell,)})
            rs = [(i, 1) for i in used_r]
            if len(used_r) < 4:
                rs.append((next(i for i in range(5) if i not in used_r), 4-len(used_r)))
            cs = [(j, 0, 1) for j in used_c]
            cs.append((next(j for j in range(5) if j not in used_c), 1, -len(used_c)))
            counts = {}
            for (i, w), (j, slope, offset) in product(rs, cs):
                k = index[role(mark+(cell, (i, j)))]
                a, b = counts.get(k, (0, 0))
                counts[k] = a+w*slope, b+w*offset
            rows.add(tuple(sorted((k, a, b) for k, (a, b) in counts.items() if a or b)))
    require(len(rows) == 65, 'affine kernel row coverage mismatch')
    return sorted(rows)


def symbolic_blocks(h, a):
    """Exact H=D*B(a/u,h); D/(a/u-c) cancels one specified factor."""
    _, index, marks, _ = catalogue()
    factors = [(Q(1), -Q(c, a)) for c in (1, 2, 3)]
    denominator = mul(mul(factors[0], factors[1]), factors[2])
    result = []
    for seed, mark in enumerate(marks):
        nr, nc = len({i for i, _ in mark}), len({j for _, j in mark})
        ordinary_r = 4-nr
        dc = (Q(0), Q(1, a))
        for c, p in enumerate(factors, 1):
            if c != nc:
                dc = mul(dc, p)

        def entry(x, y):
            return h[index[role(mark+(x, y))]]

        def rows(i, k):
            if i == nr and k == nr:
                return [(i, k, Q(1, ordinary_r)),
                        (i, k+1, Q(ordinary_r-1, ordinary_r))]
            return [(i, k, Q(1))]

        def columns(j, l):
            if j == nc and l == nc:
                return [(j, l, dc), (j, l+1, add(denominator, scale(dc, -1)))]
            return [(j, l, denominator)]

        def averaged(x, y):
            return add(*(scale(mul(wc, entry((i, j), (k, l))), wr)
                         for i, k, wr in rows(x[0], y[0]) if wr
                         for j, l, wc in columns(x[1], y[1])))

        types = list(product(range(nr+1), range(nc+1)))[:-1]
        result.append((seed, 'trivial', [[averaged(x, y) for y in types] for x in types]))
        if ordinary_r > 1:
            matrix = [[add(*(mul(w, add(entry((nr, k), (nr, t)),
                                           scale(entry((nr, k), (nr+1, t)), -1)))
                                for k, t, w in columns(j, l)))
                       for l in range(nc+1)] for j in range(nc+1)]
            result.append((seed, 'row', matrix))
        matrix = [[add(*(scale(mul(denominator,
                         add(entry((j, nc), (l, nc)), scale(entry((j, nc), (l, nc+1)), -1))), w)
                         for j, l, w in rows(i, k) if w))
                   for k in range(nr+1)] for i in range(nr+1)]
        result.append((seed, 'column', matrix))
        if ordinary_r > 1:
            p = mul(denominator, add(entry((nr, nc), (nr, nc)),
                    scale(entry((nr, nc), (nr+1, nc)), -1),
                    scale(entry((nr, nc), (nr, nc+1)), -1),
                    entry((nr, nc), (nr+1, nc+1))))
            result.append((seed, 'interaction', [[p]]))
    require(len(result) == 34 and sum(len(q) for _, _, q in result) == 138,
            'reduced block coverage mismatch')
    require(all(len(p) <= 8 for _, _, matrix in result for row in matrix for p in row),
            'cleared polynomial degree exceeds seven')
    require(all(matrix[i][j] == matrix[j][i] for _, _, matrix in result
                for i in range(len(matrix)) for j in range(len(matrix))),
            'cleared polynomial block is asymmetric')
    return result


def bernstein(p):
    lo, width = Q(1, 10), Q(9, 10)
    shifted = [sum((p[i]*comb(i, j)*lo**(i-j)*width**j
                    for i in range(j, len(p))), Q(0)) for j in range(10)]
    return tuple(sum((shifted[j]*Q(comb(k, j), comb(9, j)) for j in range(k+1)), Q(0))
                 for k in range(10))


def lean_rat(x):
    return str(x.numerator) if x.denominator == 1 else f'({x.numerator}/{x.denominator})'


def integer_gram(matrix):
    """Exact LDL, then primitive integer Gram rows with positive weights."""
    n = len(matrix)
    require(n > 0 and all(len(row) == n for row in matrix), 'Gram matrix must be nonempty and square')
    require(all(matrix[i][j] == matrix[j][i] for i in range(n) for j in range(n)),
            'Gram matrix is asymmetric')
    lower = [[Q(i == j) for j in range(n)] for i in range(n)]
    pivots = []
    for k in range(n):
        pivot = matrix[k][k]-sum((lower[k][t]**2*pivots[t] for t in range(k)), Q(0))
        require(pivot > 0, f'Gram pivot {k} is not strictly positive')
        pivots.append(pivot)
        for i in range(k+1, n):
            lower[i][k] = (matrix[i][k]-sum(
                (lower[i][t]*lower[k][t]*pivots[t] for t in range(k)), Q(0)))/pivot
    factors, weights = [], []
    for k in range(n):
        row = [lower[i][k] for i in range(n)]
        denominator = lcm(*(x.denominator for x in row))
        integers = [int(x*denominator) for x in row]
        common = gcd(*integers)
        factors.append([x//common for x in integers])
        weights.append(pivots[k]*Q(common, denominator)**2)
    require(all(matrix[i][j] == sum((weights[k]*factors[k][i]*factors[k][j]
                                    for k in range(n)), Q(0))
                for i in range(n) for j in range(n)), 'exact Gram reconstruction failed')
    return factors, weights


def lean_array(name, kind, entries, default):
    """Chunk literals to bound elaboration depth and kernel lookup cost."""
    count = (len(entries)+31)//32
    out = ''
    for k in range(count):
        out += (f'private def {name}Chunk{k} : Array ({kind}) :=\n  #['+
                ',\n    '.join(entries[32*k:32*(k+1)])+']\n\n')
    out += (f'private def {name}Chunks : Array (Array ({kind})) :=\n  #['+
            ', '.join(f'{name}Chunk{k}' for k in range(count))+']\n\n')
    out += (f'def {name} (i : ℕ) : {kind} :=\n'
            f'  ({name}Chunks.getD (i / 32) #[]).getD (i % 32) ({default})\n\n')
    return out


def gram_block_files(a, b, block, check):
    seed, sector, p = block
    n = len(p)
    bs = [[bernstein(entry) for entry in row] for row in p]
    matrices = [[[bs[i][j][k] for j in range(n)] for i in range(n)] for k in range(10)]
    grams = [integer_gram(q) for q in matrices]
    prefix = f'fourRowFinite{a}Block{b}'
    name = f'FourRowFiniteData{a}Block{b}'
    data = ('import DR.Rectangular.FourRowFiniteBernstein\nimport DR.Certificates.StrictGram\n\n'
            '/-! Generated exact data, scripts/generate_four_row_finite.py.\n'
            f'Family a={a}, triple seed {seed}, {sector} sector.\n'
            'Gram and Bernstein gates are in the separate Checks module. -/\n\n'
            'set_option maxRecDepth 100000\n\nnamespace DittertRybin\n'
            'open Certificates\nnoncomputable section\n\n')
    data += lean_array(prefix+'PowerEntry', 'Fin 10 → ℚ',
                       ['!['+', '.join(lean_rat(x) for x in list(entry)+[Q(0)]*(10-len(entry)))+']'
                        for row in p for entry in row], 'fun _ => 0')
    data += (f'def {prefix}Power : Fin {n} → Fin {n} → Fin 10 → ℚ :=\n'
             f'  fun i j => {prefix}PowerEntry ({n}*i.val+j.val)\n\n')
    data += lean_array(prefix+'BernsteinEntry', 'ℚ',
                       [lean_rat(x) for q in matrices for row in q for x in row], '0')
    data += (f'def {prefix}Bernstein (k : Fin 10) : Matrix (Fin {n}) (Fin {n}) ℚ :=\n'
             f'  fun i j => {prefix}BernsteinEntry ({n*n}*k.val+{n}*i.val+j.val)\n\n')
    data += lean_array(prefix+'FactorEntry', 'ℚ',
                       [str(x) for factor, _ in grams for row in factor for x in row], '0')
    data += lean_array(prefix+'WeightEntry', 'ℚ',
                       [lean_rat(x) for _, weights in grams for x in weights], '0')
    data += (f'def {prefix}Gram (k : Fin 10) : GramCertificate {n} {n} where\n'
             f'  weights i := {prefix}WeightEntry ({n}*k.val+i.val)\n'
             f'  factor i j := {prefix}FactorEntry ({n*n}*k.val+{n}*i.val+j.val)\n\n'
             'end\nend DittertRybin\n')
    proof = (f'import DR.Rectangular.{name}\nimport Mathlib.Tactic.FinCases\n\n'
             'namespace DittertRybin\nopen Certificates\n\n')
    for k in range(10):
        proof += ('set_option maxRecDepth 100000 in\nset_option maxHeartbeats 32000000 in\n'
                  f'private theorem {prefix}Gram_valid_{k} :\n'
                  f'    ({prefix}Gram {k}).StrictValid ({prefix}Bernstein {k}) := by\n'
                  '  decide +kernel\n\n')
    proof += (f'theorem {prefix}Gram_valid (k : Fin 10) :\n'
              f'    ({prefix}Gram k).StrictValid ({prefix}Bernstein k) := by\n'
              '  fin_cases k\n'+''.join(f'  · exact {prefix}Gram_valid_{k}\n' for k in range(10))+'\n'
              f'theorem {prefix}Bernstein_posDef (k : Fin 10) :\n'
              f'    (({prefix}Bernstein k).map (fun q : ℚ => (q : ℝ))).PosDef :=\n'
              f'  ({prefix}Gram k).strictValid_posDef _ ({prefix}Gram_valid k)\n\n'
              'end DittertRybin\n')
    output(ROOT / f'DR/Rectangular/{name}.lean', data, check)
    output(ROOT / f'DR/Rectangular/{name}Checks.lean', proof, check)
    transform = (f'import DR.Rectangular.{name}Checks\n'
                 'import DR.Rectangular.FourRowFiniteDataBernstein\n\n'
                 '/-! Exact coefficient transformation, including both closed endpoints. -/\n\n'
                 'namespace DittertRybin\nopen Certificates\n\n')
    for k in range(10):
        transform += ('set_option maxRecDepth 100000 in\nset_option maxHeartbeats 32000000 in\n'
                      f'private theorem {prefix}Transform_{k} : ∀ i j : Fin {n},\n'
                      f'    {prefix}Bernstein {k} i j = fourRowFiniteMatrixBernstein (1/10) 1\n'
                      f'      (fun k i j => {prefix}Power i j k) {k} i j := by\n'
                      f'  dsimp only [{prefix}Bernstein, fourRowFiniteMatrixBernstein]\n'
                      '  simp_rw [fourRowFiniteBernsteinNine_apply]\n'
                      '  decide +kernel\n\n')
    transform += (f'theorem {prefix}Bernstein_eq (k : Fin 10) :\n'
                  f'    {prefix}Bernstein k = fourRowFiniteMatrixBernstein (1/10) 1\n'
                  f'      (fun k i j => {prefix}Power i j k) k := by\n'
                  '  ext i j\n  fin_cases k\n'+
                  ''.join(f'  · exact {prefix}Transform_{k} i j\n' for k in range(10))+'\n'
                  f'theorem {prefix}Polynomial_posDef (u : ℝ) (hu : 1/10 ≤ u ∧ u ≤ 1) :\n'
                  f'    (fourRowFiniteMatrixPolynomial (fun k i j => {prefix}Power i j k) u).PosDef := by\n'
                  '  apply fourRowFiniteMatrixPolynomial_posDef (1/10) 1 _ (by norm_num)\n'
                  f'  · intro k\n    rw [← {prefix}Bernstein_eq]\n'
                  f'    exact {prefix}Bernstein_posDef k\n'
                  '  · norm_num\n    exact hu\n\n'
                  'end DittertRybin\n')
    output(ROOT / f'DR/Rectangular/{name}Transform.lean', transform, check)
    return len(data), len(proof)+len(transform)


def output(path, content, check):
    if check:
        if not path.exists() or path.read_text() != content:
            raise SystemExit(f'generated content differs: {path.relative_to(ROOT)}')
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--import-source', type=Path,
                        help='explicit one-time directory containing the two audited JSON inputs')
    parser.add_argument('--gram-block', type=int, action='append', default=[],
                        help='emit this reduced block (0..33) for both families, including ten exact Gram gates')
    parser.add_argument('--gram-plan', action='store_true',
                        help='audit all 680 exact integer Gram factorizations and report size without emitting them')
    args = parser.parse_args()
    if args.check and args.import_source:
        parser.error('--check does not import or write inputs')
    if any(not 0 <= b < 34 for b in args.gram_block):
        parser.error('--gram-block must be between 0 and 33')
    expect_rejection(lambda: integer_gram([[Q(-1)]]), 'negative Gram pivot')
    expect_rejection(lambda: integer_gram([[Q(0)]]), 'zero Gram pivot')
    expect_rejection(lambda: integer_gram([[Q(1), Q(2)], [Q(0), Q(1)]]), 'asymmetric Gram matrix')
    report = {'scope': 'generated data, not a Lean endpoint proof', 'families': []}
    keys, _, marks, _ = catalogue()
    eqs, kernels = coefficient_equations(), kernel_equations()
    catalogue_data = {'role_keys': [key_number(k) for k in keys], 'triple_seeds': marks,
                      'coefficient_equations': eqs, 'kernel_equations': kernels}
    output(DATA / 'catalogue.json', json.dumps(catalogue_data, indent=2)+'\n', args.check)
    rows_lean = ('import DR.Rectangular.FourRowFiniteLinear\n\n'
                 '/-! Generated sparse exact equations; physical coverage is a separate theorem. -/\n\n'
                 'set_option maxRecDepth 100000\n\nnamespace DittertRybin\n\n')
    rows_lean += lean_array('fourRowFiniteCoefficientRowData', 'FourRowFiniteCoefficientRow',
        ['⟨['+', '.join(f'(⟨{i}, by decide⟩, {count})' for i, count in row)+f'], {mult}, {succ}⟩'
         for row, mult, succ in eqs], 'default')
    rows_lean += ('def fourRowFiniteCoefficientRows (e : Fin 84) : FourRowFiniteCoefficientRow :=\n'
                  '  fourRowFiniteCoefficientRowData e.val\n\n')
    rows_lean += lean_array('fourRowFiniteKernelRowData', 'List FourRowFiniteKernelTerm',
        ['['+', '.join(f'⟨⟨{i}, by decide⟩, {slope}, {offset}⟩' for i, slope, offset in row)+']'
         for row in kernels], '[]')
    rows_lean += ('def fourRowFiniteKernelRows (e : Fin 65) : List FourRowFiniteKernelTerm :=\n'
                  '  fourRowFiniteKernelRowData e.val\n\nend DittertRybin\n')
    output(ROOT / 'DR/Rectangular/FourRowFiniteDataRows.lean', rows_lean, args.check)
    transform_table = [bernstein(tuple(Q(j == d) for j in range(10))) for d in range(10)]
    transform_lean = ('import DR.Rectangular.FourRowFiniteBernsteinLinear\n\n'
                      '/-! Exact degree-nine transform for the interval [1/10,1], checked once. -/\n\n'
                      'set_option maxRecDepth 100000\n\nnamespace DittertRybin.Certificates\n'
                      'open scoped BigOperators\n\n')
    transform_lean += lean_array('fourRowFiniteBernsteinNineEntry', 'ℚ',
                                [lean_rat(transform_table[d][k]) for k in range(10) for d in range(10)], '0')
    transform_lean += ('def fourRowFiniteBernsteinNine (i j : Fin 10) : ℚ :=\n'
                       '  fourRowFiniteBernsteinNineEntry (10*i.val+j.val)\n\n'
                       'set_option maxHeartbeats 32000000 in\n'
                       'theorem fourRowFiniteBernsteinNine_exact : ∀ i j : Fin 10,\n'
                       '    fourRowFiniteBernsteinNine i j = fourRowFiniteBernsteinLinearMap (1/10) 1 i j := by\n'
                       '  decide +kernel\n\n'
                       'theorem fourRowFiniteBernsteinNine_apply (p : Fin 10 → ℚ) (i : Fin 10) :\n'
                       '    powerToBernstein (affinePowerCoefficients (1/10) 1 p) i =\n'
                       '      ∑ j, fourRowFiniteBernsteinNine i j*p j := by\n'
                       '  simpa only [fourRowFiniteBernsteinNine_exact] using\n'
                       '    fourRowFiniteBernsteinLinearMap_apply (1/10) 1 p i\n\n'
                       'end DittertRybin.Certificates\n')
    output(ROOT / 'DR/Rectangular/FourRowFiniteDataBernstein.lean', transform_lean, args.check)
    for name, digest, a in SOURCES:
        if args.import_source:
            raw = (args.import_source / name).read_bytes()
            verify_source(raw, digest, name)
            DATA.mkdir(parents=True, exist_ok=True)
            (DATA / name).write_bytes(raw)
        raw = (DATA / name).read_bytes()
        verify_source(raw, digest, name)
        expect_rejection(lambda: verify_source(raw+b'\n', digest, name), 'changed source SHA256')
        data = json.loads(raw)
        require(data['parameter_numerator'] == a and data['column_interval'] == [a, 10*a],
                'source parameter/interval mismatch')
        require((data['row_count'], data['order'], data['numerator_degree'], data['bernstein_degree']) == (4, 4, 4, 9),
                'source row/order/degree scope mismatch')
        values = tuple(map(Q, data['coefficients']))
        require(len(values) == 1955, 'source must contain exactly 1955 rational coefficients')
        h = tuple(values[5*i:5*i+5] for i in range(391))
        uniform = (Q(1), -Q(87, 16*a), Q(319, 32*a*a), -Q(87, 16*a**3))
        for row, multiplicity, successes in eqs:
            require(add(*(scale(h[i], weight) for i, weight in row)) ==
                    mul((Q(0), Q(1)), add(scale(uniform, multiplicity), (-Q(successes),))),
                    'exact coefficient identity failed')
        for row in kernels:
            require(add(*(mul(h[i], (Q(a*slope), Q(offset))) for i, slope, offset in row)) == (Q(0),),
                    'exact affine kernel identity failed')
        blocks = symbolic_blocks(h, a)
        if args.gram_plan:
            total = pivots = payload = factor_bits = weight_bits = 0
            for _, _, matrix in blocks:
                bs = [[bernstein(p) for p in row] for row in matrix]
                n = len(matrix)
                for k in range(10):
                    q = [[bs[i][j][k] for j in range(n)] for i in range(n)]
                    factor, weights = integer_gram(q)
                    total += 1
                    pivots += n
                    payload += len(json.dumps({'factor': factor, 'weights': list(map(str, weights))}))
                    factor_bits = max(factor_bits, *(abs(x).bit_length() for row in factor for x in row))
                    weight_bits = max(weight_bits, *(max(abs(x.numerator).bit_length(), x.denominator.bit_length())
                                                     for x in weights))
            print(json.dumps({'gram_plan_parameter': a, 'matrices': total, 'positive_pivots': pivots,
                              'integer_gram_payload_bytes': payload, 'max_factor_bits': factor_bits,
                              'max_weight_bits': weight_bits}))
        for b in sorted(set(args.gram_block)):
            sizes = gram_block_files(a, b, blocks[b], args.check)
            print(json.dumps({'emitted_gram_parameter': a, 'block': b, 'data_bytes': sizes[0],
                              'gate_bytes': sizes[1]}))
        encoded = [{'seed': seed, 'sector': sector, 'power_coefficients':
                    [[[str(c) for c in p] for p in row] for row in matrix]}
                   for seed, sector, matrix in blocks]
        block_text = json.dumps(encoded, separators=(',', ':'))+'\n'
        output(DATA / f'blocks_{a}.json', block_text, args.check)
        lean = ('import Mathlib.Data.Rat.Defs\nimport Mathlib.Data.Fin.VecNotation\n\n'
                '/-! Exact rational inputs only. Generated by scripts/generate_four_row_finite.py.\n'
                f'Source SHA256: {digest}. No matrix or identity gate is asserted here. -/\n\n'
                'set_option maxRecDepth 4096\n\nnamespace DittertRybin\n\n')
        for chunk in range(13):
            lean += (f'private def fourRowFiniteFamilyNumerator{a}Chunk{chunk} : Array (Fin 5 → ℚ) :=\n  #['+
                     ',\n    '.join('!['+', '.join(map(lean_rat, p))+']'
                                    for p in h[32*chunk:32*(chunk+1)])+']\n\n')
        lean += (f'private def fourRowFiniteFamilyNumerator{a}Chunks : Array (Array (Fin 5 → ℚ)) :=\n  #['+
                 ', '.join(f'fourRowFiniteFamilyNumerator{a}Chunk{chunk}' for chunk in range(13))+']\n\n'
                 f'def fourRowFiniteFamilyNumerator{a} (i : Fin 391) (d : Fin 5) : ℚ :=\n'
                 f'  ((fourRowFiniteFamilyNumerator{a}Chunks.getD (i.val / 32) #[]).getD\n'
                 '    (i.val % 32) (fun _ => 0)) d\n\nend DittertRybin\n')
        output(ROOT / f'DR/Rectangular/FourRowFiniteData{a}.lean', lean, args.check)
        identities = (f'import DR.Rectangular.FourRowFiniteData{a}\n'
                      'import DR.Rectangular.FourRowFiniteDataRows\n\n'
                      'namespace DittertRybin\n\n'
                      'set_option maxRecDepth 100000 in\nset_option maxHeartbeats 32000000 in\n'
                      f'theorem fourRowFinite{a}_coefficient_identities : ∀ e : Fin 84,\n'
                      f'    (fourRowFiniteCoefficientRows e).Valid {a} fourRowFiniteFamilyNumerator{a} := by\n'
                      '  decide +kernel\n\n'
                      'set_option maxRecDepth 100000 in\nset_option maxHeartbeats 32000000 in\n'
                      f'theorem fourRowFinite{a}_kernel_identities : ∀ e : Fin 65,\n'
                      f'    fourRowFiniteKernelValid (fourRowFiniteKernelRows e) {a} fourRowFiniteFamilyNumerator{a} := by\n'
                      '  decide +kernel\n\nend DittertRybin\n')
        output(ROOT / f'DR/Rectangular/FourRowFiniteData{a}Identities.lean', identities, args.check)
        report['families'].append({'parameter': a, 'source_sha256': digest,
            'source_bytes': len(raw), 'roles': len(h), 'scalar_identities': 84*5+65*6,
            'block_count': len(blocks), 'block_dimensions': [len(q) for _, _, q in blocks],
            'maximum_power_degree': max(len(p)-1 for _, _, q in blocks for row in q for p in row),
            'block_json_bytes': len(block_text), 'lean_numerator_bytes': len(lean),
            'bernstein_matrix_count': 340})
    output(DATA / 'manifest.json', json.dumps(report, indent=2)+'\n', args.check)
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
