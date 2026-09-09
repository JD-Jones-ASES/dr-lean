#!/usr/bin/env python3
"""Literal fixed K4 seeds and exact coefficient equations; no PSD claims.

Reads only pinned mathematical data. The Markdown seed is extracted with
ast.literal_eval; no source code is imported, evaluated, or executed.
"""
from __future__ import annotations

import argparse
import ast
from fractions import Fraction
from hashlib import sha256
from itertools import permutations, product
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent
DATA = ROOT / 'data/finite_k4_fixed_seeds.json'
TEMPLATE = ROOT / 'data/finite_k4_quintic_template.json'
TEMPLATE_HASH = '170599056c8468ec4318e988d4dd81246251379af0550c159ab5235b94fee690'
SOURCES = {
    'K4_FIVE_BY_FIVE.md': '2276d83d8dba5cfdcbd7f10e050fbbcd2cef3e03c6e6dd222e18970744713418',
    'quintic_k4_coefficients.json': '206e590b543473de13b2a6b969cdcbe6fae2526d3f12a1408083b6713c0f9c40',
    'quintic_certificate.py': '00a675fdbf9ca8de469d1628484a3331eaed1abcd82cfaffcb22bab8ea033a56',
}
SCOPE = 'two literal rational seeds and 91 coefficient equations each; no PSD or endpoint claim'
SHAPES = [(5, 5), (20, 20)]


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def rational(value):
    require(type(value) is str and re.fullmatch(r'-?(0|[1-9][0-9]*)(/[1-9][0-9]*)?', value),
            'coefficient is not an exact rational string')
    q = Fraction(value)
    require(str(q) == value, 'coefficient is not in canonical reduced form')
    return q


def template():
    raw = TEMPLATE.read_bytes()
    require(sha256(raw).hexdigest() == TEMPLATE_HASH, 'pinned template hash differs')
    return json.loads(raw)


def independent_role_catalogue():
    """Unencoded tuple order from equality partitions and the 6 x 2 role actions.

    Source documentation orders tuple keys lexicographically. Packing five
    base-25 cells preserves that order, as checked against every stored key.
    """
    partitions = [p for p in product(range(5), repeat=5)
                  if p[0] == 0 and all(p[i] <= 1 + max(p[:i]) for i in range(1, 5))]
    require(len(partitions) == 52, 'independent Bell-five coverage differs')
    def rename(cells):
        row_first = [next(k for k in range(5) if cells[k][0] == x[0]) for x in cells]
        col_first = [next(k for k in range(5) if cells[k][1] == x[1]) for x in cells]
        rs, cs = sorted(set(row_first)), sorted(set(col_first))
        return tuple((rs.index(i), cs.index(j)) for i, j in zip(row_first, col_first))
    catalogue = set()
    for r, c in product(partitions, repeat=2):
        cells = tuple(zip(r, c))
        catalogue.add(min(rename(a + b) for a in permutations(cells[:3])
                          for b in permutations(cells[3:])))
    keys = []
    for cells in sorted(catalogue):
        value = 0
        for i, j in cells:
            value = 25 * value + 5 * i + j
        keys.append(value)
    require(len(keys) == 407 and keys == sorted(set(keys)), 'independent role order differs')
    return keys


def extract_markdown_seed(text):
    pieces = text.split("<<'PY'\n", 1)
    require(len(pieces) == 2 and '\nPY' in pieces[1], 'missing bounded seed literal block')
    tree = ast.parse(pieces[1].split('\nPY', 1)[0])
    assignments = [node for node in tree.body if isinstance(node, ast.Assign)
                   and any(isinstance(t, ast.Name) and t.id == 'SEED' for t in node.targets)]
    require(len(assignments) == 1 and len(assignments[0].targets) == 1,
            'missing or duplicated seed assignment')
    try:
        seed = ast.literal_eval(assignments[0].value)
    except (ValueError, TypeError, SyntaxError) as error:
        raise ArithmeticError('seed is not a literal') from error
    require(type(seed) is tuple and len(seed) == 407, 'seed literal has wrong type or length')
    for q in seed:
        rational(q)
    return list(seed)


def extract_sources(directory):
    values = {}
    for name, expected in SOURCES.items():
        raw = (directory / name).read_bytes()
        require(sha256(raw).hexdigest() == expected, 'pinned source hash differs: ' + name)
        values[name] = raw.decode('utf-8')
    five = extract_markdown_seed(values['K4_FIVE_BY_FIVE.md'])
    source = json.loads(values['quintic_k4_coefficients.json'])
    require(set(source) == {'schema_version', 'cases'} and source['schema_version'] == 1,
            'source JSON schema differs')
    shapes = [(c['m'], c['n']) for c in source['cases']]
    require(shapes == [(4, 5), (4, 50), (4, 1000), (20, 20)], 'source case coverage differs')
    twenty = source['cases'][-1]['seed']
    require(type(twenty) is list and len(twenty) == 407, 'twenty seed length differs')
    return [five, twenty]


def alpha(n):
    distinct = Fraction(n * (n - 1) * (n - 2) * (n - 3), n**4)
    return 2 * distinct - distinct * distinct


def validate(data):
    require(type(data) is dict and set(data) == {'schema_version', 'scope', 'source_sha256',
            'template_sha256', 'role_keys', 'cases'}, 'fixed seed data schema differs')
    require(type(data['schema_version']) is int and data['schema_version'] == 1, 'schema differs')
    require(data['scope'] == SCOPE and data['source_sha256'] == SOURCES and
            data['template_sha256'] == TEMPLATE_HASH, 'scope or source provenance differs')
    t = template()
    require(data['role_keys'] == t['role_keys'] == independent_role_catalogue(),
            '407-key source order differs')
    require(type(data['cases']) is list and len(data['cases']) == 2, 'case coverage differs')
    for case, shape in zip(data['cases'], SHAPES):
        require(type(case) is dict and set(case) == {'m', 'n', 'alpha', 'seed'}, 'case schema differs')
        require(type(case['m']) is int and type(case['n']) is int and
                (case['m'], case['n']) == shape, 'missing, extra, reordered or duplicated case')
        require(type(case['seed']) is list and len(case['seed']) == 407, 'coefficient coverage differs')
        coefficients = [rational(v) for v in case['seed']]
        a = rational(case['alpha'])
        require(a == alpha(case['n']), 'target uniform value differs')
        for row, mult, successes in zip(t['rows'], t['multiplicity'], t['successes']):
            require(sum(weight * coefficients[role] for role, weight in row) == mult * a - successes,
                    'exact coefficient equation failed')


def build(directory):
    seeds = extract_sources(directory)
    t = template()
    result = {'schema_version': 1, 'scope': SCOPE, 'source_sha256': SOURCES,
              'template_sha256': TEMPLATE_HASH, 'role_keys': t['role_keys'],
              'cases': [{'m': m, 'n': n, 'alpha': str(alpha(n)), 'seed': seed}
                        for (m, n), seed in zip(SHAPES, seeds)]}
    validate(result)
    return result


def lean_rat(text):
    q = rational(text)
    return str(q.numerator) if q.denominator == 1 else f'({q.numerator}/{q.denominator})'


def render(data):
    header = '''import Mathlib.Data.Vector.Basic
import Mathlib.Data.Rat.Defs

/-! Generated by scripts/generate_finite_k4_fixed_seeds.py. Literal mathematical
inputs in the independently checked, sorted 407-role order. Coefficient equations
are proved separately; this data file makes no matrix-positivity claim. -/
namespace DittertRybin.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

'''
    for case in data['cases']:
        n = case['n']
        header += f'def finiteK4Fixed{n}Alpha : ℚ := {lean_rat(case["alpha"])}\n\n'
        header += f'private def finiteK4Fixed{n}SeedArray : Array ℚ :=\n  #['
        header += ',\n    '.join(lean_rat(q) for q in case['seed']) + ']\n\n'
        header += f'def finiteK4Fixed{n}Seed : Vector ℚ 407 :=\n  ⟨finiteK4Fixed{n}SeedArray, by decide +kernel⟩\n\n'
        header += f'def finiteK4Fixed{n}Coefficient : Fin 407 → ℚ := finiteK4Fixed{n}Seed.get\n\n'
    return header + 'end DittertRybin.Certificates\n'


def output(path, content, check):
    if check:
        require(path.exists() and path.read_text() == content, 'generated output differs: ' + str(path))
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-dir', type=Path)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    data = build(args.source_dir) if args.source_dir else json.loads(DATA.read_text())
    validate(data)
    output(DATA, json.dumps(data, indent=2) + '\n', args.check)
    output(ROOT / 'DR/Certificates/FiniteK4FixedSeedData.lean', render(data), args.check)
    print('PASS: 2 exact seeds, 407 independently ordered roles, 182 rational equations; no PSD claim')


if __name__ == '__main__':
    main()
