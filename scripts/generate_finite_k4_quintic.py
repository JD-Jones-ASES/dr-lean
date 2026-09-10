#!/usr/bin/env python3
"""Exact finite K4 quintic template, independently reconstructed by counting.

The generator counts every equality pattern and coefficient role using exact
integer arithmetic. The optional source audit reads pinned rational data.
The coefficient equations and their Lean interpretation are described in
data/FINITE_K4_QUINTIC_SOURCE.md.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from hashlib import sha256
from itertools import combinations, permutations, product
import json
from math import factorial, prod
from pathlib import Path
from time import perf_counter

from generate_finite_k4_orbits import PATTERNS, normalized, role_key

ROOT = Path(__file__).resolve().parent.parent
JSON_PATH = ROOT / 'data/finite_k4_quintic_template.json'
LEAN_PATH = ROOT / 'DR/Certificates/FiniteK4QuinticData.lean'
SCOPE = 'finite coefficient identities only; no PSD or endpoint claim'
SOURCE_HASHES = {
    'quintic_certificate.py': '00a675fdbf9ca8de469d1628484a3331eaed1abcd82cfaffcb22bab8ea033a56',
    'QUINTIC_CERTIFICATES_K4.md': '2aef864ddac9f491167344e4e619da48042f39e0cb01bbc91ee2d6b50d5a9a94',
    'quintic_k4_coefficients.json': '206e590b543473de13b2a6b969cdcbe6fae2526d3f12a1408083b6713c0f9c40',
}
TRIPLE_ORDERS = tuple(t + tuple(i for i in range(5) if i not in t)
                      for t in combinations(range(5), 3))
NATURAL_FIELDS = ['patterns', 'triple_orders', 'role_keys', 'triple_patterns', 'monomial_keys',
                  'rows', 'multiplicity', 'successes', 'pattern_equation', 'triple_roles',
                  'triple_weights', 'deleted_successes', 'four_row_equations',
                  'four_square_equations', 'four_row_roles', 'role_equation', 'role_coefficient',
                  'row_terms', 'triple_slots']


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def decode(key):
    cells = []
    for _ in range(5):
        key, digit = divmod(key, 25)
        cells.append(divmod(digit, 5))
    require(key == 0, 'five-cell key exceeds its fixed width')
    return tuple(reversed(cells))


@lru_cache(maxsize=None)
def monomial_key(cells):
    return min(normalized(p) for p in permutations(cells))


def weight6(cells):
    """Six times reciprocal number of distinct orders of the first triple."""
    multiplicities = sorted(Counter(cells[:3]).values())
    return { (3,): 6, (1, 2): 2, (1, 1, 1): 1 }[tuple(multiplicities)]


def success(cells):
    require(len(cells) == 4, 'success predicate requires four positions')
    return int(len({x[0] for x in cells}) == 4 or len({x[1] for x in cells}) == 4)


def first_position_pattern(values):
    return tuple(values.index(x) for x in values)


def unordered_row(cells, role_index):
    """Primary expansion: one term per multiplier multiset, ordered pair."""
    weights = Counter()
    triples = {tuple(sorted(cells[i] for i in t)) for t in combinations(range(5), 3)}
    for triple in triples:
        pair = list(cells)
        for cell in triple:
            pair.remove(cell)
        weights[role_index[role_key(triple + tuple(pair))]] += 1 if pair[0] == pair[1] else 2
    multiplicity = factorial(5) // prod(factorial(v) for v in Counter(cells).values())
    successes = 0
    for removed in set(cells):
        four = list(cells)
        four.remove(removed)
        # Success forces all four cells to be distinct, giving 24 literal orders.
        successes += 24 * success(four)
    return sorted(weights.items()), multiplicity, successes


def literal_row(cells, role_index):
    """Independent audit of the source's distinct-five-order formula."""
    orders = set(permutations(cells))
    scaled = Counter()
    successes = 0
    for order in orders:
        correction = prod(factorial(v) for v in Counter(order[:3]).values())
        require(correction == weight6(order), 'multiplier correction mismatch')
        scaled[role_index[role_key(order)]] += correction
        successes += success(order[:4])
    require(all(v % 6 == 0 for v in scaled.values()), 'literal coefficient is not integral')
    return sorted((i, v // 6) for i, v in scaled.items()), len(orders), successes


def build_data():
    require(len(PATTERNS) == 52 and PATTERNS[-1] == tuple(range(5)), 'Bell-five coverage mismatch')
    require(len(TRIPLE_ORDERS) == 10 and len(set(TRIPLE_ORDERS)) == 10,
            'missing or duplicated triple choices')
    require(all(sorted(o) == list(range(5)) for o in TRIPLE_ORDERS), 'choice is not a permutation')
    samples = [tuple(zip(r, c)) for r, c in product(PATTERNS, repeat=2)]
    keys = sorted({role_key(s) for s in samples})
    key_index = {k: i for i, k in enumerate(keys)}
    monomials = sorted({monomial_key(s) for s in samples})
    require((len(keys), len(monomials)) == (407, 91), 'universal quintic coverage mismatch')
    monomial_index = {key: i for i, key in enumerate(monomials)}
    rows, multiplicities, successes = [], [], []
    for key in monomials:
        cells = decode(key)
        row, mult, good = unordered_row(cells, key_index)
        require((row, mult, good) == literal_row(cells, key_index),
                'unordered multiplier expansion differs from literal source formula')
        rows.append([list(term) for term in row])
        multiplicities.append(mult)
        successes.append(good)
    pattern_index = {p: i for i, p in enumerate(PATTERNS)}
    axis = [[pattern_index[first_position_pattern(tuple(p[i] for i in o))]
             for o in TRIPLE_ORDERS] for p in PATTERNS]
    role_table = [key_index[role_key(tuple(zip(r, c)))] for r, c in product(PATTERNS, repeat=2)]
    equations, roles, weights, deleted = [], [], [], []
    for ri, r in enumerate(PATTERNS):
        equation_row = []
        for ci, c in enumerate(PATTERNS):
            cells = tuple(zip(r, c))
            equation_row.append(monomial_index[monomial_key(cells)])
            local_roles, local_weights = [], []
            for choice, order in enumerate(TRIPLE_ORDERS):
                ordered = tuple(cells[i] for i in order)
                role = role_table[52 * axis[ri][choice] + axis[ci][choice]]
                require(role == key_index[role_key(ordered)], 'axis cache changes a physical role')
                local_roles.append(role)
                local_weights.append(weight6(ordered))
            roles.append(local_roles)
            weights.append(local_weights)
            deleted.append(sum(success([cells[i] for i in range(5) if i != a]) for a in range(5)))
        equations.append(equation_row)
    four_rows = sorted({q for row in equations[:51] for q in row})
    four_square = sorted({q for row in equations[:51] for q in row[:51]})
    four_roles = sorted({role_table[52*r+c] for r in range(51) for c in range(52)})
    require((len(four_rows), len(four_square), len(four_roles)) == (84, 78, 391),
            'restricted quintic coverage mismatch')
    occurrences = [(role, eq, coefficient) for eq, row in enumerate(rows)
                   for role, coefficient in row]
    require(sorted(role for role, _, _ in occurrences) == list(range(407)),
            'each role must occur in exactly one sparse coefficient row')
    role_equation = [0]*407
    role_coefficient = [0]*407
    for role, eq, coefficient in occurrences:
        role_equation[role] = eq
        role_coefficient[role] = coefficient
    row_terms = [row + [[0,0] for _ in range(10-len(row))] for row in rows]
    triple_slots = []
    for flat, local_roles in enumerate(roles):
        eq = equations[flat//52][flat%52]
        slots = {role: slot for slot,(role,_) in enumerate(rows[eq])}
        triple_slots.append([slots[role] for role in local_roles])
    data = {
        'schema_version': 1,
        'source_sha256': SOURCE_HASHES,
        'scope': SCOPE,
        'patterns': [list(p) for p in PATTERNS],
        'triple_orders': [list(o) for o in TRIPLE_ORDERS],
        'role_keys': keys,
        'triple_patterns': axis,
        'monomial_keys': monomials,
        'rows': rows,
        'multiplicity': multiplicities,
        'successes': successes,
        'pattern_equation': equations,
        'triple_roles': roles,
        'triple_weights': weights,
        'deleted_successes': deleted,
        'four_row_equations': four_rows,
        'four_square_equations': four_square,
        'four_row_roles': four_roles,
        'role_equation': role_equation,
        'role_coefficient': role_coefficient,
        'row_terms': row_terms,
        'triple_slots': triple_slots,
    }
    validate_data(data)
    return data


def validate_data(data):
    """Recheck shape, literal coefficient meaning, and all 2704 local relations."""
    require(isinstance(data, dict) and set(data) ==
            set(NATURAL_FIELDS) | {'schema_version', 'source_sha256', 'scope'},
            'template fields missing or extra')
    require(data['schema_version'] == 1 and type(data['schema_version']) is int, 'invalid schema')
    require(data['source_sha256'] == SOURCE_HASHES, 'source attribution hash changed')
    require(data['scope'] == SCOPE, 'template proof scope changed')
    require(data['patterns'] == [list(p) for p in PATTERNS], 'pattern ordering changed')
    require(data['triple_orders'] == [list(o) for o in TRIPLE_ORDERS], 'triple choice ordering changed')
    def naturals(value):
        if isinstance(value, list):
            return all(naturals(v) for v in value)
        return type(value) is int and value >= 0
    require(all(naturals(data[k]) for k in NATURAL_FIELDS), 'finite data must contain exact natural integers')
    for field, outer, inner in [('triple_patterns',52,10), ('pattern_equation',52,52),
                                 ('triple_roles',2704,10), ('triple_weights',2704,10),
                                 ('row_terms',91,10), ('triple_slots',2704,10)]:
        require(len(data[field]) == outer and all(len(r) == inner for r in data[field]),
                f'{field} coverage mismatch')
    require(len(data['role_keys']) == 407 and len(data['rows']) == 91 and
            len(data['monomial_keys']) == 91 and len(data['multiplicity']) == 91 and
            len(data['successes']) == 91 and len(data['deleted_successes']) == 2704 and
            len(data['role_equation']) == 407 and len(data['role_coefficient']) == 407,
            'template vector coverage mismatch')
    samples = [tuple(zip(r, c)) for r, c in product(PATTERNS, repeat=2)]
    require(data['role_keys'] == sorted({role_key(s) for s in samples}), 'literal role keys changed')
    require(data['monomial_keys'] == sorted({monomial_key(s) for s in samples}),
            'literal monomial ordering changed')
    index = {k: i for i, k in enumerate(data['role_keys'])}
    eq_index = {k: i for i, k in enumerate(data['monomial_keys'])}
    for i, key in enumerate(data['monomial_keys']):
        row, mult, good = literal_row(decode(key), index)
        require(data['rows'][i] == [list(t) for t in row] and
                data['multiplicity'][i] == mult and data['successes'][i] == good,
                f'literal source equation changed at row {i}')
    require(sorted(role for row in data['rows'] for role, _ in row) == list(range(407)),
            'sparse rows do not partition all roles exactly once')
    for eq, row in enumerate(data['rows']):
        require(len(row) <= 10 and data['row_terms'][eq] ==
                row + [[0,0] for _ in range(10-len(row))], 'sparse row padding changed')
        for role, coefficient in row:
            require(data['role_equation'][role] == eq and data['role_coefficient'][role] == coefficient,
                    'sparse role lookup changed')
    for ri, r in enumerate(PATTERNS):
        for t, order in enumerate(TRIPLE_ORDERS):
            expected = PATTERNS.index(first_position_pattern(tuple(r[i] for i in order)))
            require(data['triple_patterns'][ri][t] == expected, 'axis compression cache changed')
        for ci, c in enumerate(PATTERNS):
            flat, cells = ri * 52 + ci, tuple(zip(r, c))
            eq = data['pattern_equation'][ri][ci]
            require(eq == eq_index[monomial_key(cells)], 'pattern-to-equation map changed')
            local = Counter()
            for t, order in enumerate(TRIPLE_ORDERS):
                ordered = tuple(cells[i] for i in order)
                role, weight = data['triple_roles'][flat][t], data['triple_weights'][flat][t]
                require(role == index[role_key(ordered)], 'literal triple role changed')
                require(weight == weight6(ordered), 'literal multiplier weight changed')
                slot = data['triple_slots'][flat][t]
                require(slot < len(data['rows'][eq]) and data['row_terms'][eq][slot][0] == role,
                        'triple slot does not select its actual nonpadding role')
                local[role] += weight
            mult = data['multiplicity'][eq]
            row = dict(data['rows'][eq])
            require(all(mult*local[k] == 60*row.get(k, 0) for k in set(local) | set(row)),
                    'ten-choice coefficient relation fails')
            for slot, (_, coefficient) in enumerate(data['row_terms'][eq]):
                fiber = sum(data['triple_weights'][flat][q] for q in range(10)
                            if data['triple_slots'][flat][q] == slot)
                require(mult*fiber == 60*coefficient, 'sparse selector fiber equation fails')
            good = sum(success([cells[i] for i in range(5) if i != a]) for a in range(5))
            require(data['deleted_successes'][flat] == good, 'deleted-event count changed')
            require(mult * 12 * good == 60 * data['successes'][eq], 'deleted-event relation fails')
    restricted = sorted({i for row in data['pattern_equation'][:51] for i in row})
    square = sorted({i for row in data['pattern_equation'][:51] for i in row[:51]})
    require(len(restricted) == 84 and data['four_row_equations'] == restricted,
            'four-row equation subset missing, duplicated or reordered')
    require(len(square) == 78 and data['four_square_equations'] == square,
            'four-square equation subset changed')
    four_roles = sorted({index[role_key(s)] for s in samples[:51*52]})
    require(len(four_roles) == 391 and data['four_row_roles'] == four_roles,
            'four-row role subset changed')


def check_four_row_catalogue(data, path=None):
    path = path or ROOT / 'scripts/data/four_row_finite/catalogue.json'
    catalogue = json.loads(path.read_text())
    role_map = data['four_row_roles']
    require(catalogue['role_keys'] == [data['role_keys'][i] for i in role_map],
            'independent four-row role catalogue differs')
    expected = []
    for eq in data['four_row_equations']:
        row = [[role_map.index(i), coefficient] for i, coefficient in data['rows'][eq]]
        expected.append([row, data['multiplicity'][eq], data['successes'][eq]])
    require(catalogue['coefficient_equations'] == expected,
            'independently generated 84 literal source equations differ')


def audit_source(data, directory):
    for name, expected in SOURCE_HASHES.items():
        require(sha256((directory / name).read_bytes()).hexdigest() == expected,
                f'pinned source hash changed: {name}')
    source = json.loads((directory / 'quintic_k4_coefficients.json').read_text())
    require(source['schema_version'] == 1 and len(source['cases']) == 4, 'source case coverage changed')
    seen = set()
    for case in source['cases']:
        m, n = case['m'], case['n']
        require(type(m) is int and type(n) is int and min(m,n) >= 4 and (m,n) not in seen,
                'source dimensions invalid or repeated')
        seen.add((m,n))
        role_subset = [i for i, key in enumerate(data['role_keys'])
                       if len({r for r,_ in decode(key)}) <= m and len({c for _,c in decode(key)}) <= n]
        require(len(case['seed']) == len(role_subset), 'source seed length differs from literal roles')
        values = dict(zip(role_subset, map(Fraction, case['seed'])))
        a = Fraction(prod(range(m-3,m+1)), m**4)
        b = Fraction(prod(range(n-3,n+1)), n**4)
        alpha = a+b-a*b
        for eq, key in enumerate(data['monomial_keys']):
            if len({r for r,_ in decode(key)}) > m or len({c for _,c in decode(key)}) > n:
                continue
            lhs = sum(Fraction(weight)*values[role] for role,weight in data['rows'][eq])
            require(lhs == data['multiplicity'][eq]*alpha-data['successes'][eq],
                    f'literal source coefficient equation failed: {(m,n,eq)}')
    require(seen == {(4,5),(4,50),(4,1000),(20,20)}, 'literal source case set changed')


def output(path, content, check):
    if check:
        require(path.exists() and path.read_text() == content, f'generated output differs: {path}')
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        if not path.exists() or path.read_text() != content:
            path.write_text(content)


def render_lean(data):
    def vector(values):
        return '#v[' + ','.join(map(str, values)) + ']'
    def block(name, type_name, values):
        return f'def {name} : {type_name} :=\n  ' + vector(values) + '\n\n'
    def large_block(name, element_type, values):
        # A literal #v with 2704 entries makes elaboration prove its length by
        # costly definitional reduction. Keep the exact Vector ABI, but expose
        # the array's ground size equality to the kernel explicitly.
        return (f'private def {name}Array : Array ({element_type}) :=\n  #[' +
                ','.join(map(str,values)) + ']\n\n' +
                f'def {name} : Vector ({element_type}) 2704 :=\n' +
                f'  ⟨{name}Array, by decide +kernel⟩\n\n')
    out = '''import DR.Certificates.FiniteK4QuinticChoice

/-! Generated by scripts/generate_finite_k4_quintic.py --check.
Exact sparse quintic coefficient data. Monomials use lexicographic canonical
five-cell keys. Physical pattern pairs are flattened as r*52+c. Ten choices
are exactly finiteK4TripleOrder; the two success arrays count different things:
Successes counts distinct ordered monomials, DeletedSuccesses sums five bits.
These definitions alone assert no identity, PSD property or endpoint theorem. -/

namespace DittertRybin.Certificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

'''
    out += block('finiteK4QuinticTriplePatterns', 'Vector (Vector (Fin 52) 10) 52',
                 (vector(row) for row in data['triple_patterns']))
    out += block('finiteK4QuinticMonomialKeys', 'Vector Nat 91', data['monomial_keys'])
    out += block('finiteK4QuinticRows', 'Vector (List (Fin 407 × Nat)) 91',
                 ('['+','.join(f'({i},{w})' for i,w in row)+']' for row in data['rows']))
    out += block('finiteK4QuinticRowTerms', 'Vector (Vector (Fin 407 × Nat) 10) 91',
                 (vector(f'({i},{w})' for i,w in row) for row in data['row_terms']))
    out += block('finiteK4QuinticMultiplicity', 'Vector Nat 91', data['multiplicity'])
    out += block('finiteK4QuinticSuccesses', 'Vector Nat 91', data['successes'])
    out += block('finiteK4QuinticPatternEquation', 'Vector (Vector (Fin 91) 52) 52',
                 (vector(row) for row in data['pattern_equation']))
    out += large_block('finiteK4QuinticTripleRoles', 'Vector (Fin 407) 10',
                 (vector(row) for row in data['triple_roles']))
    out += large_block('finiteK4QuinticTripleWeights', 'Vector Nat 10',
                 (vector(row) for row in data['triple_weights']))
    out += large_block('finiteK4QuinticTripleSlots', 'Vector (Fin 10) 10',
                 (vector(row) for row in data['triple_slots']))
    out += block('finiteK4QuinticDeletedSuccesses', 'Vector Nat 2704', data['deleted_successes'])
    out += block('finiteK4QuinticFourRowEquations', 'Vector (Fin 91) 84', data['four_row_equations'])
    out += block('finiteK4QuinticFourSquareEquations', 'Vector (Fin 91) 78', data['four_square_equations'])
    out += block('finiteK4QuinticRoleEquation', 'Vector (Fin 91) 407', data['role_equation'])
    out += block('finiteK4QuinticRoleCoefficient', 'Vector Nat 407', data['role_coefficient'])
    return out + 'end DittertRybin.Certificates\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--audit-source', type=Path, help='read-only pinned source directory')
    args = parser.parse_args()
    started = perf_counter()
    data = build_data()
    check_four_row_catalogue(data)
    if args.audit_source:
        audit_source(data, args.audit_source)
    output(JSON_PATH, json.dumps(data, separators=(',', ':'))+'\n', args.check)
    output(LEAN_PATH, render_lean(data), args.check)
    print(json.dumps({'status':'passed', 'patterns':52, 'roles':407, 'equations':91,
                      'pattern_pairs':2704, 'four_row_equations':84,
                      'four_square_equations':78,
                      'sparse_terms':sum(map(len,data['rows'])),
                      'max_sparse_terms':max(map(len,data['rows'])),
                      'source_audited':bool(args.audit_source),
                      'weight_sums':sorted(set(map(sum,data['triple_weights']))),
                      'seconds':round(perf_counter()-started,3),
                      'scope':data['scope']}))


if __name__ == '__main__':
    main()
