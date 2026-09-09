#!/usr/bin/env python3
"""Reproduce the dimension-independent 93-role K=3 catalogue.

The input is the literal four-pair representative scan and first-occurrence
canonicalization in P0174 FINITE_RECTANGLE_CERTIFICATES_K3.md. No numerical
solver, ambient-dimension cutoff, or stored discovery status is used.
"""
from pathlib import Path
from itertools import product
import argparse

MARKS = (((0,0),(0,0)), ((0,0),(0,1)), ((0,0),(1,0)), ((0,0),(1,1)))
PATTERNS = tuple(p for p in product(range(4), repeat=4)
                 if all(p[i] <= i and p[p[i]] == p[i] for i in range(4)))

def canonical(cells):
    rows, cols, packed = {}, {}, 0
    for i,j in cells:
        rows.setdefault(i,len(rows)); cols.setdefault(j,len(cols))
        packed = 16*packed + 4*rows[i] + cols[j]
    return packed

def key(e,f,a,b):
    return min(canonical(t) for t in ((e,f,a,b),(f,e,a,b),(e,f,b,a),(f,e,b,a)))

def vector(values):
    return '#v[' + ','.join(str(x) for x in values) + ']'

def render():
    cells = tuple(product(range(4),repeat=2))
    catalog = {}
    for e,f in MARKS:
        for a in cells:
            for b in cells:
                catalog.setdefault(key(e,f,a,b),len(catalog))
    if len(catalog)!=93 or len(PATTERNS)!=15:
        raise ArithmeticError('Incorrect role or equality-pattern coverage')
    table = [[catalog[key(*zip(r,c))] for c in PATTERNS] for r in PATTERNS]
    if set(x for row in table for x in row)!=set(range(93)):
        raise ArithmeticError('The 225 pattern pairs do not cover exactly all roles')
    return '''import DR.Certificates.FiniteTuplePattern
import Mathlib.Data.Vector.Basic

/-! Generated literal catalogue; reproduce with scripts/generate_finite_k3_orbits.py --check.
The table has all 15-by-15 row/column equality patterns and exactly 93 pair roles. -/

namespace DittertRybin.Certificates

def finiteK3RoleKeys : Vector Nat 93 :=
  '''+vector(catalog)+'''

def finiteK3RoleTable : Vector (Vector (Fin 93) 15) 15 :=
  #v['''+',\n    '.join(vector(row) for row in table)+''']

end DittertRybin.Certificates
'''

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    dest=Path(__file__).resolve().parent.parent/'DR/Certificates/FiniteK3OrbitData.lean'
    content=render()
    if args.check:
        if not dest.exists() or dest.read_text()!=content:
            raise ArithmeticError(f'Generated catalogue changed: {dest}')
    elif not dest.exists() or dest.read_text()!=content:
        dest.write_text(content)
    print('Exactly 93 roles and 225 pattern-pair entries reproduce')

if __name__=='__main__':main()
