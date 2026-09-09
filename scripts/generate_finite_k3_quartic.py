#!/usr/bin/env python3
"""Exact 33-equation quartic template and complete equality-pattern mapping.

The enumeration is the literal inclusive-OR coefficient expansion in
P0174 FINITE_RECTANGLE_CERTIFICATES_K3.md. The Lean semantic bridge checks
the six-position-pair symmetrization against these integer equations.
"""
from pathlib import Path
from itertools import combinations, combinations_with_replacement, product
from collections import Counter
from math import factorial
import argparse
from generate_finite_k3_orbits import MARKS, PATTERNS, key, vector

def render():
    cells=tuple(product(range(4),repeat=2))
    catalog={}
    for e,f in MARKS:
        for a in cells:
            for b in cells:catalog.setdefault(key(e,f,a,b),len(catalog))
    equations={}
    quartet_ids={}
    for quartet in combinations_with_replacement(range(16),4):
        row=[0]*93
        for pair in set(combinations(quartet,2)):
            rest=list(quartet)
            for cell in pair:rest.remove(cell)
            row[catalog[key(*(cells[cell] for cell in pair+tuple(rest)))]] += 1 if rest[0]==rest[1] else 2
        mult=factorial(4)
        for count in Counter(quartet).values():mult//=factorial(count)
        successes=0
        for removed in set(quartet):
            triple=list(quartet);triple.remove(removed)
            if len({cells[e][0] for e in triple})==3 or len({cells[e][1] for e in triple})==3:
                successes+=6
        row=tuple(row)
        if row in equations and equations[row][1:]!=(mult,successes):
            raise ArithmeticError('Inconsistent literal quartic coefficients')
        equations.setdefault(row,(len(equations),mult,successes))
        quartet_ids[quartet]=equations[row][0]
    if len(catalog)!=93 or len(equations)!=33:
        raise ArithmeticError('Incomplete universal quartic template')
    pair_orders=[(i,j,*(p for p in range(4) if p not in (i,j))) for i,j in combinations(range(4),2)]
    pattern_orders=[]
    for r in PATTERNS:
        ordered=[]
        for order in pair_orders:
            vals=[r[i] for i in order]
            normalized=tuple(vals.index(x) for x in vals)
            ordered.append(PATTERNS.index(normalized))
        pattern_orders.append(ordered)
    table=[]
    pair_roles=[]
    pair_weights=[]
    for r in PATTERNS:
        out=[]
        for c in PATTERNS:
            q=tuple(4*r[i]+c[i] for i in range(4))
            index=quartet_ids[tuple(sorted(q))]
            row,(_,mult,successes)=list(equations.items())[index]
            local=[0]*93
            roles=[]
            weights=[]
            for i,j in combinations(range(4),2):
                a,b=(p for p in range(4) if p not in (i,j))
                role=catalog[key(cells[q[i]],cells[q[j]],cells[q[a]],cells[q[b]])]
                weight=2 if q[i]==q[j] else 1
                local[role]+=weight
                roles.append(role)
                weights.append(weight)
            good=0
            for removed in range(4):
                rest=[i for i in range(4) if i!=removed]
                good+=int(len({r[i] for i in rest})==3 or len({c[i] for i in rest})==3)
            if any(mult*x!=12*y for x,y in zip(local,row)) or mult*3*good!=12*successes:
                raise ArithmeticError('Six-pair symmetrization differs from literal cubic event')
            out.append(index)
            pair_roles.append(roles)
            pair_weights.append(weights)
        table.append(out)
    return '''import DR.Certificates.FiniteK3Orbits

/-! Generated exact quartic coefficient equations; reproduce with
scripts/generate_finite_k3_quartic.py --check. No numerical certificate status is an input. -/
namespace DittertRybin.Certificates

def finiteK3QuarticPairPatterns : Vector (Vector (Fin 15) 6) 15 :=
  #v['''+',\n    '.join(vector(row) for row in pattern_orders)+''']

def finiteK3QuarticRows : Vector (Vector Nat 93) 33 :=
  #v['''+',\n    '.join(vector(row) for row in equations)+''']

def finiteK3QuarticMultiplicity : Vector Nat 33 :=
  '''+vector(item[1] for item in equations.values())+'''

def finiteK3QuarticSuccesses : Vector Nat 33 :=
  '''+vector(item[2] for item in equations.values())+'''

def finiteK3QuarticPatternEquation : Vector (Vector (Fin 33) 15) 15 :=
  #v['''+',\n    '.join(vector(row) for row in table)+''']

def finiteK3QuarticPairRoles : Vector (Vector (Fin 93) 6) 225 :=
  #v['''+',\n    '.join(vector(row) for row in pair_roles)+''']

def finiteK3QuarticPairWeights : Vector (Vector Nat 6) 225 :=
  #v['''+',\n    '.join(vector(row) for row in pair_weights)+''']

end DittertRybin.Certificates
'''

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--check',action='store_true');args=parser.parse_args()
    p=Path(__file__).resolve().parent.parent/'DR/Certificates/FiniteK3QuarticData.lean'
    text=render()
    if args.check:
        if not p.exists() or p.read_text()!=text:raise ArithmeticError(f'Changed generated template: {p}')
    elif not p.exists() or p.read_text()!=text:p.write_text(text)
    print('33 literal quartic equations and all225 six-pair pattern relations reproduce')

if __name__=='__main__':main()
