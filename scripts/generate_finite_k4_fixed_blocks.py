#!/usr/bin/env python3
"""Exact fixed-board K4 ordinary blocks; mathematical data only, no Lab imports."""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
from itertools import permutations
import json
from pathlib import Path

from generate_finite_k4_fixed_seeds import ROOT, DATA, validate, output

MARKS = [[(0,0),(0,0),(0,0)],[(0,0),(0,0),(0,1)],[(0,0),(0,0),(1,0)],
         [(0,0),(0,0),(1,1)],[(0,0),(0,1),(0,2)],[(0,0),(0,1),(1,0)],
         [(0,0),(0,1),(1,2)],[(0,0),(1,0),(2,0)],[(0,0),(1,0),(2,1)],
         [(0,0),(1,1),(2,2)]]


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def key(cells):
    def packed(t):
        rs, cs, z = {}, {}, 0
        for i, j in t:
            rs.setdefault(i, len(rs))
            cs.setdefault(j, len(cs))
            z = 25*z + 5*rs[i] + cs[j]
        return z
    return min(packed(a+b) for a in permutations(cells[:3]) for b in permutations(cells[3:]))


def strict_ldl(matrix):
    size = len(matrix)
    require(size > 0 and all(len(row)==size for row in matrix), 'invalid square block')
    require(all(type(q) is Q for row in matrix for q in row), 'block entries must be exact Fractions')
    require(all(matrix[i][j]==matrix[j][i] for i in range(size) for j in range(size)),
            'asymmetric block')
    lower = [[Q(i==j) for j in range(size)] for i in range(size)]
    diagonal = []
    for i in range(size):
        pivot = matrix[i][i]-sum(lower[i][k]**2*diagonal[k] for k in range(i))
        require(pivot > 0, 'nonpositive LDL pivot')
        diagonal.append(pivot)
        for j in range(i+1, size):
            lower[j][i] = (matrix[j][i]-sum(lower[j][k]*lower[i][k]*diagonal[k]
                                          for k in range(i)))/pivot
    require(all(matrix[i][j]==sum(lower[i][k]*diagonal[k]*lower[j][k]
                                 for k in range(size)) for i in range(size) for j in range(size)),
            'LDL reconstruction failed')
    return lower, diagonal


def blocks(case, role_keys, seed):
    coefficients = dict(zip(role_keys, map(Q,case['seed'])))
    n, mark = case['n'], MARKS[seed]
    nr, nc = 1+max(i for i,j in mark), 1+max(j for i,j in mark)
    R, C = n-nr, n-nc
    require(R>0 and C>0, 'ordinary counts must be positive')
    H = lambda i,j,k,l: coefficients[key(tuple(mark)+((i,j),(k,l)))]
    average = lambda first,count,f,i,j: ((f(first,first)+(count-1)*f(first,first+1))/count
                                       if i==j==first else f(i,j))
    points = [(i,j) for i in range(nr+1) for j in range(nc+1)]
    full = [[average(nr,R,lambda i,k:average(nc,C,lambda j,l:H(i,j,k,l),x[1],y[1]),x[0],y[0])
             for y in points] for x in points]
    weight = [Q((R if i==nr else 1)*(C if j==nc else 1)) for i,j in points]
    require(all(sum(b*w for b,w in zip(row,weight))==0 for row in full), 'weighted kernel failed')
    row = [[average(nc,C,lambda j,l:H(nr,j,nr,l)-H(nr,j,nr+1,l),x,y)
            for y in range(nc+1)] for x in range(nc+1)]
    column = [[average(nr,R,lambda i,k:H(i,nc,k,nc)-H(i,nc,k,nc+1),x,y)
               for y in range(nr+1)] for x in range(nr+1)]
    interaction = [[H(nr,nc,nr,nc)-H(nr,nc,nr+1,nc)-H(nr,nc,nr,nc+1)+H(nr,nc,nr+1,nc+1)]]
    result = {'principal':[r[:-1] for r in full[:-1]],'row':row,'column':column,'interaction':interaction}
    certificates = {name:strict_ldl(matrix) for name,matrix in result.items()}
    return {'n':n,'seed':seed,'nr':nr,'nc':nc,'R':R,'C':C,'full':full,'weight':weight,
            'blocks':result,'certificates':certificates}


def render_lookup(keys):
    def tree(lo, hi):
        if hi-lo==1:
            return str(lo)
        middle = (lo+hi)//2
        return f'(if key < {keys[middle]} then {tree(lo,middle)} else {tree(middle,hi)})'
    return '''import DR.Certificates.FiniteK4Orbits

/-! Generated exact balanced lookup in the sorted 407-role catalogue. The
lookup is verified on every catalogue entry; no outside key is a certificate. -/
namespace DittertRybin.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def finiteK4FixedRoleLookup (key : ℕ) : Fin 407 :=
  ''' + tree(0,407) + '''

theorem finiteK4FixedRoleLookup_key (i : Fin 407) :
    finiteK4FixedRoleLookup (finiteK4RoleKeys.get i) = i := by
  fin_cases i <;> decide +kernel

end DittertRybin.Certificates
'''


def lean_q(q):
    return str(q.numerator) if q.denominator==1 else f'({q.numerator}/{q.denominator})'


def vec(items):
    return '#v['+','.join(items)+']'


def render_case(result):
    n, seed = result['n'], result['seed']
    text = f'''import DR.Certificates.FiniteK4FixedBlocks
import DR.Certificates.FiniteK4FixedSeedData
import DR.Certificates.StrictGram

/-! Generated exact fixed-board block data and kernel checks for {n}×{n}, seed {seed}.
No numerical PSD test is a premise. -/
namespace DittertRybin.Certificates.FiniteK4FixedCases.M{n}S{seed}
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

'''
    for name,(lower,weights) in result['certificates'].items():
        size=len(weights)
        text += f'def {name}Weights : Vector ℚ {size} :=\n  '+vec([lean_q(q) for q in weights])+'\n'
        text += f'def {name}Factor : Vector (Vector ℚ {size}) {size} :=\n  '
        text += vec([vec([lean_q(lower[j][i]) for j in range(size)]) for i in range(size)])+'\n'
        text += f'def {name}Gram : GramCertificate {size} {size} :=\n  ⟨{name}Weights.get, fun i j => ({name}Factor.get i).get j⟩\n\n'
    text += f'''theorem full_kernel :
    (finiteK4FixedFullMatrix finiteK4Fixed{n}Coefficient {n} {n} {seed}).mulVec
      (finiteK4FixedWeight {n} {n} {seed} : Fin (fourRowFiniteSeedFullSize {seed}) → ℚ) = 0 := by
  ext i
  fin_cases i <;> decide +kernel

'''
    for name in result['certificates']:
        if name=='principal':
            matrix=f'finiteK4FixedPrincipalMatrix finiteK4Fixed{n}Coefficient {n} {n} {seed}'
        elif name=='row':
            matrix=f'finiteK4FixedRowMatrix finiteK4Fixed{n}Coefficient {n} {seed}'
        elif name=='column':
            matrix=f'finiteK4FixedColumnMatrix finiteK4Fixed{n}Coefficient {n} {seed}'
        else:
            matrix=f'finiteK4FixedInteractionMatrix finiteK4Fixed{n}Coefficient {seed}'
        if name == 'interaction':
            text += f'theorem {name}_valid : {name}Gram.StrictValid ({matrix}) := by\n  decide +kernel\n\n'
            continue
        text += f'''theorem {name}_valid : {name}Gram.StrictValid ({matrix}) := by
  refine ⟨⟨?_,?_⟩,?_,?_,?_⟩
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel

'''
    return text+f'end DittertRybin.Certificates.FiniteK4FixedCases.M{n}S{seed}\n'


def render_checked(n):
    require(n in [5,20], 'unsupported fixed board')
    text='\n'.join(f'import DR.Certificates.FiniteK4FixedCases.M{n}S{s}'
                   for s in range(10))
    text += '\nimport DR.Certificates.FiniteK4FixedKernelCast\n\n/-! All ten exact block certificates for this fixed board. -/\n'
    text += 'namespace DittertRybin.Certificates\nset_option Elab.async false\n\n'
    text += f'''theorem finiteK4Fixed{n}_full_kernel (s : Fin 10) :
    (finiteK4FixedFullMatrix finiteK4Fixed{n}Coefficient {n} {n} s).mulVec
      (finiteK4FixedWeight {n} {n} s : Fin (fourRowFiniteSeedFullSize s) → ℚ) = 0 := by
  fin_cases s
'''
    for seed in range(10):
        text += f'  · exact FiniteK4FixedCases.M{n}S{seed}.full_kernel\n'
    text += f'''\ntheorem finiteK4Fixed{n}_full_kernel_real (s : Fin 10) :
    (finiteK4FixedFullMatrix (fun k => (finiteK4Fixed{n}Coefficient k : ℝ)) {n} {n} s).mulVec
      (finiteK4FixedWeight {n} {n} s : Fin (fourRowFiniteSeedFullSize s) → ℝ) = 0 :=
  finiteK4FixedFullMatrix_kernel_cast _ _ _ _ (finiteK4Fixed{n}_full_kernel s)

'''
    for name in ['principal','row','column','interaction']:
        matrix={'principal':f'finiteK4FixedPrincipalMatrix (fun k => (finiteK4Fixed{n}Coefficient k : ℝ)) {n} {n} s',
                'row':f'finiteK4FixedRowMatrix (fun k => (finiteK4Fixed{n}Coefficient k : ℝ)) {n} s',
                'column':f'finiteK4FixedColumnMatrix (fun k => (finiteK4Fixed{n}Coefficient k : ℝ)) {n} s',
                'interaction':f'finiteK4FixedInteractionMatrix (fun k => (finiteK4Fixed{n}Coefficient k : ℝ)) s'}[name]
        cast={'principal':'finiteK4FixedPrincipalMatrix_cast','row':'finiteK4FixedRowMatrix_cast',
              'column':'finiteK4FixedColumnMatrix_cast','interaction':'finiteK4FixedInteractionMatrix_cast'}[name]
        text += f'theorem finiteK4Fixed{n}_{name}_posDef (s : Fin 10) :\n    ({matrix}).PosDef := by\n  rw [←{cast}]\n  fin_cases s\n'
        for seed in range(10):
            prefix=f'FiniteK4FixedCases.M{n}S{seed}'
            text += f'  · exact {prefix}.{name}Gram.strictValid_posDef _ {prefix}.{name}_valid\n'
        text += '\n'
    return text+'end DittertRybin.Certificates\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--all', action='store_true')
    parser.add_argument('--case', nargs=2, type=int, action='append', default=[])
    args = parser.parse_args()
    data = json.loads(DATA.read_text())
    validate(data)
    output(ROOT/'DR/Certificates/FiniteK4FixedRoleLookup.lean',render_lookup(data['role_keys']),args.check)
    require(not (args.all and args.case), 'choose all or explicit cases')
    chosen = [(n,s) for n in [5,20] for s in range(10)] if args.all else (list(map(tuple,args.case)) or [(5,0),(5,9)])
    require(len(set(chosen))==len(chosen) and all(n in [5,20] and 0<=s<10 for n,s in chosen), 'case coverage differs')
    if args.all:
        for n in [5,20]:
            output(ROOT/f'DR/Certificates/FiniteK4FixedChecked{n}.lean',render_checked(n),args.check)
        output(ROOT/'DR/Certificates/FiniteK4FixedCheckedBlocks.lean',
               'import DR.Certificates.FiniteK4FixedChecked5\n'
               'import DR.Certificates.FiniteK4FixedChecked20\n',args.check)
    for case in data['cases']:
        result = [blocks(case,data['role_keys'],s) for s in range(10)]
        for r in result:
            if (r['n'],r['seed']) in chosen:
                path=ROOT/f"DR/Certificates/FiniteK4FixedCases/M{r['n']}S{r['seed']}.lean"
                output(path,render_case(r),args.check)
        pivots = sum(len(d) for r in result for L,d in r['certificates'].values())
        require(pivots==150,'unexpected fixed-board pivot coverage')
        print(f"PASS generation: {case['n']}×{case['n']}, ten kernels and 40 strict blocks, {pivots} pivots")


if __name__ == '__main__':
    main()
