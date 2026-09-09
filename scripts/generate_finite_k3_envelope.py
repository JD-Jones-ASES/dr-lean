#!/usr/bin/env python3
"""Exact data for the complete finite K=3 rectangular envelope.

The JSON supplies mathematical rational coefficients only. This generator
independently reconstructs the documented eight blocks and exact LDL factors;
it imports no Lab implementation. Lean checks every formula and factor.
"""
import argparse
import ast
import hashlib
import json
from math import lcm
from fractions import Fraction as F
from pathlib import Path
from generate_finite_k3_orbits import key, MARKS, PATTERNS

BASE=Path(__file__).resolve().parents[1]
SOURCE=BASE/'data/finite_k3_coefficients.json'
RANGES=((4,6,959),(5,5,120),(6,6,237),(7,7,24),(8,8,14),(9,9,11))
EXPECTED=tuple((m,n)for m,lo,hi in RANGES for n in range(lo,hi+1))
SHARDS=tuple((m,a,min(a+15,hi))for m,lo,hi in RANGES for a in range(lo,hi+1,16))

def rational(q):
    q=F(q)
    return str(q.numerator) if q.denominator==1 else f'({q.numerator}/{q.denominator})'

def vector(xs):return '#v['+','.join(xs)+']'

def load_cases(path=SOURCE):
    raw=json.loads(path.read_text())
    if set(raw)!={'schema_version','cases'} or raw['schema_version']!=1:
        raise ArithmeticError('Unexpected finite K3 source schema')
    seen=[];cases={}
    for case in raw['cases']:
        if set(case)!={'m','n','seed'}:raise ArithmeticError('Unexpected finite K3 case fields')
        if type(case['m'])is not int or type(case['n'])is not int:
            raise ArithmeticError('Nonintegral finite K3 dimensions')
        if not isinstance(case['seed'],list)or any(type(x)is not str for x in case['seed']):
            raise ArithmeticError('Nonliteral rational coefficient data')
        shape=(case['m'],case['n']);seen.append(shape)
        if shape in cases:raise ArithmeticError(f'Duplicate finite K3 shape {shape}')
        if len(case['seed'])!=93:raise ArithmeticError(f'Wrong coefficient count for {shape}')
        cases[shape]=tuple(map(F,case['seed']))
    if tuple(seen)!=EXPECTED or len(EXPECTED)!=1330 or len(set(EXPECTED))!=1330:
        raise ArithmeticError('Missing, extra, reordered or duplicate finite K3 case')
    return cases

def catalog():
    out={};cells=[(i,j)for i in range(4)for j in range(4)]
    for e,f in MARKS:
        for a in cells:
            for b in cells:out.setdefault(key(e,f,a,b),len(out))
    if len(out)!=93:raise ArithmeticError('Wrong universal entry catalogue size')
    return out

CATALOG=catalog()

def exact_ldl(A):
    n=len(A)
    if any(len(row)!=n for row in A)or any(A[i][j]!=A[j][i]for i in range(n)for j in range(n)):
        raise ArithmeticError('Nonsymmetric exact LDL target')
    L=[[F(i==j)for j in range(n)]for i in range(n)];d=[]
    for j in range(n):
        pivot=A[j][j]-sum((L[j][a]**2*d[a]for a in range(j)),F(0))
        if pivot<=0:raise ArithmeticError(f'Nonpositive exact pivot {j}: {pivot}')
        d.append(pivot)
        for i in range(j+1,n):
            L[i][j]=(A[i][j]-sum((L[i][a]*d[a]*L[j][a]for a in range(j)),F(0)))/pivot
    B=list(map(list,zip(*L)))
    if any(A[i][j]!=sum((d[a]*B[a][i]*B[a][j]for a in range(n)),F(0))for i in range(n)for j in range(n)):
        raise ArithmeticError('Exact LDL reconstruction failed')
    return d,B

def case_blocks(m,n,coeff):
    result=[]
    for e,f in MARKS:
        k=len({e[1],f[1]});ell=n-k
        if ell<2:raise ArithmeticError('Insufficient ordinary columns')
        dc=[(i,j)for i in range(m)for j in range(k)]
        def entry(a,b):return coeff[CATALOG[key(e,f,a,b)]]
        D=[[entry((i,k),(j,k))for j in range(m)]for i in range(m)]
        O=[[entry((i,k),(j,k+1))for j in range(m)]for i in range(m)]
        H=[[D[i][j]-O[i][j]for j in range(m)]for i in range(m)]
        def bentry(i,j):
            if i<len(dc)and j<len(dc):return entry(dc[i],dc[j])
            if i<len(dc):return entry(dc[i],(j-len(dc),k))
            if j<len(dc):return entry(dc[j],(i-len(dc),k))
            i-=len(dc);j-=len(dc)
            return O[i][j]+(D[i][j]-O[i][j])/ell
        B=[[bentry(i,j)for j in range(len(dc)+m)]for i in range(len(dc)+m)]
        v=[F(1)]*len(dc)+[F(ell)]*m
        if any(sum((x*y for x,y in zip(row,v)),F(0))for row in B):
            raise ArithmeticError(f'Nonzero aggregate kernel for {(m,n,e,f)}')
        B0=[row[:-1]for row in B[:-1]]
        result.append((exact_ldl(H),exact_ldl(B0)))
    return result

def render_patterns():
    def table(n):
        def at(t,a,b):
            xs=(0,t,a,b)
            return str(PATTERNS.index(tuple(xs.index(x)for x in xs)))
        return vector(vector(vector(at(t,a,b)for b in range(n))for a in range(n))for t in range(2))
    return '\n'.join(['import DR.Certificates.FiniteK3OrbitData','','/-! Generated one-axis lookups; every value is checked against actual label compression. -/',
      'namespace DittertRybin.Certificates','','def finiteK3EnvelopeRowPatterns : Vector (Vector (Vector (Fin 15) 9) 9) 2 :=','  '+table(9),'',
      'def finiteK3EnvelopeColPatterns : Vector (Vector (Vector (Fin 15) 4) 4) 2 :=','  '+table(4),'','end DittertRybin.Certificates',''])

def render_sparse():
    source=(BASE/'DR/Certificates/FiniteK3QuarticData.lean').read_text()
    chunk=source.split('def finiteK3QuarticRows :')[1].split('def finiteK3QuarticMultiplicity')[0]
    rows=ast.literal_eval(chunk[chunk.index('#v['):].strip().replace('#v',''))
    if len(rows)!=33 or any(len(r)!=93 or any(type(x)is not int or x<0 for x in r)for r in rows):
        raise ArithmeticError('Wrong exact quartic row data')
    terms=[[(v,k)for k,v in enumerate(r)if v]for r in rows]
    width=max(map(len,terms))
    if width!=6 or sum(map(len,terms))!=93:raise ArithmeticError('Unexpected sparse quartic support')
    return '\n'.join(['import DR.Certificates.FiniteK3QuarticData','',
      '/-! Exact sparse storage of the same literal33 coefficient rows; equality is checked separately. -/',
      'namespace DittertRybin.Certificates','',
      'def finiteK3QuarticSparseTerms : Vector (Vector (Nat × Fin 93) 6) 33 :=',
      '  #v['+',\n    '.join(vector(f'({v},{k})'for v,k in ts+[(0,0)]*(6-len(ts)))for ts in terms)+']','',
      'end DittertRybin.Certificates',''])

def render_manifest():
    return json.dumps({'schema_version':1,'case_count':1330,
      'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
      'cases':[{'m':m,'n':n,'module':f'DR.Certificates.FiniteK3Cases.M{m}N{n}'}for m,n in EXPECTED],
      'shards':[{'m':m,'lower':lo,'upper':hi,'count':hi-lo+1,
        'module':f'DR.Certificates.FiniteK3Dispatch.M{m}N{lo}To{hi}'}for m,lo,hi in SHARDS]},indent=2)+'\n'

def validate_manifest(raw):
    expected=json.loads(render_manifest())
    if raw!=expected:raise ArithmeticError('Changed, missing, extra, duplicate or reordered manifest entry')
    flattened=tuple((m,n)for m,lo,hi in SHARDS for n in range(lo,hi+1))
    if flattened!=EXPECTED:raise ArithmeticError('Dispatch shards do not exactly cover the canonical envelope')

def render_dispatch(m,lo,hi):
    lines=[f'import DR.Certificates.FiniteK3Cases.M{m}N{n}'for n in range(lo,hi+1)]
    lines+=['import Mathlib.Tactic.IntervalCases','',
      '/-! Bounded exact coverage: each branch carries its actual rational certificate. -/',
      f'namespace DittertRybin.Certificates.FiniteK3Dispatch.C{m}N{lo}To{hi}','',
      f'theorem exists_valid (n : Nat) (hlo : {lo}≤n) (hhi : n≤{hi}) :',
      f'    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid {m} n (by decide) coeff := by',
      '  interval_cases n']
    lines += [f'  · exact ⟨FiniteK3Cases.C{m}N{n}.coeff,FiniteK3Cases.C{m}N{n}.valid⟩'for n in range(lo,hi+1)]
    lines += ['',f'end DittertRybin.Certificates.FiniteK3Dispatch.C{m}N{lo}To{hi}','']
    return '\n'.join(lines)

def render_case(m,n,coeff):
    blocks=case_blocks(m,n,coeff)
    denominator=lcm(*(q.denominator for q in coeff))
    numerators=[int(q*denominator)for q in coeff]
    if any(F(a,denominator)!=q for a,q in zip(numerators,coeff)):
        raise ArithmeticError('Common denominator changed rational coefficients')
    lines=['import DR.Certificates.FiniteK3EnvelopeSparseEquations','',
      f'/-! Exact mathematical rational data and kernel checks for K3 on {m}x{n}.',
      f'Reproduce with scripts/generate_finite_k3_envelope.py --case {m} {n} --check. -/',
      f'namespace DittertRybin.Certificates.FiniteK3Cases.C{m}N{n}',
      'open scoped BigOperators','',
      'def numerators : Vector ℤ 93 :=','  '+vector(map(str,numerators)),
      f'def denominator : Nat := {denominator}',
      'def coeff (i : Fin 93) : ℚ := (numerators.get i:ℚ)/denominator','']
    for t,(h,b) in enumerate(blocks):
        for name,(d,factor) in ((f'h{t}',h),(f'b{t}',b)):
            size=len(d)
            lines += [f'def {name}Weights : Vector ℚ {size} :=','  '+vector(map(rational,d)),
              f'def {name}Factors : Vector (Vector ℚ {size}) {size} :=',
              '  #v['+',\n    '.join(vector(map(rational,row))for row in factor)+']',
              f'def {name}Gram : GramCertificate {size} {size} :=',
              f'  ⟨fun i => {name}Weights.get i,fun i j => ({name}Factors.get i).get j⟩','']
    lines+=['set_option maxRecDepth 100000 in','set_option maxHeartbeats 32000000 in',
      f'private theorem sparse_equations_checked : FiniteK3EnvelopeSparseIntegerEquations denominator (numerators.get 0) numerators.get := by',
      '  decide +kernel','',
      'private theorem integer_equations_checked : FiniteK3EnvelopeIntegerEquations denominator (numerators.get 0) numerators.get :=',
      '  finiteK3EnvelopeIntegerEquations_of_sparse _ _ _ sparse_equations_checked','',
      f'private theorem equations_checked : FiniteK3EnvelopeEquations {m} {n} coeff := by',
      f'  exact finiteK3EnvelopeEquations_of_integer {m} {n} denominator (numerators.get 0) numerators.get',
      '    (by decide) (by decide +kernel) integer_equations_checked','']
    for t in range(4):
        for name,target in ((f'h{t}',f'finiteK3EnvelopeTableH coeff {m} (by decide) {t}'),
                            (f'b{t}',f'finiteK3EnvelopeTableB0 coeff {m} {n} (by decide) {t}')):
            lines+=['set_option maxRecDepth 100000 in','set_option maxHeartbeats 32000000 in',
              f'private theorem {name}_checked : {name}Gram.StrictValid ({target}) := by',
              f'  change {name}Gram.StrictValid (Matrix.of (fun i j : Fin {len(blocks[t][0 if name.startswith("h") else 1][0])} => ({target}) i j))',
              '  decide +kernel','']
    lines+=['set_option maxRecDepth 100000 in','set_option maxHeartbeats 32000000 in',
      'private theorem kernels_checked : ∀ s : Fin 4,∀ i,',
      f'    (∑ j,finiteK3EnvelopeFlatTableB coeff {m} {n} (by decide) s i j*',
      f'      finiteK3EnvelopeKernel {m} {n} s j)=0 := by',
      '  decide +kernel','',
      f'theorem valid : FiniteK3EnvelopeValid {m} {n} (by decide) coeff := by',
      '  refine ⟨equations_checked,?_⟩','  intro s',
      f'  have hk := kernels_checked s',
      f'  rw [← finiteK3EnvelopeFlatB_eq_table coeff {m} {n} (by decide) (by decide) s] at hk',
      '  fin_cases s']
    for t in range(4):
        lines += ['  · refine ⟨?_,?_,hk⟩',
          f'    · rw [finiteK3EnvelopeH_eq_table coeff {m} (by decide) (by decide)]',
          f'      exact h{t}Gram.strictValid_posDef _ h{t}_checked',
          f'    · rw [finiteK3EnvelopeB0_eq_table coeff {m} {n} (by decide) (by decide)]',
          f'      exact b{t}Gram.strictValid_posDef _ b{t}_checked']
    lines += ['',f'end DittertRybin.Certificates.FiniteK3Cases.C{m}N{n}','']
    return '\n'.join(lines)

def main():
    p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');p.add_argument('--patterns',action='store_true');p.add_argument('--all',action='store_true');p.add_argument('--manifest',action='store_true');p.add_argument('--dispatch',action='store_true');p.add_argument('--shard',nargs=3,type=int,action='append',default=[]);p.add_argument('--case',nargs=2,type=int,action='append',default=[]);args=p.parse_args()
    cases=load_cases()
    outputs={}
    if args.patterns:
        outputs[BASE/'DR/Certificates/FiniteK3EnvelopePatternData.lean']=render_patterns()
        outputs[BASE/'DR/Certificates/FiniteK3QuarticSparseData.lean']=render_sparse()
    if args.all or args.manifest or args.dispatch or args.shard:
        outputs[BASE/'data/finite_k3_manifest.json']=render_manifest()
        validate_manifest(json.loads(render_manifest()))
    if args.dispatch and args.shard:raise ArithmeticError('Select all dispatch shards or an explicit list')
    selected_shards=SHARDS if args.dispatch else tuple(map(tuple,args.shard))
    if len(selected_shards)!=len(set(selected_shards))or any(x not in SHARDS for x in selected_shards):
        raise ArithmeticError('Duplicate or noncanonical dispatch shard')
    for m,lo,hi in selected_shards:
        outputs[BASE/f'DR/Certificates/FiniteK3Dispatch/M{m}N{lo}To{hi}.lean']=render_dispatch(m,lo,hi)
    if args.all and args.case:raise ArithmeticError('Select all cases or an explicit list')
    selection=EXPECTED if args.all else tuple(map(tuple,args.case))
    if len(selection)!=len(set(selection)):raise ArithmeticError('Duplicate generated case selection')
    for shape in selection:
        if shape not in cases:raise ArithmeticError(f'Case outside exact envelope: {shape}')
        m,n=shape
        outputs[BASE/f'DR/Certificates/FiniteK3Cases/M{m}N{n}.lean']=render_case(m,n,cases[shape])
    for path,content in outputs.items():
        if args.check:
            if not path.exists()or path.read_text()!=content:raise ArithmeticError(f'Changed generated data: {path}')
        elif not path.exists()or path.read_text()!=content:
            path.parent.mkdir(parents=True,exist_ok=True)
            path.write_text(content)
    if args.all:
        expected_paths={BASE/f'DR/Certificates/FiniteK3Cases/M{m}N{n}.lean'for m,n in EXPECTED}
        actual_paths=set((BASE/'DR/Certificates/FiniteK3Cases').glob('M*N*.lean'))
        if actual_paths!=expected_paths:raise ArithmeticError('Missing or extra generated case modules')
    print(f'Validated exact canonical coverage of {len(cases)} finite K3 cases; {len(selection)} selected case modules')

if __name__=='__main__':main()
