#!/usr/bin/env python3
"""Reproduce the kernel-checked sparse order-five singleton identity.

Uses exact Fraction arithmetic and the literal Lean numerator. The independent
SymPy coefficient generator supplies the required comparison JSON. Every
emitted arithmetic step is proved again by ordinary Lean kernel reduction;
this Python program is an optional reproducer, never a trusted proof oracle.

Example (from the repository root):
  python scripts/generate_singleton_coefficients.py --output /tmp/singleton.json
  python scripts/generate_singleton_sparse.py --coefficient-json /tmp/singleton.json --check
"""
from argparse import ArgumentParser
from pathlib import Path
from fractions import Fraction as F
import ast,json,re
parser = ArgumentParser(description=__doc__)
parser.add_argument("--coefficient-json", required=True, type=Path,
                    help="Exact output of generate_singleton_coefficients.py")
parser.add_argument("--check", action="store_true", help="Compare all generated files without writing")
args = parser.parse_args()
root = Path(__file__).resolve().parents[1]
outputs = {}
def emit(path, text):
    outputs[root / path] = text
src=(root / 'DR/Certificates/SpectralFiveSingletonPolynomial.lean').read_text()
body=src[src.index('def uPolynomial'):src.index('theorem singletonScale_pos')]
entries=re.findall(r'def (\w+) : ([^\n]+) :=\s*(.*?)(?=\ndef |\Z)',body,re.S)
nodes=[]; bykey={}; names={}; rational={}; roots=[]
def clean(p):return {e:c for e,c in p.items() if c}
def plus(p,q,sign=1):
 z=p.copy()
 for e,c in q.items():z[e]=z.get(e,F(0))+sign*c
 return clean(z)
def times(p,q):
 z={}
 for e,c in p.items():
  for f,d in q.items():
   g=tuple(a+b for a,b in zip(e,f));z[g]=z.get(g,F(0))+c*d
 return clean(z)
def rat(e):
 if isinstance(e,ast.Constant):return F(e.value)
 if isinstance(e,ast.Name):return rational[e.id]
 if isinstance(e,ast.UnaryOp):return -rat(e.operand)
 a,b=rat(e.left),rat(e.right)
 return {ast.Add:lambda:a+b,ast.Sub:lambda:a-b,ast.Mult:lambda:a*b,ast.Div:lambda:a/b,ast.Pow:lambda:a**int(b)}[type(e.op)]()
def intern(key):
 if key in bykey:return bykey[key]
 op,*args=key
 if op=='c':p={} if not args[0] else {(0,0,0):args[0]}
 elif op=='x':p={tuple(int(k==args[0]) for k in range(3)):F(1)}
 elif op=='add':p=plus(nodes[args[0]][1],nodes[args[1]][1])
 elif op=='sub':p=plus(nodes[args[0]][1],nodes[args[1]][1],-1)
 elif op=='mul':p=times(nodes[args[0]][1],nodes[args[1]][1])
 elif op=='pow':
  p={(0,0,0):F(1)}
  for _ in range(args[1]):p=times(p,nodes[args[0]][1])
 i=len(nodes);bykey[key]=i;nodes.append((key,p));return i
def node(e,used,refs):
 if isinstance(e,ast.Name):refs.add(e.id);return names[e.id]
 if isinstance(e,ast.Constant):i=intern(('c',F(e.value)))
 elif isinstance(e,ast.Call):
  i=intern(('c',rat(e.args[0]))) if e.func.id=='C' else intern(('x',int(rat(e.args[0]))))
 elif isinstance(e,ast.BinOp):
  a=node(e.left,used,refs)
  if isinstance(e.op,ast.Pow):i=intern(('pow',a,int(rat(e.right))))
  else:i=intern(({ast.Add:'add',ast.Sub:'sub',ast.Mult:'mul'}[type(e.op)],a,node(e.right,used,refs)))
 else:raise ValueError(ast.dump(e))
 used.add(i);return i
for name,typ,rhs in entries:
 py=re.sub(r'X ([012])',r'X(\1)',rhs).replace('^','**');py=re.sub(r'C (\w+)',r'C(\1)',py)
 tree=ast.parse('('+py.strip()+')',mode='eval').body
 if typ=='ℚ':rational[name]=rat(tree);continue
 used=set();refs=set();i=node(tree,used,refs);names[name]=i;roots.append((name,i,sorted(used),sorted(refs)))
expected={tuple(t[:3]):F(t[3]) for t in json.loads(args.coefficient_json.read_text())['terms']}
assert nodes[names['scaledSingletonPolynomial']][1]==expected
print('exact DAG:',len(nodes),'nodes;',sum(len(p)for _,p in nodes),'stored terms;',max(len(p)for _,p in nodes),'maximum support')
ns='DittertRybin.Certificates.SpectralFiveSingleton'
def q(c):return f'({c.numerator} : ℚ)' if c.denominator==1 else f'(({c.numerator} : ℚ) / {c.denominator})'
def data(i):return f'node{i:02}'
base='DR/Certificates/SpectralFiveSingleton'
s=f'import DR.Certificates.SparsePolynomialTensor\n\nnamespace {ns}.SparseStages\nset_option maxRecDepth 200000\nset_option maxHeartbeats 4000000\n\ndef mkTerm (t x y : ℕ) (c : ℚ) : SparsePolynomial.Term := ((t,x,y),c)\n\n'
for i,(key,p) in enumerate(nodes):
 ts=[f'mkTerm {e[0]} {e[1]} {e[2]} {q(c)}' for e,c in sorted(p.items(),key=lambda z:(z[0][1],z[0][2],z[0][0]))]
 s+=f'def {data(i)} : SparsePolynomial.Polynomial :=\n  ['+',\n   '.join(ts)+']\n\n'
s+=f'end {ns}.SparseStages\n'
emit(base+'SparseStageData.lean', s)
def lhs(key):
 op,*a=key
 if op=='c':return 'SparsePolynomial.constant '+q(a[0])
 if op=='x':return f'SparsePolynomial.var {a[0]}'
 if op=='pow':return f'SparsePolynomial.pow {data(a[0])} {a[1]}'
 return f'SparsePolynomial.{op} {data(a[0])} {data(a[1])}'
ng=(len(nodes)+7)//8
for g in range(ng):
 s=f'import DR.Certificates.SpectralFiveSingletonSparseStageData\n\nnamespace {ns}.SparseStages\nset_option maxRecDepth 200000\nset_option maxHeartbeats 64000000\n\n'
 for i in range(8*g,min(8*g+8,len(nodes))):
  s+=f'theorem {data(i)}_checked : {lhs(nodes[i][0])} = {data(i)} := by\n  decide +kernel\n\n'
 s+=f'end {ns}.SparseStages\n'
 emit(base+f'/SparseStageGroup{g:02}.lean', s)
s='import DR.Certificates.SpectralFiveSingletonSparseSource\n'
s+=''.join(f'import DR.Certificates.SpectralFiveSingleton.SparseStageGroup{g:02}\n' for g in range(ng))
s+=f'\nnamespace {ns}.SparseStages\nset_option maxRecDepth 200000\nset_option maxHeartbeats 4000000\n\n'
for name,i,used,refs in roots:
 s+=f'theorem {name}_checked : SparseSource.{name} = {data(i)} := by\n  unfold SparseSource.{name}\n'
 if name=='energyPolynomial':s+='  rw [show ((1 - 24 / 625) / 5 : ℚ) = 601 / 3125 by norm_num]\n'
 if refs:s+='  simp only ['+', '.join(n+'_checked' for n in refs)+']\n'
 # Each source occurrence uses only the listed operations; numerical rational expressions reduce definitionally.
 aliases=(["SparseSource.singletonScale"] if name=='scaledSingletonPolynomial' else [])+[data(k)+'_checked' for k in used]
 s+='  simp only ['+', '.join(aliases)+']\n\n'
s+=f'end {ns}.SparseStages\n'
emit(base+'SparseStages.lean', s)
s=f'''import DR.Certificates.SpectralFiveSingletonSparseStageData
import DR.Certificates.SpectralFiveSingletonPowerData

namespace {ns}.SparseStages
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000

theorem final_tensor_checked : {data(names['scaledSingletonPolynomial'])} =
    SparsePolynomial.fromTensor singletonPowerCoefficients := by
  decide +kernel

end {ns}.SparseStages
'''
emit(base+'SparseTensorCheck.lean', s)

if args.check:
    differences = [str(path.relative_to(root)) for path, text in outputs.items()
                   if not path.exists() or path.read_text() != text]
    if differences:
        raise SystemExit("Generated content differs: " + ", ".join(differences))
    print(f"All {len(outputs)} generated Lean files reproduce exactly.")
else:
    for path, text in outputs.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        if not path.exists() or path.read_text() != text:
            path.write_text(text)
    print(f"Wrote {len(outputs)} Lean files. Build them to check every step.")
