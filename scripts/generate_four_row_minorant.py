#!/usr/bin/env python3
"""Reproduce the exact repeated-row minorant coefficient checks.

Source: Analytic-Lab P0174 HIGHER_ORDER_COLLISIONS.md, equation (11), and
k4_minorant_certificate.py COMPACT_TERMS. The 21 literal integer monomials
are independently checked against the displayed compactification in Lean.
All 35^3 elevated coefficients are checked by ordinary Lean kernel reduction.
This certificate proves only the repeated-row family, not the complete minorant.
"""
from pathlib import Path
import argparse
from itertools import product

TERMS = (
 ((2,2,2),16),((2,2,1),-16),((2,1,2),-32),((2,1,1),48),((2,1,0),-16),
 ((2,0,2),16),((2,0,1),-32),((2,0,0),16),((1,2,2),-12),((1,2,1),8),
 ((1,1,1),8),((1,1,0),-4),((1,0,2),12),((1,0,1),-16),((1,0,0),4),
 ((0,2,2),-4),((0,2,1),8),((0,1,2),6),((0,1,1),-11),((0,1,0),2),((0,0,1),1),
)

def moment(a,i): return (1122,33*i,i*(i-1))[a]
def numerator(i,j,k): return sum(c*moment(a,i)*moment(b,j)*moment(d,k) for (a,b,d),c in TERMS)

def render():
    values={(i,j,k):numerator(i,j,k) for i,j,k in product(range(35),repeat=3)}
    if len(values)!=42875 or [q for q,v in values.items() if v==0]!=[(0,0,0)]:
        raise ArithmeticError("Coefficient coverage or zero set changed")
    if min(v for v in values.values() if v)!=6323724:
        raise ArithmeticError("Exact positive coefficient margin changed")
    patterns='\n'.join(f'  | {a}, {b}, {d} => {c}' for (a,b,d),c in TERMS)
    expression=' +\n    '.join(f'({c})*degree34MomentNumerator {a} i*degree34MomentNumerator {b} j*degree34MomentNumerator {d} k' for (a,b,d),c in TERMS)
    data=f'''import DR.Certificates.BernsteinTransform
import Mathlib.Tactic.FinCases

/-! Exact repeated-row certificate data from P0174 equation (11).
Regenerate with `scripts/generate_four_row_minorant.py --check`.
The common coefficient denominator is 1122^3 = 1412467848. -/

namespace DittertRybin.Certificates.FourRowMinorant

/-- Literal coefficients in the compactified (X,T,Z) polynomial. -/
def compactPowerCoefficient (a b c : Fin 3) : ℤ :=
  match a.val, b.val, c.val with
{patterns}
  | _, _, _ => 0

/-- Numerators for choose(i,k)/choose(34,k), k=0,1,2, over denominator1122. -/
def degree34MomentNumerator (a : Fin 3) (i : Fin 35) : ℤ :=
  match a.val with
  | 0 => 1122
  | 1 => 33*(i.val:ℤ)
  | _ => (i.val:ℤ)*((i.val:ℤ)-1)

/-- The exact numerator of each of the 42,875 elevated Bernstein coefficients. -/
def compactBernsteinNumerator (i j k : Fin 35) : ℤ :=
    {expression}

end DittertRybin.Certificates.FourRowMinorant
'''
    result={'DR/Certificates/FourRowMinorantData.lean':data}
    for row in range(35):
        result[f'DR/Certificates/FourRowMinorantCheck{row:02}.lean']=f'''import DR.Certificates.FourRowMinorantData

/-! Kernel checks of every (j,k) coefficient with first index {row}. -/
namespace DittertRybin.Certificates.FourRowMinorant
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem compactBernsteinNumerator_row_{row} : ∀ j k : Fin 35,
    0 ≤ compactBernsteinNumerator {row} j k := by decide +kernel

theorem compactBernsteinNumerator_margin_row_{row} : ∀ j k : Fin 35,
    ({row} = (0:Fin 35) ∧ j = 0 ∧ k = 0) ∨
      6323724 ≤ compactBernsteinNumerator {row} j k := by decide +kernel

end DittertRybin.Certificates.FourRowMinorant
'''
    return result

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--check',action='store_true');args=parser.parse_args()
    root=Path(__file__).resolve().parent.parent
    for name,content in render().items():
        p=root/name
        if args.check:
            if not p.exists() or p.read_text()!=content: raise ArithmeticError(f'Changed generated file: {p}')
        elif not p.exists() or p.read_text()!=content: p.write_text(content)
    print('Exact 42,875-coefficient minorant data and 35 kernel row checks reproduce')
if __name__=='__main__': main()
