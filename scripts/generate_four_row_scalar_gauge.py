#!/usr/bin/env python3
"""Reproduce the degree-seven four-row scalar certificate from its literal formula.

Source: Analytic-Lab P0174 K4_LEADING_FOUR_ROWS.md, equations (5) and (5a).
SymPy derives rational data; Lean proves the displayed identity and nonnegativity.
Run with --check to compare the deterministic generated file without editing it.
"""
from pathlib import Path
import argparse
import sympy as s


def render():
    r = s.symbols('r0:4')
    a, b, c, d = s.symbols('a b c d')
    S = sum(r)
    g = [sum(r[j]**2*r[k] for j in range(4) for k in range(4)
             if j != k and i not in (j, k)) for i in range(4)]
    H = 2*s.Rational(3,32)*S**7-2*S**3*sum(r[i]*g[i] for i in range(4))-sum(
        r[i]*(g[i]-s.Rational(3,32)*S**3)**2 for i in range(4))
    V = sum((x-S/4)**2 for x in r)
    ordered = (d,c+d,b+c+d,a+b+c+d)
    substitution = dict(zip(r,ordered))
    H_order = s.Poly(s.expand(H.subs(substitution)),a,b,c,d)
    if len(H_order.terms()) != 116 or min(H_order.coeffs()) != s.Rational(183,1024):
        raise ArithmeticError('Literal target coefficient inventory changed')
    remainder = s.Poly(s.expand(1024*(H-s.Rational(61,256)*V*S**5).subs(substitution)),a,b,c,d)
    if not all(coef.is_Integer and coef > 0 for coef in remainder.coeffs()):
        raise ArithmeticError('Nonpositive or inexact residual coefficient')
    if remainder.total_degree() != 7:
        raise ArithmeticError('Degree changed')
    def monomial(exponents,coef):
        factors=[f"({coef} : ℝ)"]
        factors.extend(str(x) if power==1 else f'{x}^{power}'
                       for x,power in zip((a,b,c,d),exponents) if power)
        return '*'.join(factors)
    def balanced(terms):
        if len(terms)==1:return '('+terms[0]+')'
        cut=len(terms)//2
        return '('+balanced(terms[:cut])+' +\n    '+balanced(terms[cut:])+')'
    expression=balanced([monomial(e,v) for e,v in remainder.terms()])
    return f'''import DR.Rectangular.FourRowScalarGaugePolynomial

/-! Generated exact sorted-gap certificate. Reproduce with
`scripts/generate_four_row_scalar_gauge.py --check`.
The literal target has 116 positive coefficients. Its quantitative residual
below has {len(remainder.terms())} positive integer coefficients after multiplication by 1024. -/

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace DittertRybin
open scoped BigOperators

noncomputable def fourRowScalarGaugeResidual (a b c d : ℝ) : ℝ :=
    {expression}

theorem fourRowScalarGaugeResidual_nonneg {{a b c d : ℝ}}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    0 ≤ fourRowScalarGaugeResidual a b c d := by
  unfold fourRowScalarGaugeResidual
  positivity

/-- The finite identity is proved by ordinary ring normalization of the literal source. -/
theorem fourRowScalarGaugeResidual_identity (a b c d : ℝ) :
    1024*(fourRowGaugeHomogeneous ![d,c+d,b+c+d,a+b+c+d] -
      (61/256)*fourRowGaugeHomogeneousVariance ![d,c+d,b+c+d,a+b+c+d]*
        (a+2*b+3*c+4*d)^5) = fourRowScalarGaugeResidual a b c d := by
  simp only [fourRowGaugeHomogeneous, fourRowGaugeHomogeneousVariance]
  simp_rw [fourRowGaugeCollision_moments]
  norm_num [Fin.sum_univ_succ, fourRowScalarGaugeResidual]
  ring

end DittertRybin
'''


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    target=Path(__file__).resolve().parent.parent/'DR/Certificates/FourRowScalarGaugeData.lean'
    content=render()
    if args.check:
        if not target.is_file() or target.read_text()!=content:
            raise ArithmeticError('Generated four-row scalar certificate differs')
        print('Four-row scalar certificate reproduces exactly')
    elif not target.is_file() or target.read_text()!=content:
        target.write_text(content)
        print('Wrote',target)


if __name__=='__main__':
    main()
