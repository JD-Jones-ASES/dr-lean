# Two-zero permanent: all-dimension scalar tail

Mathematical source: Lab P0174 `TWO_ZERO_PERMANENT_GAP.md`, equations (10)--(12).
SHA256 `23c9a917c22e476e0f2dfc54a48ad01860fedaaa615c65526355270907a2df0e`.
This extends the frozen scalar bridge in `TWO_ZERO_POLYNOMIAL_SOURCE.md`.
No source implementation or certificate code is imported.

`TwoZeroLogBounds` proves the three logarithmic truncation inequalities by
exact derivative identities and monotonicity, including equality at zero and
explicit denominator guards. `TwoZeroLogAlgebra` proves the exact source
rational identity and the required caps on its logarithm arguments.

For the degree-16 polynomial E, this proof replaces the source Bernstein
certificate with a simpler direct estimate on `0 <= q <= 1/25`:

```
E(q) >= 3 - 71q - 46q^3 - 14568q^5
     >= 1519182/9765625 > 0.
```

The first inequality groups every negative term of degree at least five using
`q^k <= q^5` and discards only nonnegative terms. The exact polynomial and
normalization are unchanged; the source endpoint value is tested exactly.

`TwoZeroLogTail` derives a strict logarithmic margin, proves the exact
normalization by `boundaryPermanentFloor (m+2)`, and exports:

```
twoZeroReducedPermanent_tail_gap
  (hm : 25 <= m) (ha : 0 <= a) (hb : 0 <= b)
  (haM : a <= 1/m) (hbM : b <= 1/m) :
  boundaryPermanentFloor (m+2)*(1+1/(4*m^2))
    < twoZeroReducedPermanent m a b
```

This remains a scalar theorem. Actual two-zero matrix-face reduction,
representative existence, and permanent counting are separate obligations.
Extra zeros are not excluded by the scalar parameter bounds.

Replay: `lake build Test.TwoZeroLogTail`, PASS 3450 jobs, 12 examples, ten
standard-only axiom audits, no warnings. Controls include zero logarithm
arguments after normalization, both signs of the expansions, exact endpoint
value, failure at q=1/20, failure at a denominator pole, the m=25 junction,
the m=4 ratio counterexample, the boundary-floor versus gamma distinction,
and both zero exceptional diagonal entries. No broad root replay was run.
