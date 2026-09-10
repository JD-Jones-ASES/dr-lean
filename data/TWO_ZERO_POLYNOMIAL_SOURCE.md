# Two-zero permanent: scalar equalization and bracket bridge

Mathematical source: Analytic-Lab P0174 `TWO_ZERO_PERMANENT_GAP.md`,
equations (3)--(9). Source SHA256:
`23c9a917c22e476e0f2dfc54a48ad01860fedaaa615c65526355270907a2df0e`.
The five finite rational brackets retain the separate pinned source in
`NEAR_ENDPOINT_FINITE_CUTS_SOURCE.md`; no new literal certificate was introduced.

This increment proves the scalar statements directly in Lean. It imports no
Lab implementation or peer code. The source's published face-reduction
attribution (Pula--Song--Wanless, 2011, invoking Minc's averaging theorem)
is not used as a premise or formal axiom here. Actual matrix minimization,
repeated-support averaging, and the permanent expansion of a representative
matrix are separate obligations.

## Proved scope

`twoZeroReducedPermanent m a b` is the explicit signed two-parameter formula.
For every natural `m >= 4` and the full closed rectangle `0 <= a,b <= 1/m`:

- replacing `a,b` by their mean lowers this formula, strictly when `a != b`;
- its equalized form is `m! x(u)^(m-2) h(u)`, with `u = 1-m(a+b)/2` in `[0,1]`;
- the derivative has exactly the sign of the source cubic, which is strictly
  increasing on the entire real line;
- `h` decreases on `[0,1/m]`;
- any bracket `0 <= ell <= r <= 1/m` satisfying `f(ell) <= 0 <= f(r)` gives
  the lower bound `m! x(ell)^(m-2) h(r)` on the entire parameter rectangle;
- the strict coarse bracket `ell=1/m-2/m^3`, `r=1/m` works for every `m >= 4`.

The proof of the bracket bound uses interval monotonicity outside the bracket
and separate monotonicity of its factors inside the bracket. It does not need
an assumed minimizer or a numerical root. The lower-point cubic sign is proved
by an exact positive-coefficient expansion in `m-4`.

`nearEndpoint_twoZeroReducedPermanent_finite_lt` transfers the five already
kernel-checked rational brackets to a strict real scalar lower bound for
`n=21,...,25`, `m=n-1`. This still makes no arbitrary-matrix permanent claim.
The infinite-tail logarithmic estimate after source equation (9) is not part
of this increment.

## Replay and persistent controls

```
lake build Test.TwoZeroPolynomial Test.NearEndpointTwoZeroPolynomial
```

Both tests pass with 3509 jobs, 18 examples, and 12 axiom reports containing
only `propext`, `Classical.choice`, and `Quot.sound`. Controls retain one or two
zero exceptional diagonals, two zero borders, signed infeasible polynomial
identities, the exact `m^4` numerator normalization, both univariate endpoints,
wrong bracket signs, reversed equalization, and a concrete failure after
dropping the parameter bound. No broad project replay was run for this isolated
increment; no root import or frozen module was changed.
