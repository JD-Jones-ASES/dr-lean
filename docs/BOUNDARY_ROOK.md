# Rectangular boundary rook floor

`DR/Endpoint/BoundaryRook.lean` transfers the proved square one-zero
permanent floor to balanced rectangular boards. Write
`b = distinctUniformProbability n m = (n)_m/n^m` and
`kappa_n = boundaryPermanentFloor n / dittertConstant n`.
For `0 < m ≤ n`, `n ≥ 3`, and a nonnegative `m×n` board `B` whose row
sums are `1/m`, column sums are `1/n`, and which has a zero entry, it proves

```
b * kappa_n ≤ m^m * rookSum B m.
```

The source is the rectangular padding step in the Lab's
`P0174_rybin_semimatchings/PANG_RECTANGULAR_ENDPOINT.md`, combined with
the internally proved one-zero floor documented in
`docs/BOUNDARY_PERMANENT.md`. No boundary minimizer classification is
assumed. The normalized square theorem includes its sharp `n=3` boundary.

## Exact transfer

The actual padding has first rows `m*B` and `n-m` dummy rows equal to
`1/n`. It is doubly stochastic and retains every original zero. The
already proved permanent identity becomes

```
per(padding B) = [(n-m)! / n^(n-m)] * endpointRookRatio B.
```

The same positive coefficient times `b` is exactly `n!/n^n`. The proof
uses the factorial identity `(n-m)! * (n)_m = n!` and the exact exponent
sum `(n-m)+m=n`, so no asymptotic estimate enters the floor transfer.

Endpoint rook monotonicity holds on nonnegative boards, and signed
scalar homogeneity has degree `m`. Consequently, if `(1-t)B ≤ P`
entrywise and `t ≤ 1`, then

```
(1-t)^m * b * kappa_n ≤ endpointRookRatio P.
```

This version retains `t=1`; it neither normalizes `P` nor divides by
`1-t`. A separate convenience theorem assumes `t<1` and a zero in `P`,
and derives the required zero in `B`. The distinction is necessary at
zero scaling. Transport existence and parameter choices remain separate
inputs to later endpoint closure.

## Verification

Run `lake --wfail build Test.BoundaryRook`. Tests cover an actual balanced
`2×3` boundary board, half and zero scaling, signed homogeneity, empty
original rows, square padding, the sharp `3×3` probability normalization,
a rejected stronger floor, and the failure of zero transfer at zero
scaling. Eight public axiom audits expose only the standard Lean axioms.
