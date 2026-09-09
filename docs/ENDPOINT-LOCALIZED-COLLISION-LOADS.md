# Localized exact collision-pattern loads

[RowPairMoments](../DR/Endpoint/RowPairMoments.lean) and
[RowCollisionLocalized](../DR/Endpoint/RowCollisionLocalized.lean) prove
equations (6) and (7) in Analytic-Lab P0174
`ENDPOINT_RELATIVE_COLLISIONS.md`. With actual nonnegative normalized row
laws, local collision loads `d_i <= 1/8`, total unordered intensity `D`,
and a column-sum cap `cap`, the results are

```
localizedDoubleton_i <= (16/9)*d_i,
localizedDeficitTwo_i <= d_i*((32/27)*cap+(256/81)*D),
localizedDeficitTwo_i <= cap^2*((32/27)+(128/81)*m).
```

Every load is a sum of literal exact-pattern probabilities divided by
actual `rowAvoidance X`. This denominator is positive under the stated
hypotheses. Tripletons involving row `i` are indexed by an increasing pair
outside `i`. In two-doubleton terms, the first pair contains `i` and the
second is disjoint and increasing. These conventions avoid reversed
orientations and duplicate pattern counts.

The tripleton moment bound comes from the exact identity

```
2*sum_(a<b) y_a*y_b = (sum_a y_a)^2-sum_a y_a^2.
```

This identity permits signed coordinates. Applying it after setting the
specified row coordinate to zero preserves the factor `1/2` in the
restricted pair sum. Nonnegative actual row entries then give the moment
bound `sum_triples Pr(equalities) <= cap*d_i/2`. For two doubletons, the
restricted second-pair sum is bounded by `D`. The coarser column-cap form
uses the proved actual bounds `d_i <= cap` and `D <= m*cap/2`.

Verification: `lake build Test.RowCollisionLocalized` passed 3,159 jobs
with nine standard-only axiom audits. Tests check exact unordered counts,
the signed quadratic identity, the non-duplicated factor two, a rational
four-row bound derived directly from a column cap, vanishing actual
localized penalties when all collision loads are zero, and empty row
sets. Source files contain no added axioms, placeholders, or native
decision shortcuts.

The distribution of exact collision patterns is now bounded locally.
Identifying these sums with the deletion matrix's expected incidence
vectors, proving the pointwise deletion-matrix inequality, and completing
its square-completion and endpoint-range inputs remain separate steps.
No endpoint range is widened by this package.
