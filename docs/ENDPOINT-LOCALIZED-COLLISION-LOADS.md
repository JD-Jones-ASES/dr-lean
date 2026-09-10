# Localized exact collision-pattern loads

Under independent nonnegative normalized row laws X, suppose each
incident collision load d_i is at most 1/8, let D be the total unordered
intensity, and suppose every column sum of X is at most cap. Then

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

## Formal statements

[RowPairMoments](../DR/Endpoint/RowPairMoments.lean), [RowCollisionLocalized](../DR/Endpoint/RowCollisionLocalized.lean).
