# Global saturated leading-gauge stability

Let B(r) have diagonal entries one and off-diagonal entries
1−(m−2)!∏_{a∉{i,j}}r_a. For column vectors v_j, define
G(P)=∑_j√(v_jᵀB(r)v_j). For every probability board with `m≥96`,
this leading gauge satisfies

```
G(P) ≥ sqrt(1−a) + (a/1000) x/(1+x),
G(P)^2 − (1−a) ≥ (a/1000) x/(1+x),
a = m!/m^m,   x = m^2 sum_i (rowSum(P)_i−1/m)^2.
```

There is no column-count cutoff, support assumption, stationarity premise,
or positive-kernel premise in these two global conclusions. The zero-column
dimension has no probability board; individual zero columns and zero rows
remain part of the domain.

`LeadingProductGap` sums the proved logarithmic estimate on `0<y≤2` to
obtain `product(y)≤exp(−sum(y−1)^2/8)`. Its scalar square-root gap is
`a*x/[16(1+x)]`, valid for all `x≥0`, including zero. The norm comparison
from `LeadingNorm` transfers this to an actual board once its original
kernel is positive semidefinite and its rows lie below twice uniform.

`LeadingSaturatedMinimum` minimizes the actual gauge minus the saturated
penalty on the full closed probability simplex. The raw rational penalty
has a pole outside the attainable row-square domain. Continuity is proved
on the actual simplex, where its denominator is positive. At a true
minimum, comparison with uniform gives gauge less than one, hence every
row is positive. The proved moment and feasible row-scaling
identities supply every premise of `saturated_stationary_kernel`.
That theorem, proved in the stationary analysis, derives
positive definiteness and the twice-uniform row cap for `m≥96`.

At the selected minimum, the stronger norm gap dominates the saturated
penalty. Compact comparison transfers this lower value to every probability
board, proving both displayed inequalities. The
[contender comparison](ENDPOINT-LEADING-COMPARISON.md) converts this
gauge stability into the concentration needed by the
[quadratic endpoint theorem](ENDPOINT-QUADRATIC.md).

## Formal statements

[LeadingProductGap](../DR/Endpoint/LeadingProductGap.lean), [LeadingSaturatedMinimum](../DR/Endpoint/LeadingSaturatedMinimum.lean), [LeadingSaturated](../DR/Endpoint/LeadingSaturated.lean).
