# Global saturated leading-gauge stability

For every probability board with `m≥96`, the actual leading gauge satisfies

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
row is positive. The previously proved moment and feasible row-scaling
identities supply every premise of `saturated_stationary_kernel`.
That theorem, independently supplied in the root scalar package, derives
positive definiteness and the twice-uniform row cap for `m≥96`.

`LeadingSaturated` applies the stronger norm gap at that minimum; it
dominates the chosen penalty. Compact comparison then proves the two
global inequalities above. This is the accepted P0174
`ENDPOINT_SATURATED_STABILITY.md` argument, with all analytic and finite
matrix inputs proved. The separate event comparison and contender
concentration needed for the long-column P2 theorem remain downstream.

`lake --wfail build Test.EndpointLeadingSaturated` passed 3,274 jobs,
fifteen examples and ten standard-only axiom audits. Controls include the
closed coordinate cap, empty products, failure of the uncapped logarithm
bound, zero variance, failure after removing the saturated denominator,
the unattainable penalty pole, a true compact minimum, arbitrary probability
boards, and a zero-row boundary. Warnings are rejected.
