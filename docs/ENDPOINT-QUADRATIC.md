# Complete quadratic endpoint strip

`DittertRybin.uniform_maximum_quadratic_endpoint_strip` proves that uniformity
uniquely maximizes the inclusive-OR semimatching probability at K=m for
every m>=96 and N>=10000m^2, in both orientations. The domain is every
nonnegative real probability matrix, including zero entries and arbitrary
marginals. The exact sharp value and iff equality are supplied by
`UniformMaximizer`.

The [global saturated gauge](ENDPOINT-SATURATED-GAUGE.md) gives
`g>=a*x/[1000(1+x)]`, where `x=m^2 sum_i(r_i-1/m)^2` and
`g=G^2-(1-a)`. The actual [contender concentration](ENDPOINT-LONG-COLUMN-CONCENTRATION.md)
gives `cmax<25/N` and `x/(1+x)<503b/N`. Since `b<m^2/2` and
N>=10000m^2, the last ratio is below 1/32; elementary algebra yields
`x<1/16`. This is a direct scalar strengthening within the accepted proof's
sufficient constants, not a change in the advertised theorem range.

The [retained-kernel closure](ENDPOINT-LONG-COLUMN-CLOSURE.md) applies these
two actual contender caps after every deletion of two columns. The
collision-cluster estimate and exact elementary coefficient give strict
positive definiteness of the actual averaging kernel. Strict column
averaging forces identical columns at every compact global maximizer;
the product-matrix equality case then forces uniform rows. The proof
therefore includes the sharp bound and unique equality on the full closed
simplex, with no stationarity or positive-support premise on the input.

The source is the accepted P0174 `ENDPOINT_COLLISION_CLUSTER_STRIPS.md`,
using its separate `ENDPOINT_SATURATED_STABILITY.md` input. The formal
dependency graph separates the gauge minimum from the probability maximum.
The independently assembled [quartic](ENDPOINT-QUARTIC.md),
[combined](ENDPOINT-COMBINED.md) and [all-aspect](ENDPOINT-ALL-ASPECTS.md)
endpoint families are also complete, each with its own exact range.

`lake --wfail build Test.Quadratic Test.LongColumnVariance` passed 3,337
jobs, 23 persistent examples and 14 standard-only axiom audits. Controls
cover the exact first dimension and column cutoff, transpose, explicit
closed-simplex bound and iff equality, finite factorial guards, a nonzero
variance scalar example, and failure after dropping the column cutoff.
The permitted axioms are `propext`, `Classical.choice` and `Quot.sound`.
