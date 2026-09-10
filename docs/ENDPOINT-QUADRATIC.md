# Complete quadratic endpoint strip

For an m×n nonnegative matrix P of total mass one, let F_k(P) be the
probability that k independent cell draws have distinct rows or distinct
columns, with inclusive OR. Write U_ij=1/(mn) and (n)_m=n(n−1)…(n−m+1).
At the endpoint k=m, put a=m!/m^m and b=(n)_m/n^m. The sharp statement is
F_m(P)≤a+b−ab, with equality if and only if P=U. A contender means a
probability board satisfying F_m(P)≥F_m(U).

`DittertRybin.uniform_maximum_quadratic_endpoint_strip` proves that uniformity
uniquely maximizes the inclusive-OR semimatching probability at K=m for
every m>=96 and N>=10000m^2, in both orientations. The domain is every
nonnegative real probability matrix, including zero entries and arbitrary
marginals. The exact sharp value and iff equality are supplied by
`UniformMaximizer`.

The [global saturated gauge](ENDPOINT-SATURATED-GAUGE.md) gives
`g>=a*x/[1000(1+x)]`, where `x=m^2 sum_i(r_i-1/m)^2` and
`g=G^2-(1-a)`. Here B=(m−2)(m+1)/2 is the collision-remainder coefficient. The actual [contender concentration](ENDPOINT-LONG-COLUMN-CONCENTRATION.md)
gives `cmax<25/N` and `x/(1+x)<503b/N`. Since `B<m^2/2` and
N>=10000m^2, the last ratio is below 1/32; elementary algebra yields
`x<1/16`. This is a direct scalar strengthening within these sufficient constants, not a change in the stated theorem range.

The [retained-kernel closure](ENDPOINT-LONG-COLUMN-CLOSURE.md) applies these
two actual contender caps after every deletion of two columns. The
collision-cluster estimate and exact elementary coefficient give strict
positive definiteness of the actual averaging kernel. Strict column
averaging forces identical columns at every compact global maximizer;
the product-matrix equality case then forces uniform rows. The proof
therefore includes the sharp bound and unique equality on the full closed
simplex, with no stationarity or positive-support premise on the input.

The gauge minimum and the probability maximum are different optimization
problems. The first proves a global inequality used to concentrate contenders
for the second. The [quartic](ENDPOINT-QUARTIC.md),
[combined](ENDPOINT-COMBINED.md), and [all-aspect](ENDPOINT-ALL-ASPECTS.md)
results apply related estimates with their stated dimension conditions.

## Formal statements

[Quadratic](../DR/Endpoint/Quadratic.lean).
