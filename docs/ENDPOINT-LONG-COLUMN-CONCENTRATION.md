# Actual long-column contender concentration

The leading costs are `alpha_j = endpointLeadingColumnCost P j`, with
`G=sum alpha_j`. Their variance is centered at `G/N`, because their total
need not equal one. For every probability board with m>=5, the proved cost
bounds give `(1-rho)c_j<=alpha_j<=c_j`, where
`rho=1-sqrt(1-endpointLeadingDefect m)`, `0<=rho<1/8` and `rho<=5a`.
This uses the available sharper defect; it implies the bounds required by
the accepted P0174 polynomial-strip argument.

`LongColumnVariance` centers `c=alpha+(c-alpha)` and proves
`Vc<=3 Valpha+3 rho^2/N` and `c_j^2<=4/N^2+4 Valpha` for actual column
costs. Zero columns are allowed. The cost vector is never normalized to mass
one. Its generic centered-square identity also supplies the actual
[probability comparison](ENDPOINT-LEADING-COMPARISON.md).

`LongColumnParameters` proves `128 m^3 a<=1` and `a<1/625000` for every
m>=16 by an exact rational base and factorial half-decay. Closed-simplex
Maclaurin then gives the actual contender cap `c_j<1/(3m^2)` whenever
N>=6m^2. For `b=(m-2)(m+1)/2`, this implies `b c_j<1/6`. The same scalar
module proves `ab<1` and `b rho^2<1`.

`LongColumnAbsorption` combines the retained-uniform comparison
`g+N Valpha<=N b cmax Vc+ab/(2N)` with variance conversion. It yields

```
g+(N/2) Valpha <= ab/(2N)+3b rho^2 cmax.
```

For a nonnegative gauge gap, the pointwise squared bound gives
`y^2<8+24y`, where `y=N cmax`; hence `cmax<25/N`. Substitution gives
`g<=a(b/2+1875ab)/N`.

`LongColumnConcentration` chooses an attained column maximum and applies
the independently proved actual event comparison to it. Its theorem
assumes only the actual contender and a nonnegative gauge gap, with
m>=16 and N>=6m^2. Either the linear or saturated gauge modulus then gives
the same normalized bound `<503b/N`. No global endpoint theorem is used
to obtain these concentration estimates.

These are the variance and bootstrap arguments of P0174
`ENDPOINT_POLYNOMIAL_STRIPS.md` and `ENDPOINT_COLLISION_CLUSTER_STRIPS.md`.
They combine with the separate [quadratic proof](ENDPOINT-QUADRATIC.md).
Persistent controls include non-unit cost mass, the difference between
centering at cost mean and at uniformity, zero columns, empty vectors,
rejected missing cost bounds, actual boundary probability inputs, and the
strict quadratic margin at the proposed column cap.
