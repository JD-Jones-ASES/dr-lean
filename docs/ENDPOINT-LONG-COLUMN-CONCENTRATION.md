# Actual long-column contender concentration

For a probability board with m≥5, write a=m!/m^m,
alpha_j=√(v_jᵀB(r)v_j) and G=∑alpha_j. Here B(r) is the
[leading kernel](ENDPOINT-LEADING-FOUNDATION.md) and v_j is column j.
Its cost bounds give (1−rho)c_j≤alpha_j≤c_j, where
rho=1−√(1−endpointLeadingDefect(m)), 0≤rho<1/8, and rho≤5a.
The cost variance is centered at G/N because the costs need not sum to one.

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

Combining these estimates with saturated gauge stability gives the
[quadratic strip](ENDPOINT-QUADRATIC.md); the linear gauge modulus
gives the [quartic strip](ENDPOINT-QUARTIC.md). Both uses retain the
cost mean G/N and the original marginal mean 1/N as distinct quantities.

## Formal statements

[LongColumnVariance](../DR/Endpoint/LongColumnVariance.lean), [LongColumnParameters](../DR/Endpoint/LongColumnParameters.lean), [LongColumnAbsorption](../DR/Endpoint/LongColumnAbsorption.lean), [LongColumnConcentration](../DR/Endpoint/LongColumnConcentration.lean).
