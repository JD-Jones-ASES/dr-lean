# Arithmetic endpoint dimension estimates

For integers m≥128 and m≤n, the cutoff

```
22*n*log(m) <= m*(m-1)
```

implies n<m², b=(n)_m/n^m≤1/m¹¹, and the strict scalar comparison

```
b + (n-1)*a_m < (512/289)/(m^3*n^2*(n-1)^2),
a_m = m!/m^m.
```

[ArithmeticParameters](../DR/Endpoint/ArithmeticParameters.lean) proves
these estimates using the exact uniform avoidance product, its exponential
bound, and the existing factorial decay a_m≤m⁻¹⁴. The constant 512/289 is
exactly twice (16/17)². The argument holds for every integer dimension in
the stated domain; it does not extrapolate a finite scan.

Substitute these inequalities into the common-divisor criterion with g=1
in [boundary scaling](ENDPOINT-BOUNDARY-SCALING.md). This proves the
arithmetic endpoint theorem: uniform is the unique maximizer for m≥128,
m≤n≤m(m−1)/(22 log m), in both orientations.

## Formal statements

[Arithmetic](../DR/Endpoint/Arithmetic.lean), [ArithmeticParameters](../DR/Endpoint/ArithmeticParameters.lean).
