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

This is the elementary parameter part of the Lab's
`ENDPOINT_ARITHMETIC_SCALING.md` sufficient criterion without its optional
gcd improvement. Balanced transport, boundary permanent comparison and
the resulting unique-maximizer theorem remain separate obligations.
This lemma alone completes no new principal release target.

Tests include an admitted 256×256 dimension, the logarithm bound at m=128,
and rejected missing-cutoff and small-dimension variants.

```
lake --wfail build +Test.ArithmeticParameters
```
