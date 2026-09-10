# Uniform column avoidance bound

For 0≤m≤n with n>0, the uniform distinct-column probability is
b=(n)_m/n^m=∏_{i=0}^{m−1}(1−i/n). Every factor is nonnegative
and at most exp(−i/n). Multiplying and summing the arithmetic progression
gives

```
b <= exp(-m*(m-1)/(2*n)).
```

Under `2<=m`, `m<=n`, and `20*n<=m*(m-1)`, this is strictly below
`1/16384`. The numerical step uses Mathlib's proved exponential lower
bound and exact rational arithmetic: `exp(1)>8/3` and
`(3/8)^10<1/16384`. No floating-point or asymptotic estimate is used.

## Formal statements

[UniformAvoidanceBound](../DR/Endpoint/UniformAvoidanceBound.lean).
