# Uniform avoidance bound on the accepted endpoint strip

`DR/Endpoint/UniformAvoidanceBound.lean` formalizes equation (2) of the
Lab's `ENDPOINT_LLL_STRIP.md`. The literal distinct-column probability is
first identified with the finite product of `1-i/n`, retaining zero
sample order. Each nonnegative factor is bounded by `exp(-i/n)` and the
exact arithmetic-progression sum gives

```
b <= exp(-m*(m-1)/(2*n)).
```

Under `2<=m`, `m<=n`, and `20*n<=m*(m-1)`, this is strictly below
`1/16384`. The numerical step uses Mathlib's proved exponential lower
bound and exact rational arithmetic: `exp(1)>8/3` and
`(3/8)^10<1/16384`. No floating-point or asymptotic estimate is used.

Replay: `lake build Test.UniformAvoidanceBound`. Persistent checks retain
zero and one samples, an exact two-draw probability, the necessity of
the collision exponent's factor one half, the accepted nonempty strip
instance `m=2^22,n=2^39`, and failure when the upper-edge assumption is
removed. This supplies the uniform probability input for actual contender
row concentration; it does not by itself prove an endpoint maximizer range.
