# Elementary coefficient lower bound for endpoint kernels

[ElementaryLowerBound](../DR/Endpoint/ElementaryLowerBound.lean) proves

```
(h/2)^k ≤ k! * elementarySymmetric x k
```

where e_k(x)=elementarySymmetric x k is the sum of the products over
k-element subsets. The inequality holds for any finite nonnegative real
vector x of positive total mass h, when
all coordinates are at most c and `k*c ≤ h/2`. The vector need not have
mass one. Zero coordinates and k=0 are included; the proof does not assume
k is at most the ambient dimension or take an avoidance estimate as input.
The cap is automatically nonnegative under the stated assumptions.

The proof removes the first label from an injection to obtain its tail and
a label outside the tail's range. This is an explicit bijection, including
empty domains. Consequently, for the ordered injection sum A_k, the exact
signed recurrence is

```
A_(k+1) = sum_e product_i x(e_i) * (h - sum_i x(e_i)).
```

Under nonnegativity the product weights are nonnegative. Each prefix of at
most k labels uses at most k*c mass, so each extension has at least h/2
available. Induction gives the lower bound for A_k. The proved counting
identity `A_k=k!*elementarySymmetric x k` supplies the exact factorial.

[FactorialScale](../DR/Endpoint/FactorialScale.lean) separately proves

```
2^(m-2) * dittertConstant m < 1/32   for every m≥16.
```

The factorial estimate follows by induction from
`dittertConstant(m+1) ≤ dittertConstant(m)/2` and exact arithmetic at m=16.
Applied at k=m−2, the elementary bound and this decay prove the
[coefficient ratio](ENDPOINT-COEFFICIENT-RATIO.md) for a retained board
with the stated positive mass and coordinate cap.

## Formal statements

[ElementaryLowerBound](../DR/Endpoint/ElementaryLowerBound.lean), [FactorialScale](../DR/Endpoint/FactorialScale.lean).
