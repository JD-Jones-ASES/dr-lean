# Elementary coefficient lower bound for endpoint kernels

[ElementaryLowerBound](../DR/Endpoint/ElementaryLowerBound.lean) proves

```
(h/2)^k ≤ k! * elementarySymmetric x k
```

for any finite nonnegative real vector x of positive total mass h, when
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

It uses the previously proved factorial successor bound
`dittertConstant(m+1) ≤ dittertConstant(m)/2` and exact arithmetic at m=16.
This is a dimension induction. The accepted endpoint source is Analytic-Lab
P0174 `ENDPOINT_LLL_STRIP.md`, section 4. These ingredients still require
actual deleted-board normalization and parameter hypotheses before they can
supply the endpoint kernel's coefficient bound.

[Persistent tests](../Test/ElementaryLowerBound.lean) include eight examples:
a signed injection sum, the ordering factorial and its rejected omission,
nonunit mass with a zero coordinate, k=0 on the empty host, failure without
the cap, the exact factorial base, and a rejected extension to m=14.
The targeted build passed 3,154 jobs with seven standard-only axiom audits
and no warnings. No principal endpoint range is claimed by these lemmas alone.
