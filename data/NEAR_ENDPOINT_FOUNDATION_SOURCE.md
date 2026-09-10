# Near-endpoint sampling, padding and transport

For n−1 independent sampled cells on an n×n signed matrix, the normalized
identity is F=a(R+S−T), where a=(n)ₙ₋₁/nⁿ⁻¹. For probability contenders
with n≥3, the nonnegative marginal deficits satisfy dᵣ+d𝒸≤δ=a−T≤a.
Under the stated scalar guards, marginal estimates and all transport cuts
construct balanced B with (1−t)B≤P and t²=(4/3)n²δ.
These are identities and estimates for the actual sampling law in
[NearEndpointNormalization](../DR/Endpoint/NearEndpointNormalization.lean)
and [NearEndpointMarginals](../DR/Endpoint/NearEndpointMarginals.lean).

The [padding](../DR/Endpoint/NearEndpointPadding.lean) adds a first row and
column, with corner zero, border entries 1/n, and core (n−1)B. Balanced input
produces a doubly stochastic square. Any zero of B becomes a second zero in
a different row and column. The exact signed permanent identity has factor
(n−1)ⁿ⁻¹/n² times the rook sum, with no extra sampling factorial.
Equivalently per(D)=μₙ₊₁ T/a, using the one-zero boundary floor μ;
uniform input gives per(D)=μₙ₊₁.

[NearEndpointPaddingCounting](../DR/Endpoint/NearEndpointPaddingCounting.lean)
proves the omitted-index/increasing-embedding bijection, the sum of permanent
minors, and the corner-border expansion. The counting identities retain a
one-cell core, zero scale, and empty minor. Positive dimension is explicit
where division by n is used.

The [full theorem](../DR/Endpoint/SquareNearEndpoint.lean) combines these facts
with the actual two-zero permanent gap and the finite/analytic cut estimates.

```sh
lake --wfail build Test.NearEndpointFoundation
```

Tests retain signed border factors, reject an extra factorial, distinguish
μ₄=8/81 from γ₄=3/32, and exhibit nonuniform equality for n=2, K=1.
