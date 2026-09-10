# Consecutive endpoints from exact active cuts

For an m×n nonnegative matrix P of total mass one, let F_k(P) be the
probability that k independent cell draws have distinct rows or distinct
columns, with inclusive OR. Write U_ij=1/(mn) and (n)_m=n(n−1)…(n−m+1).
At the endpoint k=m, put a=m!/m^m and b=(n)_m/n^m. The sharp statement is
F_m(P)≤a+b−ab, with equality if and only if P=U. A contender means a
probability board satisfying F_m(P)≥F_m(U).

The principal declaration `uniform_maximum_consecutive_endpoint` in
`DR/Endpoint/Consecutive.lean` proves `UniformMaximizer m (m+1) m`
and its transpose for every integer `m >= 19`. The domain is the full
nonnegative probability simplex, and equality holds exactly at the uniform
board. Individual zero entries and a zero rook deficit are included.
General P2 is not asserted.

The minimum-dilation method follows Cheon and Wanless (2012),
[Some results towards the Dittert conjecture on permanents](https://users.monash.edu.au/~iwanless/papers/DittertIndecompLAA.pdf),
Lemma 2.3; their Lemma 2.2 credits the domination criterion to C.-K. Li.
Finite balanced transport constructs the dilation. Its permanent lower
bounds are proved by polynomial capacity, including the prescribed
zero-rectangle degree improvement.

For n=m+1 and a=gamma_m, b=(n)_m/n^m, a contender has a shared rook deficit
delta=b-T(P), with 0<=delta<=b. The size-sensitive marginal
modules establish the row cap H=101/100, the subset bounds

    A_k = 2 H^2 k(m-k)/m^3,
    B_l = 2(n-1) l(n-l)/(n^2 m),
    p = k/m+l/n-1,
    C = [A_k+(a/b) B_l]/p^2.

The finite gates prove C b/(1-b)<1/500 for every positive non-whole cut.
This establishes actual positive cut mass before selecting the minimum
dilation q. The resulting balanced B satisfies qB<=P, has an active cut of
mass qp, and has a zero complementary rectangle. Because q>0, every
original zero also survives in B.

The padding bridge proves the exact rook floor

    beta = b * max(mu_n, gamma_(n-m+k) gamma_l/gamma_(k+l-m)) / gamma_n

for mixed cuts; axis cuts use mu_n alone. Here mu_n is the proved one-zero
permanent floor. The zero rectangle is transferred to the actual padded
matrix, with no averaging in a fixed-dummy slice.

When q=1, probability domination forces P=B and the one-zero floor exceeds
the uniform rook value. When q<1, t=1-q satisfies

    t^2 <= C delta/(1-b),
    b-delta >= (1-t)^m beta.

The second finite certificate,

    beta-b-m^2 C beta^2/[4(1-b)] > b/2000,

then gives a contradiction by Bernoulli and an exact completion of the
square. Thus no boundary contender exists. The compactness and
maximum-norm argument in `PositiveMaximizers.lean` converts positivity of
every global maximizer into the full sharp inequality and iff equality.
Finally, the separate factorial recurrence in `ConsecutiveLarge.lean`
covers all m>=30, so the finite range is not extrapolated.

## Exact checks

`ConsecutiveCutRational.lean` defines every quantity by rational formulas.
The eleven `ConsecutiveCutGate19` through `ConsecutiveCutGate29` modules
use `decide +kernel` over every pair in `Fin (m+1) × Fin (m+2)`.
`ConsecutiveCutChecks.lean` assembles this literal range and verifies the
eleven row-cap inequalities. The count of positive non-whole pairs is
3,608. Each comparison uses the formula-defined rational quantities
and covers every positive non-whole cut in the stated finite range.

## Formal statements

[Consecutive](../DR/Endpoint/Consecutive.lean), [MinimumDilation](../DR/Endpoint/MinimumDilation.lean), [BoundaryPermanent](../DR/Endpoint/BoundaryPermanent.lean), [PositiveMaximizers](../DR/Endpoint/PositiveMaximizers.lean), [ConsecutiveLarge](../DR/Endpoint/ConsecutiveLarge.lean), [ConsecutiveCutCertificates](../DR/Endpoint/ConsecutiveCutCertificates.lean).
