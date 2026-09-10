# Consecutive endpoints from exact active cuts

The principal declaration `uniform_maximum_consecutive_endpoint` in
`DR/Endpoint/Consecutive.lean` proves `UniformMaximizer m (m+1) m`
and its transpose for every integer `m >= 19`. The domain is the full
nonnegative probability simplex, and equality holds exactly at the uniform
board. Individual zero entries and a zero rook deficit are included.
General P2 is not asserted.

The finite part follows Section I of Analytic-Lab's P0174 note
`ACTIVE_CUT_RECTANGULAR_EXTENSIONS.md`, SHA-256
`4ae2b41d7b6e1969c180501bc336cb567f12fe787ff853bcf465f1d37f32e28e`.
That note credits the minimum-dilation argument to Cheon–Wanless (2012),
Lemma 2.3, and the balanced domination criterion there to C.-K. Li.
This implementation uses the proved finite transport theorem and actual
minimum in `MinimumDilation.lean`. The permanent inputs are proved in
`BoundaryPermanent.lean` and `Square/ZeroRectangle.lean`; the latter uses
capacity and degree bounds. No cited face-minimizer or permanent-floor claim
is introduced as an assumption.

For n=m+1 and a=gamma_m, b=(n)_m/n^m, a contender has a shared rook deficit
delta=b-T(P), with 0<=delta<=b. The frozen generic size-sensitive marginal
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
square. Thus no boundary contender exists. The frozen compactness and
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
3,608, independently checked by a persistent Lean example. No generated
certificate table, Python runtime, floating-point approximation, or
external arithmetic oracle is required by the proof.

Each gate was first built in bounded batches of at most two. A normal
cached replay is:

    lake build Test.ConsecutiveCutCertificates Test.Consecutive

The tests cover finite dimensions 19 and 29, the recurrence join at 30,
dimension 1000, both orientations, actual zero-cell strictness, a zero
deficit, empty and whole cuts, and a rectangle floor exceeding the one-zero
floor. Negative controls reject the finite scalar certificate at m=18 and
the stronger b/1000 margin at the last axis cut. The former is a failure of
this certificate, not a counterexample to P2.

Twelve stored axiom audits cover the finite arithmetic/real bridges,
actual rectangle floor, square-completion argument, actual positive cuts,
active-cut loss, boundary exclusion and full principal theorem. They use
only `propext`, `Classical.choice`, and `Quot.sound`.
