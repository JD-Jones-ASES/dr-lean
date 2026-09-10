# Actual leading-gauge stationarity and compactness

`LeadingStationarity`, `LeadingMoments`, `LeadingRatioBounds`, and
`LeadingBoundary` under `DR/Endpoint/` supply the actual-matrix input for
the penalized gauge argument in P0174 `ENDPOINT_LEADING_GLOBAL.md` and
`ENDPOINT_SATURATED_STABILITY.md`.

For fixed normalized independent row law X and positive mass-one row
vector r, define actual column costs h_j, c_j=sum_i r_i X_ij, z_j=c_j/h_j,
G=sum_j h_j, D=(gamma/2)sum_j T_j/h_j, and A_i=sum_j X_ij z_j. Empty
columns have cost identically zero along every real row scaling; they
are treated separately from the positive-square-root derivative.

The exact weighted moments are

```
sum_j h_j z_j = 1,
sum_j h_j z_j² = G + 2D,
sum_i r_i A_i = G + 2D.
```

Finite weighted Cauchy gives `1 <= G(G+2D)`. The cost bounds yield
`1 <= A_i <= 1/sqrt(1-beta)`, including empty columns, as well as
`D >= 0` and `0 < G <= 1`.

At a genuine minimum of `G - psi(sum r_i²)` on the feasible row-mass
simplex, positive rows make every sum-zero line locally feasible. For
`psi'(sum r_i²)=tau`, the exact line derivative, pair directions, and
weighted normalization prove

```
A_i = G - (m-2)D + 2tau(r_i - sum_a r_a²) + D/r_i.
```

No Lagrange equation is a premise. The construction uses no derivative
condition at a zero cell and no assumed optimizer shape.

The separate full-board predicate `IsEndpointGaugeMinimum` retains the
entire closed probability simplex. Continuity and compactness prove that
such a minimum exists for every continuous row penalty. A zero row forces
all actual column costs to equal their column masses, so its gauge equals
one. An actual strict bound `G < 1` therefore gives positive rows. The
full-board minimum then restricts to the fixed **original** normalized
row law, and its stationarity theorem is exported directly. No deleted
law is substituted in this argument.

The upper-strip theorem is still pending: the minimum must next be
compared with uniform and the scalar row-spread criterion, then combined
with the product/norm gap and actual contender concentration estimates.

Verification: `lake --wfail build Test.EndpointLeadingBoundary
Test.EndpointLeadingStationarity` passed 2,533 jobs, 12 examples and
23 standard-only axiom audits without warnings. Tests include equality in
the single-column weighted Cauchy bound, a proved nonstationary positive
board that cannot be a gauge minimum, nonlinear penalties, zero rows and
columns, and a boundary row whose normalized row sum is exactly zero.
