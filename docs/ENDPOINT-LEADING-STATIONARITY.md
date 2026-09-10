# Actual leading-gauge stationarity and compactness

Minimizing the leading gauge minus a differentiable penalty in the row
squared norm gives exact equations for the row masses. Compactness
provides a minimum on the full probability simplex; the zero-row value
separates the boundary before any coordinate is divided out.

For m≥3, fixed nonnegative normalized independent row law X and positive mass-one row
vector r, put c_j=∑_i r_i X_ij, h_j=√(c_j²−γT_j), and z_j=c_j/h_j,
G=sum_j h_j, D=(gamma/2)sum_j T_j/h_j, and A_i=sum_j X_ij z_j.
Here γ=(m−2)!∏r_i, T_j=(∑_i X_ij)²−∑_i X_ij²,
and β=((m−2)!/(m−2)^(m−2))(1−1/m). In an empty column set
z_j=0 and interpret T_j/h_j as zero. Empty
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

The completed [coarse gauge](ENDPOINT-COARSE-GAUGE.md) compares this minimum
with uniform and the scalar row-spread criterion. The product/norm gap and
actual contender concentration then feed the completed
[quadratic](ENDPOINT-QUADRATIC.md) and [combined](ENDPOINT-COMBINED.md) strips.

## Formal statements

[LeadingStationarity](../DR/Endpoint/LeadingStationarity.lean), [LeadingMoments](../DR/Endpoint/LeadingMoments.lean), [LeadingRatioBounds](../DR/Endpoint/LeadingRatioBounds.lean), [LeadingBoundary](../DR/Endpoint/LeadingBoundary.lean).
