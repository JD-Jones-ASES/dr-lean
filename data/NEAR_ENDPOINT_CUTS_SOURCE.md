# Near-endpoint actual active-cut foundation

Source: P0174 `ACTIVE_CUT_RECTANGULAR_EXTENSIONS.md`, near-endpoint part.
The matrix proof remains generic in every n≥3, not a check on sampled boards.

The normalized elementary deficits give marginal variance≤2d/[n(1−a)].
The exact centered subset-indicator projection gives a factor k(n−k), and
the two deficits share the actual rook-deficit budget. For a positive cut
p=(k+l−n)/n, the squared discrepancy is at most p²*Ckl*δ/(1−a), where
Ckl=2[k(n−k)+l(n−l)]/(k+l−n)². Whole and empty subsets are retained.

Under the two weak scalar guards a≤1/4 and(4/3)n²a<1, the previously
proved actual balanced domination makes every positive cut mass positive.
The finite minimum-dilation theorem then produces q>0, q≤1, balanced B,
qB≤P and a positive active cut whose complementary rectangle in B is zero.
The actual active equality yields(1−q)²≤Cklδ/(1−a), also when δ=0.
The weak guards are proved for all n≥21 by five exact cases followed by
the already proved n≥26 scalar tail.

Both complementary index sets are mapped through Fin.succ into the actual
corner-zero padding. The general zero-rectangle theorem then gives
per(D(B))≥gamma(k+1)gamma(l+1)/gamma(k+l+1−n). An optional separate floor
v≤per(D(B)) can be combined by max; this premise remains explicit until
the independent two-zero permanent theorem is supplied. No numerical
certificate is treated as a universal matrix permanent bound.

Validation: `lake --wfail build Test.NearEndpointCuts`,3498jobs,
eight examples and eight standard-only axiom reports. Tests distinguish
mixed and axis cuts, retain the whole/zero-demand boundary, check the
shifted residual-order denominator, test both finite junctions21,25 and
the zero-deficit consequence q=1. No final near-endpoint principal is
claimed by this increment.
