# Near-endpoint scalar tail, n≥26

Source: Analytic-Lab P0174 `NEAR_ENDPOINT_SCALING.md`, estimates(2),(6)
and the final all-dimension scalar argument. These are scalar bounds only;
the two-zero permanent estimate is not a hypothesis or conclusion here.

Lean proves the exact base Z26<3/4 for
Z_n=(5/3)(n−1)^4 n³ gamma_n, then all-dimension monotonicity. The proof
uses the already established gamma_(n+1)≤gamma_n/2 and the simple exact
weight estimate n^4(n+1)^3≤2(n−1)^4n³ for n≥26. This substitutes a
shorter sufficient recurrence for the source's reverse-ratio estimate;
it preserves the same threshold and full infinite range.

Consequently a=(n)_(n−1)/n^(n−1)<3/[5(n−1)^4n²]. The module also derives
a<1/4, (4/3)n²a<1, and the exact strict scaling comparison against
beta=1+1/[4(n−1)²]. Zero deficit is handled by the downstream algebra,
not discarded by taking a positive square root.

Validation: `lake --wfail build Test.NearEndpointParameters`,3466jobs,
six examples and six standard-only axiom reports; no warnings. Persistent
controls show Z25>1, so the sufficient scalar estimate itself does not
establish n=25, and show why the separate m≥2 scalar guard is necessary.
Finite near-endpoint21–25 remains a different, cut-sensitive route.
