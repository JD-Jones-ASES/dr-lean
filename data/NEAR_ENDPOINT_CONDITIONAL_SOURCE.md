# Conditional near-endpoint closure

Mathematical source: Analytic-Lab P0174 `NEAR_ENDPOINT_SCALING.md`,
`TWO_ZERO_PERMANENT_GAP.md`, and `ACTIVE_CUT_RECTANGULAR_EXTENSIONS.md`.
The finite rational source and its five-row hash are preserved separately in
`NEAR_ENDPOINT_FINITE_CUTS_SOURCE.md`; the scalar polynomial and all-order
logarithmic tail have their own source receipts.

`NearEndpointBoundaryTail`, `NearEndpointBoundaryFinite`, and
`NearEndpointConditional` close the actual probability-matrix transport
argument for every square dimension n at least 21, conditional on one explicit
permanent bound for actual doubly stochastic (n+1)-square matrices with two
independent zeros. These files do not prove or assume a principal near-endpoint
theorem unconditionally.

For n=21,...,25 the proof uses the actual minimum dilation q, the actual active
positive cut and its complementary zero rectangle. The case q=1 is handled
separately; otherwise a whole cut would contradict q<1. The complete ordered
finite gates provide the strict quadratic scaling gap. For n at least 26 the
shared-deficit balanced domination and the proved logarithmic scalar parameters
give boundary exclusion directly. The normalization is the boundary permanent
floor mu_(n+1), not the uniform permanent gamma_(n+1).

The positivity-to-uniformity theorem retains the full closed probability
simplex and exact equality case. Its only remaining external mathematical input
is `TwoIndependentZeroPermanentBound`. An adapter from a genuine actual-matrix
reduced-form inequality records the exact obligation for the face theorem;
no existence, averaging, or coefficient identity is assumed as a declaration.

Replay: `lake build Test.NearEndpointConditional`. Persistent controls cover
the finite/analytic junction, zero exceptional diagonal parameters, c=1 zero
inheritance, rejection at c=0, and the vacuous independent-zero domain in order
one. Six axiom audits use only Lean's standard logical axioms.
