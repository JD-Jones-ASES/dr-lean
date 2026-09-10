# Finite near-endpoint scalar certificates, n=21,...,25

Source: Analytic-Lab P0174 `ACTIVE_CUT_RECTANGULAR_EXTENSIONS.md`, literal
NEAR_CASES table and displayed near-endpoint cut equations. Source SHA256:
`4ae2b41d7b6e1969c180501bc336cb567f12fe787ff853bcf465f1d37f32e28e`.
The exact source literals were extracted with ast.literal_eval and compared
against the Lean left-endpoint/excess clauses; no source implementation was
imported. `NEAR_ENDPOINT_CUT_REPLAY.json` records the independent rational
replay and exact worst relative margins.

The five lower endpoints times10^8 are4976889,4741862,4527961,4332468,4153110;
each upper endpoint is larger by10^−8. The excesses times10^9 are1112507,
1014678,929196,854069,787692. Every cubic bracket is checked with its exact
strict signs, its0<lo<hi<1/m domain, and the lower-reference comparison
μ_(n+1)(1+excess)<m!*x(lo)^(m−2)*h(hi),m=n−1.

For every admissible ordered cut size(k,l), exact rational gates verify
Ckl*a/(1−a)<1/10000 and beta−a−m²*Ckl*beta²/[4(1−a)]>3a/10000.
The reference beta uses the maximum of the declared two-zero scalar floor
and the actual zero-rectangle floor on mixed cuts, and the declared scalar
floor on axis cuts. Real cast lemmas connect every term to the existing
actual matrix/cut definitions, preserving the μ_(n+1) denominator.

The five Fin(n+1)×Fin(n+1) universal gates cover230,252,275,299,324 admissible
non-whole positive ordered cut sizes, totaling1380. Whole and nonpositive
cuts are excluded by explicit implications and are not discarded from an
unrecorded lookup table. The separate actual-matrix proof handles whole cuts.

Validation: `lake --wfail build Test.NearEndpointCutCertificates`,3504jobs,
10examples,5standard-only axiom reports,322Lean lines. Each dimension's actual
gate took3.2–4.2seconds. Source-literal comparison and a separate Fraction
replay also passed all1380 comparisons. Tests reject a reversed bracket
sign, extending the literal bracket table to26, removal of the two-zero
improvement, and omission of one positive ordered cut. No native_decide,
new axiom, or numerical optimizer is used.

**Scope:** these are exact scalar certificates. Their declared two-zero
reference is not yet known here to bound every relevant matrix permanent.
That requires the separate face-reduction/univariate theorem. No final
near-endpoint UniformMaximizer declaration is claimed in this increment.
