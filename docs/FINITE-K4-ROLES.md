# Five-cell roles for K=4 certificates

The quintic certificate uses three multiplier cells and two quadratic
cells. Its coefficient depends only on their row and column equality
relations, after permuting the three multiplier positions and the two
quadratic positions independently. Row/column transposition is a separate
operation. This account describes the exact role catalogue and its
connection to the physical formula; it does not supply matrix positivity
or a complete finite K=4 theorem.

The mathematical source is Analytic-Lab P0174 `quintic_certificate.py` and
the associated quintic certificate notes. The universal catalogue has 407
roles; the four-row restriction has 391, in the same lexicographic order
as the two finite four-row coefficient families. The separate four-by-four
restriction has 376 roles. The generator checks these counts, and Lean
independently verifies completeness for the 407- and 391-role catalogues.

## From physical labels to a finite table

[TupleLabelPermutation](../DR/Certificates/TupleLabelPermutation.lean)
proves that two finite natural-label tuples with the same equality
relations are related by a permutation of all natural labels. The proof
uses the finite subtype of first-occurrence representatives, where both
maps are injective, and extends their bijection. Repeated labels, unused
labels and empty tuples are included.

[FiniteFiveTuplePattern](../DR/Certificates/FiniteFiveTuplePattern.lean)
proves completeness and injectivity of all 52 five-position equality
patterns. First-position labels preserve exactly the original equalities.
The sole pattern with five distinct labels is the final identity pattern;
a repeated label therefore has one of the first 51 indices. These are
first-position labels, so a representative can equal 4 even when there
are only four distinct physical row labels.

[RoleSemantics](../DR/Certificates/FiniteK4RoleSemantics.lean) uses separate
row and column permutations to compress the actual List-based canonical
key. This key normalizes sequential first-occurrence ranks, encodes the
five pairs in radix 25, and takes the minimum over all 3! times 2! orders.
It is exactly the formula used by
[FourRowFiniteRole](../DR/Rectangular/FourRowFiniteRole.lean).

The complete table has 52 times 52 entries. To make its ordinary Lean
kernel replay economical, [RoleCache](../DR/Certificates/FiniteK4RoleCache.lean)
proves the 624 one-axis normalizations once, then reuses them in
[the actual role checks](../DR/Certificates/FiniteK4OrbitChecks.lean).
This changes evaluation cost, not the defining formula or the obligations.

[FiniteK4Orbits](../DR/Certificates/FiniteK4Orbits.lean) exposes an index in
`Fin 407` for every physical tuple and proves that its stored key equals
the actual canonical key. One checked witness per role proves surjectivity;
injective stored keys exclude duplicated roles. A checked 51-by-52 subtable
and 391 witnesses establish the four-row restriction. The physical theorem
applies to every `Fin 4 × Fin n` board, without a column cutoff.

## Relation to the quintic probability identity

[Symmetrization](../DR/Rectangular/FourRowFiniteSymmetrization.lean) proves
that an exact sum over all 120 position permutations determines the actual
quintic polynomial. All 120 terms remain present when cells repeat.
[Certificate evaluation](../DR/Rectangular/FourRowFiniteCertificate.lean)
splits the five ordered positions into a multiplier triple and an actual
quadratic pair. The ordered triple has correction 1, 1/3 or 1/6 according
to whether it has one, two or three distinct cells.

Evaluation is the literal weighted sum of quadratic matrix values, including
signed unnormalized board weights. For a nonnegative mass-one board, PSD
of every physical matrix gives a nonnegative sum. A positive cell repeated
three times supplies a strictly positive multiplier, so an exact constant
quadratic kernel yields uniform equality even on the simplex boundary.

The finite coefficient identities, actual small-block matrix reductions,
positive Gram gates and complete parameter coverage are connected in the
[full four-row proof](FOUR-ROW-PROOF.md) and the
[fixed-board proofs](FIXED-BOARD-ORDER-FOUR.md). This role catalogue supplies
their exhaustive physical classification; positivity comes from those
separately proved certificate and kernel arguments.

## Replay

```sh
python3 scripts/generate_finite_k4_orbits.py --check
python3 scripts/test_finite_k4_orbits.py
lake build Test.FiniteK4Orbits Test.FourRowFiniteCertificate
```

The generator and six corruption/boundary controls also run under Python
`-O`. Lean checks the generated data with its ordinary kernel. The tests
retain arbitrary relabelings, repeated and empty tuples, and explicitly
reject merging row/column transposes or collapsing distinct labels.

The catalogue test build passed 2,486 jobs and seven standard-only axiom
audits. Large finite coverage checks are split by index or row, with their
elaboration serialized to limit overlapping kernel reduction caches. The
coverage statements and all literal cases are unchanged by that scheduling.
