# The corrected four-row collision minorant

The principal declaration is `DittertRybin.fourRow_corrected_minorant` in
[`FourRowMinorantFinal.lean`](../DR/Rectangular/FourRowMinorantFinal.lean).
For every pair of nonnegative vectors `r,v : Fin 4 → ℝ` with both coordinate
sums equal to one, it proves

```
∑ i, v_i (1 − g_i(r)) ≤ vᵀ B₄(r) v,
g_i(r) = ∑_{j ≠ k; j,k ≠ i} r_j² r_k,
(B₄(r))_ii = 1,
(B₄(r))_ij = 1 − 2 r_k r_l  (i ≠ j, {k,l} complementary).
```

The statement includes every zero row and every support of `v`. No
optimizer shape, stationary feasibility, polynomial identity, or restricted
face bound is a premise. The endpoint probability theorem requires the
additional leading-term and remainder estimates maintained separately.

## Source and proof changes

The mathematical source is Analytic-Lab P0174,
`HIGHER_ORDER_COLLISIONS.md`, sections “Exact boundary theorem” through
“Completion of the corrected four-row minorant,” together with the exact
`k4_minorant_certificate.py` replay. The polynomial and coefficient data
were developed in that investigation. The Lean proof uses Mathlib's
published finite-sum, real analysis, compactness, and polynomial theory;
no peer-repository implementation is an input.

The formal proof makes three elementary replacements within the source
argument. The two-support estimate uses an exact square completion. The
three-row and full fixed-square extremum steps use an explicit rational
rotation preserving the required moments, whose product derivative is
`2(a−b)(a−c)(b−c)`. Finally, a maximum squared norm among tied actual face
minima rules out nonzero flat directions, including the singular
discriminant case. These replacements discharge the source's analytic
reductions inside Lean.

## Dependency map

| Obligation | Modules |
|---|---|
| Actual homogeneous objective and kernel-gap identity; ordered-pair factor two | `FourRowMinorantDefinitions` |
| All two-support distributions and zero-row boundaries | `FourRowMinorantTwo`, `FourRowMinorantFaces` |
| Exact repeated-row polynomial, compactification, and closed-box positivity | `FourRowMinorantRepeated`, `Certificates/FourRowMinorant*` |
| Cubic row scaling and the exact repeated-row averaging loss | `FourRowMinorantEqualRows`, `FourRowMinorantThreeBoundary` |
| True fixed-moment curve, local feasibility, compact affine-product minimum | `FourRowMinorantThreeCurve`, `FourRowMinorantThreeExtrema` |
| Actual three-face stationary formula and feasible-value nonnegativity | `FourRowMinorantThreeStationary`, `FourRowMinorantThreeFeasible` |
| Compact face minimum, flat-direction exclusion, stationary identification, all proper faces | `FourRowMinorantThreeMinimum`, `FourRowMinorantThreeVariation`, `FourRowMinorantThreeFace` |
| Full interior stationary algebra and actual minimum identification | `FourRowMinorantInterior`, `FourRowMinorantVariations`, `FourRowMinorantStationaryMin` |
| Actual fixed-square row maximum has one large coordinate; feasible rational sign | `FourRowMinorantRowCurve`, `FourRowMinorantRowPermutation`, `FourRowMinorantRowExtrema`, `FourRowMinorantOneLarge` |
| Closed fixed-square feasible set, its actual maximum, and full stationary nonnegativity | `FourRowMinorantFullCompact`, `FourRowMinorantFullFeasible` |
| Both closed probability simplices and the visible kernel inequality | `FourRowMinorantFinal` |

## Exact certificate boundary

The repeated-row compactified polynomial has degree at most two in each
of three variables. Its tensor Bernstein representation at degree
`(34,34,34)` is proved by exact finite identities, and all `35³ = 42,875`
coefficient signs are checked by the ordinary Lean kernel. The common
integer denominator is `1122³`; only coefficient `(0,0,0)` is zero and the
smallest positive coefficient is `5323/1188946`. The conversion back to
finite `z ≥ 0` retains the exact positive factor `(1+z)²`.

The generator is an untrusted convenience: the checked Lean equalities
and rational inequalities are the proof. The persistent tests reject
degree 32 via an exact negative coefficient and preserve compactification
and boundary controls. No floating-point computation or `native_decide`
is used in the proof.

## Replays and controls

```
lake build Test.FourRowMinorantRepeated Test.FourRowMinorantFaces
lake build Test.FourRowMinorantThreeExtrema Test.FourRowMinorantThreeStationary
lake build Test.FourRowMinorantThreeFeasible Test.FourRowMinorantThreeFace
lake build Test.FourRowMinorantInterior Test.FourRowMinorantRowExtrema
lake build Test.FourRowMinorantFinal
python3 scripts/generate_four_row_minorant.py --check
```

Controls distinguish an actual feasible distribution from an unconstrained
stationary vector. In particular, `(49,17,17,17)/100` has an infeasible
full stationary vector, and `(3,1,1,10)` has a negative three-face stationary
coordinate despite a positive denominator. Other controls cover zero
discriminant, negative discriminant, zero affine-product coefficient,
signed row scaling, nonunit row mass, multiple zero rows, all repeated-pair
orientations, and stationary coordinates exactly zero.

The principal axiom audit is printed by `Test.FourRowMinorantFinal`.
The final local replay passed **2,395 build jobs and five principal axiom
audits**, with no warnings. The proper-face replay separately passed 2,388
jobs and eight audits.
The allowed logical dependencies are `propext`, `Classical.choice`, and
`Quot.sound`; there are no custom axioms or unfinished proof terms.
