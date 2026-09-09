# Unconditional order-three Dittert endpoint

The proof occupies the ten `DR/Square/OrderThree*.lean` modules, 1479 lines.
Integration entry point: `import DR.Square.OrderThreeFinal`.

## Principal results

- `DittertRybin.dittert_order_three : DittertMaximizer 3`.
- `DittertRybin.uniformMaximizer_three_three_three : UniformMaximizer 3 3 3`.
- `DittertRybin.orderThree_globalMax_uniform`: every actual global maximizer
  on the full nonnegative mass-three simplex is the uniform matrix.

The Dittert bound is `16/9`, with equality only at the constant `1/3` matrix.
The equivalent probability endpoint is `32/81`, with equality only at the
uniform probability board. No positivity, support, stationarity, matching,
or order-three maximization theorem is assumed in either principal result.

## Proof structure and scope

1. `OrderThree` proves the six-term permanent expansion, exact homogeneous
   cubic, actual directional derivative, and full-simplex cell-transfer KKT
   inequalities including missing target cells. It also proves exact flat
   same-support column blending and the Schur/quartic/majority certificates
   excluding two distinct doubletons plus a full column.
2. `OrderThreePositive` proves strictly positive maximizer uniqueness using
   just three exact column blends: 01 at 1/2, 02 at 1/3, 12 at 1/2. These
   produce equal columns. The already-proved stationary marginal identity
   forces row sums one. The comparison matrix with a uniform third column
   has trivial kernel, permitting reversal of the two half-averages.
   No limit, Hessian, or auxiliary compact face minimizer is used.
3. `OrderThreeBoundary`, `OrderThreeFaces`, and `OrderThreeCanonical` prove
   the actual singleton, zero-rectangle, two-doubleton, and six-cycle
   exclusions. Disconnected square/cross supports have unconditional
   bounds 3/2 and 27/16, including all zero boundary entries, strictly
   below 16/9. The six-cycle stationary value is exactly 7/4.
4. `OrderThreeSymmetry` and `OrderThreeAveragedFaces` prove feasible,
   support-preserving row/column averages. Each required zero rectangle
   reduces to its canonical matrix in at most two half-averages.
5. `OrderThreeSupport` proves the finite support classification by 512
   explicit Boolean cases and `decide +kernel`. This is not a native
   computation axiom or an assumed support-classification statement.
   An independent Python enumeration found 265 masks with nonempty axes
   and no uncovered mask. The Lean theorem itself proves the exhaustion.
6. `OrderThreeRelabel` proves objective/mass invariance under permutations.
   `OrderThreeFinal` combines all canonical cases, obtains nonempty axes
   from the contender marginal theorem, then uses `Maximizers` to obtain
   the full inequality and unique equality on the entire simplex.

## Provenance

This is the endpoint-only prerequisite requested in the Lab's
`P0174_rybin_semimatchings/SQUARE_SPINOUT_AUDIT.md`, using the mathematical
arguments in `THREE_ROW_PROPER_SUPPORTS_K3.md`,
`THREE_ROW_SINGLETONS_K3.md`, `SINGLE_ZERO_RECTANGLE_K3.md`, and
`POSITIVE_GLOBAL_MAXIMA.md`. The finite three-blend positive proof and
direct disconnected-family bounds simplify the formalization. This
handoff does not claim that order-three Dittert is a new mathematical
result, nor does it widen to an arbitrary rectangular K=3 theorem.

## Verification

- `lake build DR.Square.OrderThreeFinal`: passed, 3205 jobs.
- All ten modules are free of `sorry`, `admit`, custom axioms, and
  `native_decide`; relevant `git diff --check` passed.
- `/private/tmp/DROrderThreeAxioms.lean` checks all 86 public
  definitions/theorems and checks both principal theorem types. It passed;
  every dependency list is a subset of `propext`, `Classical.choice`, and
  `Quot.sound`. There are no additional axioms or native-evaluation axioms.
- Combined repository tests, exact-commit CI and the complete publication gate
  are tracked in PROGRESS.md.

There is no remaining order-three mathematical obligation in these modules.
The full square and rectangle release gate remains open.
