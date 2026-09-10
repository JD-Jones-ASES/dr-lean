# Unconditional order-three Dittert endpoint

The proof is in [OrderThreeFinal](../DR/Square/OrderThreeFinal.lean) and
its dependencies.

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
   The Lean theorem proves that these cases exhaust every support mask.
6. `OrderThreeRelabel` proves objective/mass invariance under permutations.
   `OrderThreeFinal` combines all canonical cases, obtains nonempty axes
   from the contender marginal theorem, then uses `Maximizers` to obtain
   the full inequality and unique equality on the entire simplex.

## Relation to the rectangular theorem

This argument proves the square three-sample endpoint. The separate
[three-row theorem](THREE-ROW-PROOF.md) extends the support method to every
three-row rectangle. The [complete three-sample theorem](ORDER-THREE-COMPLETE.md)
combines that family with infinite bounds and finite certificates.
Attribution for the square formulation and earlier results is in
[Sources](SOURCES.md).

## Verification

Run `lake build DR.Square.OrderThreeFinal Test.AllSquareOrders`.
[The complete axiom audit](../Test/Axioms.lean) checks the proof dependencies;
[Verification](VERIFICATION.md) gives the full independent checks.
