# The square spectral range

`DittertRybin.dittert_ge_six` proves the full Dittert inequality and unique
equality for every integer n>=6, including matrices with zero entries. The
expanded original statement is checked in `Test/SpectralSquare.lean`.

This is the spectral part of the alternative square proof credited in
[Sources](SOURCES.md). [AllOrders](../DR/Square/AllOrders.lean) combines
it with the elementary orders one and two and the separate
[order-three](ORDER-THREE-PROOF.md), [order-four](ORDER-FOUR-PROOF.md),
and [order-five](ORDER-FIVE-PROOF.md) arguments.

The dependency chain is:

1. `Stationarity` and `Contenders` derive feasible-scaling equations and
   positive marginals for an actual global maximizer on the closed simplex.
2. `SpectralPair` constructs the actual reversible weights, conductances and
   score, proves its energy identity, and obtains positive variance for any
   nonuniform global maximizer using the permanent equality theorem.
3. `WeightedSweep`, `SweepReindex` and `SpectralCut` produce actual row and
   column subsets and their original-matrix crossing mass. `RefinedSweep`
   checks the rational path certificate needed at n=7.
4. `MarginalDiscrepancy` bounds both axis discrepancies from their shared
   deficit budget. `SpectralCut` proves transport cuts and equal cardinalities.
5. `BlockFloor` applies the proved transport and van der Waerden results to
   the two arbitrary diagonal submatrices. `SpectralAssembly` turns this
   into the exact scalar contradiction for n>=8; `SpectralSeven` supplies
   the refined order-seven case.
6. `Square/Maximizers` supplies compactness and converts classification of
   every actual maximizer into the full inequality and iff equality.

For n=6, `SixMarginalBounds` proves the sharper shared discrepancy envelope.
`AlternatingPath` and `AlternatingSweep` supply a balanced cut through exact
Gram algebra and a minimum over even prefixes. `ScoreOrder` preserves the
singleton's extremal marginal orientation under complementation, and
`SixMatrixBounds` retains that actual singleton entry in its permanent floor.
`Certificates/SpectralSix` checks all 546 Bernstein coefficients and the
positive denominator transfer. `Square/SpectralSix` applies both floors to
the same cut and concludes full unique maximization.

The formal proof includes zero permanent, disconnected support, tied score
values, empty/full capacity cuts and deficit zero. It does not need to remove
the zero-deficit endpoint before forming the scalar coordinate. It also needs
only that the two equal cut sizes lie strictly between zero and n for the
permanent floor used here.

Run `lake build DR Test`. See [Verification](VERIFICATION.md) for the
complete axiom and independent-kernel checks.
