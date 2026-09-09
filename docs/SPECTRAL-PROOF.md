# The completed square spectral range

`DittertRybin.dittert_ge_seven` proves the full Dittert inequality and unique
equality for every integer n>=7, including matrices with zero entries. The
expanded original statement is checked in `Test/SpectralSquare.lean`.

The proof follows the Lab's `SPECTRAL_SQUARE_ENDPOINT.md`, with the source
attribution retained in the project provenance records. It is an alternative
proof, with no claim to the first complete resolution of Dittert. Orders three
through six remain separate work, so the all-dimension release target is open.

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

The formal proof includes zero permanent, disconnected support, tied score
values, empty/full capacity cuts and deficit zero. It does not need to remove
the zero-deficit endpoint before forming the scalar coordinate. It also needs
only that the two equal cut sizes lie strictly between zero and n; the sharper
half-dimension bound in the informal source is unnecessary for the permanent
floor used here.

Replay with `lake build DR Test`. The complete public-release gate remains
the full twenty-target inventory and its independent verification.
