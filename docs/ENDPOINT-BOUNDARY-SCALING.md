# Arithmetic boundary scaling and the logarithmic endpoint range

[BoundaryScaling.lean](../DR/Endpoint/BoundaryScaling.lean) proves the full
closed-simplex endpoint inequality, with equality exactly at uniform, whenever

    3 ≤ m ≤ n, n ≥ 18, 1 ≤ g, g divides m and n,
    b+(n−1)a < (512/289) g² / [m³ n² (n−1)²],
    a=m!/m^m, b=(n)_m/n^m.

Both orientations are included. The choice g=1 recovers the original
rectangular sufficient criterion; a common divisor retains the arithmetic
gain. The theorem is a sufficient condition, not a classification of all
rectangular endpoints.

The proof connects independently checked ingredients:

1. [Shared marginal control](ENDPOINT-SHARED-MARGINALS.md) applies to the
   actual full-probability contender and its actual rook deficit δ.
2. [The cut argument](../data/CUT_DEFICIT_SOURCE.md) uses the positive
   integer numerator of each cut. Its common-divisor lower bound g/(mn)
   constructs a balanced probability board B with (1−t)B ≤ P, where
   t² = Lδ and L = 2mn²[1+(n−1)a/b]/(3g²). Nonpositive cuts remain valid.
3. [Rectangular padding and its boundary rook floor](BOUNDARY_ROOK.md)
   turn any zero of P into a zero of B and prove
   (1−t)^m b κ_n ≤ m^m rookSum(P,m), with κ_n=μ_n/a_n.
4. [The boundary permanent ratio](BOUNDARY_PERMANENT.md) gives
   (κ_n−1)/κ_n² > (16/17)²/[3(n−1)²]. The exact scalar criterion
   implies b<1/4, 0<L, Lb<1 and m²bL/4 below this ratio.
5. [Bernoulli and square completion](../DR/Endpoint/BoundaryScalingScalars.lean)
   contradict the boundary inequality, including δ=0. Hence all actual
   global maximizers are positive.
6. [Compactness and maximum squared norm](POSITIVE_MAXIMIZERS.md) identify
   every global maximizer as uniform and give the full iff equality statement.

The permanent bound is proved internally from the capacity development.
The mathematical sources remain the Knopp–Sinkhorn boundary theorem and
Pang's boundary-scaling method and ratio bound; see the boundary source note
for the precise attribution. The rectangular padding, joint deficit and
arithmetic refinement are the accepted Analytic-Lab P0174 derivations.

[Arithmetic.lean](../DR/Endpoint/Arithmetic.lean) combines this result with
[the exact dimension bounds](ENDPOINT-ARITHMETIC-PARAMETERS.md) to prove the
required release target `uniform_maximum_arithmetic_endpoint`:

    m ≥ 128, m ≤ n, 22 n log(m) ≤ m(m−1), K=m.

Natural logarithms are explicit. A second interface states the upper bound
as n ≤ m(m−1)/(22 log m). The maximum is a+b−ab; both orientations and all
zero-entry boundary boards are covered. Arbitrary rectangular P2 remains open.

Replay:

```sh
lake --wfail build +Test.EndpointMarginalDiscrepancy +Test.BoundaryScaling
```

Tests cover zero and positive deficits, strict scalar-gap necessity, the
common-divisor size condition, an admitted 256-by-300 rectangle and transpose,
the quotient cutoff, and actual strict boundary exclusion. The seven scaling
and final arithmetic APIs have only propext, Classical.choice and Quot.sound
as transitive axioms.
