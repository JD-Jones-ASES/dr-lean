# Arithmetic boundary scaling and the logarithmic endpoint range

For an m×n nonnegative matrix P of total mass one, let F_k(P) be the
probability that k independent cell draws have distinct rows or distinct
columns, with inclusive OR. Write U_ij=1/(mn) and (n)_m=n(n−1)…(n−m+1).
At the endpoint k=m, put a=m!/m^m and b=(n)_m/n^m. The sharp statement is
F_m(P)≤a+b−ab, with equality if and only if P=U. A contender means a
probability board satisfying F_m(P)≥F_m(U).

[BoundaryScaling.lean](../DR/Endpoint/BoundaryScaling.lean) proves the full
closed-simplex endpoint inequality, with equality exactly at uniform, whenever

    3 ≤ m ≤ n, n ≥ 18, 1 ≤ g, g divides m and n,
    b+(n−1)a < (512/289) g² / [m³ n² (n−1)²],
    a=m!/m^m, b=(n)_m/n^m.

Both orientations are included. The choice g=1 recovers the original
rectangular sufficient criterion; a common divisor retains the arithmetic
gain. The theorem is a sufficient condition, not a classification of all
rectangular endpoints.

The proof has six steps:

1. [Shared marginal control](ENDPOINT-SHARED-MARGINALS.md) applies to the
   actual full-probability contender and its actual rook deficit δ.
2. [The cut argument](../DR/Endpoint/CutDeficit.lean) uses the positive
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

The one-zero permanent bound is proved by polynomial capacity. The
Knopp–Sinkhorn theorem supplies its mathematical antecedent, and
[Pang’s boundary-scaling argument](https://arxiv.org/abs/2606.01531v1)
supplies the ratio method; see [the permanent bound](BOUNDARY_PERMANENT.md).
The rectangular argument uses the joint marginal deficit and the exact
common-divisor spacing of positive cut demands.

[Arithmetic.lean](../DR/Endpoint/Arithmetic.lean) combines this result with
[the exact dimension bounds](ENDPOINT-ARITHMETIC-PARAMETERS.md) to prove the
theorem `uniform_maximum_arithmetic_endpoint`:

    m ≥ 128, m ≤ n, 22 n log(m) ≤ m(m−1), K=m.

Natural logarithms are explicit. A second interface states the upper bound
as n ≤ m(m−1)/(22 log m). The maximum is a+b−ab; both orientations and all
zero-entry boundary boards are covered. Arbitrary rectangular P2 remains open.

The strict scalar inequality is essential to the contradiction. The
argument retains zero rook deficit and nonpositive cuts, and does not
require the input board to have positive entries.

## Formal statements

[Arithmetic](../DR/Endpoint/Arithmetic.lean), [BoundaryScaling](../DR/Endpoint/BoundaryScaling.lean), [BoundaryScalingScalars](../DR/Endpoint/BoundaryScalingScalars.lean).
