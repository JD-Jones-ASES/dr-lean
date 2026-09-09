# Four-row leading bounds and finite-certificate reduction

These are completed inputs to the rectangular proofs. The full four-row
K=4 theorem and the full rectangular K=3 theorem remain separate targets.
All formulas refer to the actual iid-cell probability F_K with inclusive OR.
Sources are Analytic-Lab P0174 `HIGHER_ORDER_COLLISIONS.md`,
`FOUR_ROW_STRIP.md`, and `FINITE_RECTANGLE_CERTIFICATES_K3.md`.

## Actual four-sample collision remainder

For a four-row probability board P, let r and c be its row and column
marginals, and let B_4(r) be the documented leading quadratic kernel. Put

    L = 6 sum_j P_column_j^T B_4(r) P_column_j.

[The actual remainder](../DR/Rectangular/FourRowRemainder.lean) proves

    0 <= L - (1-F_4(P))
      <= 8 sum_j c_j^3 + 3 (sum_j c_j^2)^2 - 6 sum_j c_j^4
      <= 11 sum_j c_j^3.

The equal-column-pair count exceeds the column-collision indicator
pointwise. Restricting this nonnegative excess to row failure decreases
its expectation. Exact marginalization gives the displayed polynomial;
the factor six counts the actual sample pairs and the complementary-row
factor two is proved explicitly. No column cap, extremality, positive-entry
assumption, or dimension threshold is required. The signed homogeneous
column formula retains the total-mass factor on its cubic term.

[The complete corrected minorant](FOUR-ROW-MINORANT.md) is now proved for
all nonnegative probability vectors r and v, with every boundary case:

    sum_i v_i (1-g_i(r)) <= v^T B_4(r) v.

Its proof derives the actual compact minima, all proper-face reductions,
singular-discriminant exclusions, feasible stationary vectors, and fixed-q
row-optimizer structure. The repeated-row polynomial has 42,875 checked
nonnegative Bernstein coefficients. No minorant or optimizer shape is an
assumption of the final theorem.

[The column-gauge proof](../DR/Rectangular/FourRowGaugeMinorant.lean) handles
zero columns directly and uses normalization and weighted Cauchy for positive
column mass. Thus actual contenders at N>=500 supply every concentration,
deletion and kernel premise. [The final tail](../DR/Rectangular/FourRowTail.lean)
proves uniform unique maximality on the full closed simplex, with sharp value

    1 - (29/32) (6/N - 11/N^2 + 6/N^3).

Actual strict column averaging gives equal columns at every global maximum;
the exact independent-coordinate sampling formula and row-product equality
give uniform rows. The transposed theorem is included. The finite quintic
families below 500 columns remain separate proof obligations. Their
[matrix Bernstein soundness](../DR/Rectangular/FourRowFiniteBernstein.lean)
is now proved on the entire closed parameter interval; the literal block
identities and finite data have not yet been connected.

## Three-sample four-row leading bound

Let f(t)=sqrt(1-(2/3)(1-t)^2), H=sum_i r_i f(r_i), and
a_j=sum_i P_ij f(r_i). The proved scalar and actual sampling bounds are

    H^2 >= 5/8 + (1/4) sum_i(r_i-1/4)^2,
    1-F_3(P) >= sum_j (3 a_j^2 - 11 a_j^3).

[The leading proof](../DR/Rectangular/OrderThreeFourRowLeading.lean)
uses an exact six-square identity for a copositive quadratic minorant.
A continuity argument covers zero elementary-symmetric denominator and
zero-column cases. This is copositivity on nonnegative columns; a stored
signed-column counterexample rejects an unrestricted PSD interpretation.
Contender concentration and final uniqueness for N>=960 are now proved in
[the final strip theorem](../DR/Rectangular/OrderThreeFourRowFinal.lean).
The residual signed-vector kernel floor is 1/8; the actual midpoint gain is
at least 3/16 times the squared column difference. This proves equal columns
at every global maximum and closes the theorem, including transposition.

## Interchangeable ordinary columns in finite K=3 certificates

The [matrix reduction](../DR/Certificates/OrdinaryColumnBlocks.lean) starts
with the actual matrix on distinguished cells and ell ordinary columns.
Write A for the distinguished block, G for each cross block, D for each
ordinary diagonal block, and O for each off-diagonal ordinary block. Set

    H = D-O,
    B = [[A,G],[G^T,(D+(ell-1)O)/ell]].

For z=sum_j y_j and w_j=y_j-z/ell, Lean proves exactly

    Q(x,y) = B(x,z) + sum_j H(w_j).

The identity allows signed vectors and nonsymmetric input blocks. Symmetric
inputs and PSD B,H give PSD of the full physical matrix. If H is positive
definite and B has exactly the kernel (ones,ell*ones), the full quadratic
kernel consists exactly of constant vectors. The principal-block kernel
theorem in [Gram](../DR/Certificates/Gram.lean) supplies the separate aggregate
kernel step after a checked principal certificate and reindexing.

Tests detect the missing factor 1/ell and show why merely semidefinite H
does not establish strict uniqueness. The dimension-independent 93-entry
[orbit construction](../DR/Certificates/FiniteK3Orbits.lean) is now proved:
first-position compression preserves every equality relation on any ambient
type; all fifteen patterns and 225 row/column pattern pairs are complete;
all table entries match the literal sequential-rank canonical key. Actual
entries preserve independent multiplier/quadratic-pair reversal and injective
row/column maps. Transposition is deliberately a separate operation.
The quartic identity, physical seed-kernel coverage, and all 1,330 rational
certificate instantiations still have to be connected.
This matrix reduction alone is not a finite-rectangle P2 theorem.
