# Square Dittert: theorem and proof dependencies

For an integer $n\geq1$, let $A$ be a nonnegative real $n\times n$
matrix with total mass $n$. Write $r_i=\sum_j A_{ij}$,
$c_j=\sum_i A_{ij}$, and $\gamma_n=n!/n^n$. The theorem is

$
  \prod_i r_i+\prod_j c_j-\mathrm{per}(A)\leq2-\gamma_n,
$

with equality if and only if every entry is $1/n$. Zero entries and
arbitrary marginals are included. The complete statement is
`DittertRybin.dittert_unique_maximum` in
[AllOrders.lean](../DR/Square/AllOrders.lean).

## Normalization and compact maximization

For a probability matrix $P$, the scaling $A=nP$ is a bijection onto
the entire mass-$n$ domain and

$
 F_n(P)=\gamma_n\left(\prod_i r_i+\prod_j c_j-\mathrm{per}(A)\right).
$

[Normalization.lean](../DR/Square/Normalization.lean) proves the equivalence,
including equality. [Maximizers.lean](../DR/Square/Maximizers.lean) proves
compactness of the matrix simplex and existence of a global maximizer.
Thus identifying every global maximizer as uniform proves both the sharp
inequality and its unique equality case.

## Permanent and transport foundations

The capacity argument proves van der Waerden's bound
$\mathrm{per}(B)\geq\gamma_n$ for every doubly stochastic matrix
$B$, with equality exactly at the constant matrix. The proof constructs
the row-product polynomial, proves its stability, proves closure under
differentiation and zero specialization with the zero-polynomial alternative,
and iterates a capacity inequality. The full squarefree coefficient is the
actual permanent. A matrix-specific entropy argument establishes equality.
The main conclusions are in [CapacityBound.lean](../DR/Square/CapacityBound.lean)
and [CapacityEquality.lean](../DR/Square/CapacityEquality.lean); the
[capacity account](CAPACITY-ROUTE.md) explains the intermediate results.

[Transport.lean](../DR/Square/Transport.lean) proves the finite real-capacity
criterion: for $A\geq0$ and $q\geq0$, a matrix $0\leq B\leq A$
with every row and column sum $q$ exists exactly when

$
 q(|I|+|J|-n)\leq\sum_{i\in I,\,j\in J}A_{ij}
 \quad\text{for every row set }I\text{ and column set }J.
$

The proof maximizes transported mass and then minimizes row-square energy;
a deficient cut contradicts the displayed inequalities. Combining transport,
permanent monotonicity and van der Waerden gives the
[block lower bounds](../DR/Square/BlockFloor.lean) used in the square proof.

## The spectral argument

At a global maximizer, supported-cell variations give exact stationarity
equations. Normalizing by the row and column marginals produces a contraction
with an explicit singular pair. A finite sweep of the corresponding weighted
coordinates supplies a cut. Shared marginal-deficit bounds control its mass,
while transport and the block permanent floor give the competing lower bound.
Their incompatibility forces the marginal deficit to vanish. Equality in
van der Waerden then identifies the uniform matrix.

The main components are [Stationarity](../DR/Square/Stationarity.lean),
[MarginalDiscrepancy](../DR/Square/MarginalDiscrepancy.lean),
[SpectralPair](../DR/Square/SpectralPair.lean), and
[SpectralAssembly](../DR/Square/SpectralAssembly.lean).
[SpectralSeven](../DR/Square/SpectralSeven.lean) and
[SpectralSix](../DR/Square/SpectralSix.lean) sharpen the finite sweep at the
two smallest dimensions in this branch. The [spectral proof](SPECTRAL-PROOF.md)
gives the detailed inequalities.

## Small orders and assembly

| Orders | Proof |
| --- | --- |
| 1 and 2 | Direct algebra and the exact probability normalization. |
| 3 | Feasible averaging and complete boundary-support classification; [OrderThreeFinal](../DR/Square/OrderThreeFinal.lean). |
| 4 | The actual polynomial gap, complete symmetry coverage, and rational positive-semidefinite certificates with a strict equality argument; [OrderFourFinal](../DR/Square/OrderFourFinal.lean). |
| 5 | Refined stationary cuts and actual block bounds using orders 2, 3 and 4; [SpectralFive](../DR/Square/SpectralFive.lean). |
| At least 6 | The spectral branch above, with all-integer parameter bounds. |

The finite certificates include proofs of their polynomial identities,
physical matrix interpretation, complete coverage, positivity and equality.
Their correctness is checked by Lean's kernel; an external numerical or
symbolic computation is not assumed. [AllOrders](../DR/Square/AllOrders.lean)
combines the branches and exports the square probability theorem through
the normalization equivalence. No rectangular conjecture or desired
permanent bound is an assumption of the final theorem.
