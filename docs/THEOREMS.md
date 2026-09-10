# Theorems

Let $P$ be a nonnegative real $m\times n$ matrix of total mass one.
Let $F_k(P)$ be the probability that $k$ independent draws with replacement
have distinct rows or distinct columns, with inclusive OR. Put

$$
u_{m,n,k}=\frac{(m)_k}{m^k}+\frac{(n)_k}{n^k}
-\frac{(m)_k(n)_k}{m^kn^k}.
$$

Write $\mathcal U(m,n,k)$ for the statement

$$
\forall P,\quad F_k(P)\leq u_{m,n,k}
\quad\text{and}\quad
(F_k(P)=u_{m,n,k}\iff P_{ij}=1/(mn)\text{ for every }i,j).
$$

There are no positive-entry, balanced-marginal, or support assumptions.
Every rectangular statement below asserts $\mathcal U$ for the specified
parameters. Natural-number dimensions are understood. The logarithm is
natural. Each endpoint statement includes the transpose. The square
near-endpoint statement has $k=n-1$, not $k=n$.

For the square Dittert statement, $A$ instead has total mass $n$ and
$\Phi(A)=\prod_i r_i+\prod_j c_j-\mathrm{per}(A)$. Its equality
matrix has entries $1/n$.

## The twenty principal statements

The links in the first column point to the internal declarations in namespace
`DittertRybin`. [Solution.lean](../Solution.lean) exposes matching statements
with the same short names in namespace `DittertRybinRelease`.

| Declaration | Hypotheses and conclusion | Proof |
|---|---|---|
| [dittert_unique_maximum](../DR/Square/AllOrders.lean) | All n>=1; nonnegative square A of total mass n; Phi(A)<=2-n!/n^n, equality exactly A_ij=1/n. | [Argument](SQUARE-DEPENDENCIES.md) |
| [uniform_maximum_order_two](../DR/Rectangular/OrderTwo.lean) | K=2 on every M,N>=2. | [Argument](RECTANGULAR-FOUNDATIONS.md) |
| [uniform_maximum_order_three](../DR/Rectangular/OrderThreeFinal.lean) | K=3 on every M,N>=3. | [Argument](ORDER-THREE-COMPLETE.md) |
| [uniform_maximum_four_rows](../DR/Rectangular/FourRowFinal.lean) | K=4 on every 4 by N, N>=4, and transpose. | [Argument](FOUR-ROW-PROOF.md) |
| [uniform_maximum_five_by_five_order_four](../DR/Rectangular/FiveByFiveOrderFour.lean) | K=4 on the full 5 by 5 probability simplex. | [Argument](FIXED-BOARD-ORDER-FOUR.md) |
| [uniform_maximum_twenty_by_twenty_order_four](../DR/Rectangular/TwentyByTwentyOrderFour.lean) | K=4 on the full 20 by 20 probability simplex. | [Argument](FIXED-BOARD-ORDER-FOUR.md) |
| [uniform_maximum_large_boards](../DR/Rectangular/LargeBoards.lean) | Every K>=4 and M,N>=128(K-2)(binom(K,2)*binom(binom(K,2)^2,2)+1)^2. | [Argument](RECTANGULAR-FOUNDATIONS.md) |
| [uniform_maximum_large_boards_power](../DR/Rectangular/LargeBoards.lean) | Every K>=4 and min(M,N)>=K^21. | [Argument](RECTANGULAR-FOUNDATIONS.md) |
| [uniform_maximum_large_endpoints](../DR/Endpoint/AllAspects.lean) | K=m on every m by N with m>=10^18 and N>=m, and transpose. | [Argument](ENDPOINT-ALL-ASPECTS.md) |
| [uniform_maximum_quadratic_endpoint_strip](../DR/Endpoint/Quadratic.lean) | K=m, m>=96, N>=10000 m^2, and transpose. | [Argument](ENDPOINT-QUADRATIC.md) |
| [uniform_maximum_quartic_endpoint_strip](../DR/Endpoint/Quartic.lean) | K=m, m>=16, N>=20000 m^4, and transpose. | [Argument](ENDPOINT-QUARTIC.md) |
| [uniform_maximum_combined_endpoint_strip](../DR/Endpoint/Combined.lean) | K=m, m>=5, N>=10^11 m^2, and transpose. | [Argument](ENDPOINT-COMBINED.md) |
| [uniform_maximum_consecutive_endpoint](../DR/Endpoint/Consecutive.lean) | K=m on m by (m+1), m>=19, and transpose. | [Argument](ENDPOINT_CONSECUTIVE_CUTS.md) |
| [uniform_maximum_short_endpoint](../DR/Endpoint/NearSquare.lean) | K=m on m by N with m>=117 and m<=N<=2m, and transpose. | [Argument](ENDPOINT_NEAR_DOUBLE.md) |
| [uniform_maximum_square_near_endpoint](../DR/Endpoint/SquareNearEndpoint.lean) | K=n-1 on n by n, n>=21. | [Argument](SQUARE_NEAR_ENDPOINT.md) |
| [uniform_maximum_arithmetic_endpoint](../DR/Endpoint/Arithmetic.lean) | K=m, m>=128, m<=N<=m(m-1)/(22 log m), and transpose. | [Argument](ENDPOINT-BOUNDARY-SCALING.md) |
| [uniform_maximum_double_endpoint](../DR/Endpoint/Double.lean) | K=m on m by 2m for m>=80, and transpose. | [Argument](ENDPOINT_NEAR_DOUBLE.md) |
| [uniform_maximum_lll_endpoint](../DR/Endpoint/LLLStrip.lean) | K=m, m>=128, 64m^(3/2)<=N<=m(m-1)/20, and transpose, when the interval is nonempty. | [Argument](ENDPOINT-LLL-STRIP-PROOF.md) |
| [uniform_maximum_small_side](../DR/Rectangular/SmallSideFinal.lean) | Every 2<=K<=min(M,N) when 2<=min(M,N)<=4. | [Argument](ORDER-THREE-COMPLETE.md) |
| [uniform_maximum_five_by_five](../DR/Rectangular/FiveByFiveFinal.lean) | Every 2<=K<=5 on 5 by 5. | [Argument](ORDER-THREE-COMPLETE.md) |

The exact integer form of the local-lemma lower cutoff is
$4096m^3\leq n^2$, and its upper cutoff is $20n\leq m(m-1)$.
For $m\geq128$ these are equivalent to the displayed real inequalities.
The logarithmic cutoff is written in Lean without division as
$22n\log m\leq m(m-1)$; its denominator is positive in the stated domain.
The explicit large-board threshold is

$$
D_k=128(k-2)\left[\binom{k}{2}
\binom{\binom{k}{2}^{\!2}}{2}+1\right]^2.
$$

The machine-readable counterpart is [release-targets.json](../release-targets.json).
These twenty statements include corollaries and overlapping ranges; their
number is not a claim of twenty independent new results.

## Proof structure

1. [Finite probability and matrix definitions](../DR/Semimatching.lean)
   identify the sampling event, its uniform value, and the square normalization.
2. [Rectangular collision estimates](RECTANGULAR-FOUNDATIONS.md) prove the
   large-board results. Support classification and exact positive-matrix
   certificates give [all three-sample rectangles](ORDER-THREE-COMPLETE.md)
   and [four-row four-sample rectangles](FOUR-ROW-PROOF.md).
3. [The square proof](SQUARE-DEPENDENCIES.md) combines capacity, transport,
   stationary cuts, and the separate small orders. All permanent
   prerequisites are proved, with their boundary and equality cases.
4. [Endpoint arguments](ENDPOINT-ALL-ASPECTS.md) combine concentration,
   balanced transport, boundary permanent bounds, and collision avoidance.
   Their numerical hypotheses are checked as inequalities for every integer
   in the stated ranges. The [near-endpoint square argument](SQUARE_NEAR_ENDPOINT.md)
   uses a separate two-zero permanent bound.

Full arbitrary-rectangle P2 remains open outside the stated ranges. At
$k=1$ success is always one and uniform uniqueness fails in general.
[Verification](VERIFICATION.md) describes how to check every principal
statement and its complete axiom dependencies.
