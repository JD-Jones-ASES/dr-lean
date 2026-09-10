# Square near-endpoint theorem

`DittertRybin.uniform_maximum_square_near_endpoint` proves
`UniformMaximizer n n (n-1)` for every natural n at least 21. Its domain is every
nonnegative real n by n matrix of total mass one, including all zero-entry
supports. The objective is the actual probability that n-1 independent cell
draws have distinct rows or distinct columns, with inclusive OR. The maximum
is `a*(2-a)`, where `a = n!/n^(n-1)`. Equality holds exactly at the constant
probability board with entries 1/n².

The final declaration has only the dimension hypothesis. It does not assume a
permanent bound, optimizer form, scalar certificate, positivity of the input
matrix, or existence of a balanced dominated matrix.

## Proof

The exact sampling and near-endpoint rook identities provide a shared deficit
for the row and column marginals. Actual finite transport yields balanced
domination. For a balanced probability board B, with each row and column
sum equal to 1/n, form the (n+1)×(n+1) matrix

```
D = [ 0           (1/n) 1ᵀ ]
    [ (1/n) 1     (n−1) B  ].
```

Every row and column of D sums to one. A zero of B lies in a different
row and column from D's upper-left zero, giving two independent zeros.
Expansion along the added row and column proves, even for signed B,

```
per D = ((n−1)^(n−1)/n²) rookSum(B,n−1).
```

Here rookSum(B,k) sums the products of entries over k-cell matchings,
counting each matching once. The formula converts the normalized rook
value exactly to the one-zero boundary scale
μ_(n+1)=(n−1)!((n−1)/n²)^(n−1); it introduces no additional factorial.

On the closed two-zero doubly stochastic face, compactness and least squared
norm select a genuine face minimum. Supported and one-sided cofactor arguments,
the proved repeated-row permanent inequality, and feasible averaging make all
ordinary rows and columns equal. The resulting two-parameter matrix has its
permanent evaluated by two Laplace expansions, valid even for signed parameters.
Equalization and the proved cubic bracket then bound the entire closed feasible
parameter rectangle.

For n=21,...,25 the full ordered active-cut certificates strengthen the bound
with the actual complementary zero rectangle of a minimum dilation. For n at
least 26 the logarithmic scalar tail supplies a dimension-uniform gap. Both
routes exclude every boundary contender, including zero deficit and unit
dilation. The positivity-of-all-global-maximizers theorem then gives
the sharp inequality and exact equality case on the full probability simplex.

## Mathematical references

The two-zero face argument follows the repeated-support model studied
by Pula, Song and Wanless,
[Minimum permanents on two faces of the polytope of doubly stochastic matrices](https://cs.du.edu/~mathfiles/preprints/nsm-math-preprint-1022.pdf).
The [face reduction](TWO_ZERO_REDUCTION.md) and
[permanent bounds](TWO_ZERO_PERMANENT.md) derive the matrix and scalar
steps used above, allowing additional zero entries.

## Formal statements

[NearEndpointPadding](../DR/Endpoint/NearEndpointPadding.lean), [NearEndpointConditional](../DR/Endpoint/NearEndpointConditional.lean), [TwoZeroPermanent](../DR/Endpoint/TwoZeroPermanent.lean), [SquareNearEndpoint](../DR/Endpoint/SquareNearEndpoint.lean).
