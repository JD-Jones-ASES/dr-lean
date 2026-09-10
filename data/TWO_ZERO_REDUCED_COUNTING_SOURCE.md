# Permanent of the reduced two-zero matrix

[TwoZeroReducedBoard](../DR/Endpoint/TwoZeroReducedBoard.lean) defines a matrix
with two exceptional diagonal entries 1−na,1−nb, two exceptional off-diagonal
zeros, symmetric borders a,b, and constant ordinary core x=(1−a−b)/n.
For n≥2 and arbitrary signed real a,b,
[TwoZeroReducedCounting](../DR/Endpoint/TwoZeroReducedCounting.lean) proves

```
permanent = n! [ (1−na)(1−nb)xⁿ
              + n((1−na)b²+(1−nb)a²)xⁿ⁻¹
              + n(n−1)a²b²xⁿ⁻² ].
```

The proof begins with five independent signed parameters for the two
exceptional diagonals, borders and core. Two Laplace expansions leave identical
rows, whose permutations contribute n!. Removing an ordinary column preserves
the exceptional coordinates; ordinary choices contribute n and n(n−1).
No division by entries or positive approximation is used.

The matrix entries are then identified with `twoZeroReducedBoard`, and the
expansion factors into the [scalar formula](TWO_ZERO_POLYNOMIAL_SOURCE.md).
The [face reduction](../DR/Endpoint/TwoZeroReduction.lean) separately justifies
using this form for a permanent minimizer.

```sh
lake --wfail build Test.TwoZeroReducedCounting
```

Tests include n=2, a zero core, zero borders, zero exceptional diagonals,
negative signed permanents, a missing-factorial mutation, and an n=1
counterexample to removing the dimension guard.
