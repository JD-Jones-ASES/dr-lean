# Rectangular balanced domination from exact cuts

For positive m,n and arbitrary nonnegative real capacities P, a dominated
matrix B with row sums 1/m and column sums 1/n exists exactly when every pair
of row and column subsets satisfies

```
cutMass P I J ≥ |I|/m + |J|/n − 1.
```

The capacities need not be normalized. Empty subsets and nonpositive demands
are included. The resulting B is a probability matrix, and every zero capacity
remains a zero.

The proof uses the [square transport criterion](../DR/Square/Transport.lean).
For m≤n, append n−m dummy rows of capacities 1/(mn), leaving original
capacities unchanged. A square transport with common marginal 1/m saturates
every dummy cell because each dummy row's total capacity is already 1/m.
Removing those rows leaves column sums 1/n.

For a cut selecting r dummy rows and a column set J, the difference between
the square demand and the rectangular bound has nonnegative slack

```
((n−m)−r) * (n−|J|) / (mn).
```

The [cut decomposition](../DR/Endpoint/RectangularTransportCuts.lean) proves
this identity using the actual row equivalence. Transposition handles m>n.
Necessity follows from the complementary-rectangle identity and nonnegativity.
The final interface is `exists_balanced_dominated_of_rectangular_cuts` in
[RectangularTransport](../DR/Endpoint/RectangularTransport.lean).

```sh
lake --wfail build Test.RectangularTransport
```

Tests include capacities of mass 5/3, saturated positive and zero-demand cuts,
both dimension orderings, and failure when individual cuts or a positive
dimension hypothesis are omitted.
