# Rectangular endpoint padding

For an m×n real matrix B with m≤n, form an n×n matrix D by scaling the
original rows by m and appending n−m rows whose entries are all 1/n. Then

```
permanent D = (n−m)! * m^m / n^(n−m) * rookSum B m.
```

The identity is signed polynomial algebra. It assumes neither probability
normalization nor a permanent lower bound. Empty original/dummy row sets are
retained; the empty square has permanent one.

[RectangularPaddingCounting](../DR/Endpoint/RectangularPaddingCounting.lean)
identifies a column permutation with an injection of the original rows and
a completion on unused columns. The completion type has cardinality (n−m)!,
which supplies the displayed factorial.

[RectangularPadding](../DR/Endpoint/RectangularPadding.lean) proves that a
nonnegative B with row sums 1/m and column sums 1/n pads to a doubly stochastic
square when m,n>0. Every original zero remains zero at its embedded row.
Uniform rectangular input pads to the uniform square. For m=n this is simply
scalar multiplication by n.

These identities transfer square permanent bounds to rectangular endpoint
problems. The boundary-floor estimate used after padding is a separate
mathematical theorem; see [the published sources](../docs/SOURCES.md) for the
permanent inequalities and Pang's Dittert result.

```sh
lake --wfail build Test.RectangularPadding
```

Tests include two dummy rows and their essential factorial, signed input,
no dummy rows, an all-dummy input, the empty square, and balanced input with zeros.
