# Rectangular endpoint padding

Mathematical source: Analytic-Lab,
`probes/P0174_rybin_semimatchings/PANG_RECTANGULAR_ENDPOINT.md`, section
“The boundary gap survives rectangular padding at K=m,” equation (8).
The inspected source SHA-256 is
`180858fe7a6fb077c98c00b7e59f4bf082f6af6f1e49b71bc68589cf6c0b6ad2`.
Only the mathematical statement is used; no Lab implementation is imported.

For an m×n real board B with m≤n, the padding D has the m original rows
scaled by m, followed by n−m dummy rows with every entry1/n. The proved
identity is

```
permanent D = (n−m)! * m^m / n^(n−m) * rookSum B m.
```

The proof is signed polynomial algebra. It does not assume probability,
balance, positivity, a permanent lower bound, or any boundary gap. Original
and dummy rows may be empty; the empty square has permanent1.

`RectangularPaddingCounting.lean` exposes the actual equivalence between a
permutation of the n columns and an injection of the original m rows plus
a completion of the dummy rows into the unused columns. Every completion
is proved bijective, and its type has cardinal(n−m)!. The weighted summation
uses Mathlib's exact sum-embedding equivalence and finite cardinal theorems.
It does not enumerate sample boards or accept an assumed counting identity.

`RectangularPadding.lean` proves that nonnegative B with row sums1/m and
column sums1/n pads to an actual member of `doublyStochastic ℝ (Fin n)` when
m,n are positive. Uniform rectangular input pads to the uniform doubly
stochastic square, even in the empty-original-row case. Every zero in an
original cell remains zero at its explicitly embedded row. The m=n case is
exactly scalar multiplication by n.

These are foundations for transferring a separately proved square boundary
floor. No Knopp–Sinkhorn or Pang boundary-floor premise enters this module,
and the later source inequalities (9)–(10) are not claimed here.

Reproduction:

```bash
lake --wfail build +Test.RectangularPadding
```

Persistent controls retain two dummy rows and their essential factorial,
a signed1×3 input with padded permanent−4/3, rejection of the result obtained
by dropping2!, no dummy rows, one dummy row, an all-dummy input, the empty
square, and an explicit balanced2×3 board whose padding is doubly stochastic
and still has a zero cell.
