# Two-zero permanent formula: logarithmic tail

[TwoZeroLogBounds](../DR/Endpoint/TwoZeroLogBounds.lean) proves three logarithmic
truncation inequalities by derivative identities and monotonicity, with equality
at zero and explicit denominator guards.
[TwoZeroLogAlgebra](../DR/Endpoint/TwoZeroLogAlgebra.lean) supplies the rational
identity and bounds its logarithm arguments.

For its degree-16 polynomial E and 0≤q≤1/25, direct term estimates give

```
E(q) ≥ 3 − 71q − 46q³ − 14568q⁵
     ≥ 1519182/9765625 > 0.
```

Negative terms of degree at least five use qᵏ≤q⁵; only nonnegative terms
are discarded. Together with exact normalization by the one-zero boundary
floor, [TwoZeroLogTail](../DR/Endpoint/TwoZeroLogTail.lean) proves

```
boundaryPermanentFloor (m+2) * (1+1/(4*m²))
  < twoZeroReducedPermanent m a b
```

for every m≥25 and 0≤a,b≤1/m. This is a scalar theorem on the full closed
parameter rectangle, including zero exceptional diagonals and borders.
The [actual matrix reduction](../DR/Endpoint/TwoZeroPermanent.lean) turns it
into a permanent inequality for matrices with two independent zeros.

```sh
lake --wfail build Test.TwoZeroLogTail
```

Tests include both signs of the logarithmic expansions, equality at zero,
the exact endpoint value, a denominator pole, and failure at q=1/20.
