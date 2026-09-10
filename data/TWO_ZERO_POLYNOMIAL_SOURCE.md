# Two-zero permanent formula: equalization and brackets

`twoZeroReducedPermanent m a b` is the explicit two-parameter formula defined
in [TwoZeroPolynomial](../DR/Endpoint/TwoZeroPolynomial.lean).
For every m≥4 and 0≤a,b≤1/m:

- replacing a,b by their mean lowers the formula, strictly when a≠b;
- the equalized expression is m! x(u)ᵐ⁻² h(u), with u=1−m(a+b)/2∈[0,1];
- its derivative has the sign of an explicit cubic, strictly increasing on ℝ;
- h decreases on [0,1/m];
- a bracket 0≤ℓ≤r≤1/m with f(ℓ)≤0≤f(r) gives the lower bound
  m! x(ℓ)ᵐ⁻² h(r) throughout the parameter rectangle;
- the strict coarse bracket ℓ=1/m−2/m³, r=1/m works for every m≥4.

The [bracket proof](../DR/Endpoint/TwoZeroPolynomialBracket.lean) uses monotonicity
outside the bracket and separate monotonicity of its two factors inside it.
The lower-point sign follows from a positive-coefficient expansion in m−4.
No numerical root or assumed minimizer is required.

[NearEndpointTwoZeroPolynomial](../DR/Endpoint/NearEndpointTwoZeroPolynomial.lean)
transfers the five [rational brackets](NEAR_ENDPOINT_FINITE_CUTS_SOURCE.md)
to strict real bounds for n=21,…,25 and m=n−1. The
[logarithmic estimate](TWO_ZERO_LOG_TAIL_SOURCE.md) covers the infinite tail.
[TwoZeroPermanent](../DR/Endpoint/TwoZeroPermanent.lean) proves their application
to actual matrices. Related face-minimizer methods are attributed to
Pula–Song–Wanless (2011) and Minc in [the published sources](../docs/SOURCES.md).

```sh
lake --wfail build Test.TwoZeroPolynomial Test.NearEndpointTwoZeroPolynomial
```

Tests retain zero exceptional diagonals and borders, signed polynomial
identities, both endpoints, exact m⁴ normalization, and failures after reversing
equalization or dropping the parameter bound.
