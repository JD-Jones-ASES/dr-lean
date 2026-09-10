# Finite near-endpoint scalar certificates, n=21,…,25

[NearEndpointCutRational](../DR/Endpoint/NearEndpointCutRational.lean) defines
five exact cubic brackets and excesses:

| n | Lower endpoint ×10⁸ | Excess ×10⁹ |
| --- | --- | --- |
| 21 | 4976889 | 1112507 |
| 22 | 4741862 | 1014678 |
| 23 | 4527961 | 929196 |
| 24 | 4332468 | 854069 |
| 25 | 4153110 | 787692 |

Each upper endpoint exceeds the lower endpoint by 10⁻⁸. Exact inequalities
verify the strict cubic signs, 0<lo<hi<1/m, and
μₙ₊₁(1+excess)<m! x(lo)ᵐ⁻² h(hi), where m=n−1.
The [scalar polynomial argument](TWO_ZERO_POLYNOMIAL_SOURCE.md) explains
why this bracket gives a permanent-formula lower bound.

For every admissible ordered cut size (k,l), the certificates verify
Cₖₗa/(1−a)<1/10000 and
β−a−m²Cₖₗβ²/[4(1−a)]>3a/10000.
On mixed cuts β uses the maximum of the two-zero floor and the zero-rectangle
floor; axis cuts use the two-zero floor. The cast lemmas preserve the actual
matrix definitions and the boundary-floor denominator μₙ₊₁.

[NearEndpointCutCertificates](../DR/Endpoint/NearEndpointCutCertificates.lean)
checks respectively 230, 252, 275, 299 and 324 positive ordered cut sizes that
are not whole cuts: 1,380 cases. Whole and nonpositive cuts remain explicit
branches of the [matrix argument](NEAR_ENDPOINT_CUTS_SOURCE.md).
The [two-zero theorem](../DR/Endpoint/TwoZeroPermanent.lean) supplies the actual
matrix interpretation of the scalar floor.

```sh
lake --wfail build Test.NearEndpointCutCertificates
```

Tests reject reversed bracket signs, an extension of the literal table to
n=26, removal of the two-zero improvement, and omission of a positive cut.
