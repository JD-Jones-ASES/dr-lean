# Rectangular cut deficit and balanced domination

For positive dimensions m,n and a common divisor g, a positive cut demand
p=k/m+l/n−1 has integer numerator nk+ml−mn divisible by g. Therefore
p≥g/(mn). This is a lower bound; it does not assert attainability for every shape.

For a nonnegative probability matrix P, the complementary-cut identity gives
P(I,J)≥p−ε when the sum of the two absolute marginal subset deviations is at
most ε. If every such sum is at most t*g/(mn), with 0≤t≤1, every cut satisfies
P(I,J)≥(1−t)p. Nonpositive demand uses entrywise nonnegativity directly.
For t<1 the [rectangular transport criterion](../DR/Endpoint/RectangularTransport.lean)
constructs a balanced probability matrix B with (1−t)B≤P. Every zero of P
remains a zero of B.

The [integer grid](../DR/Endpoint/CutDeficitGrid.lean) allows arbitrary natural
cardinalities. The [cut and scaling identities](../DR/Endpoint/CutDeficit.lean)
allow signed matrices where nonnegativity is unnecessary. The scaled inequality
includes t=1; division and zero inheritance require t<1. A contender discrepancy
estimate is an input to this transport step, rather than a consequence of it.

```sh
lake --wfail build Test.CutDeficit
```

The [tests](../Test/CutDeficit.lean) include the gcd constant, zero demand,
signed complementary cuts, exact balanced domination, and the failure of zero
inheritance when t=1.
