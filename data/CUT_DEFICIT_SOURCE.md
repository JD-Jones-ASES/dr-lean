# Rectangular cut deficit and balanced domination

Mathematical sources: Analytic-Lab P0174
`ENDPOINT_ARITHMETIC_SCALING.md`, positive-cut gcd grid and cut domination;
`PANG_RECTANGULAR_ENDPOINT.md`, rectangular balanced domination argument.
The source notes supply mathematics only; the Lean proof was written independently.

For positive dimensions m,n and any common divisor g, a positive cut demand
p=k/m+l/n−1 has positive integer numerator nk+ml−mn divisible by g.
Consequently p≥g/(mn). This is a lower bound, with no assertion that the
minimum is attained for every shape. The divisor-one and gcd corollaries
retain the original and refined versions respectively.

For an actual nonnegative mass-one matrix P, the exact complementary-cut
identity shows that P(I,J)≥p−epsilon when the sum of the two absolute
marginal subset deviations is at most epsilon. If all such sums are at
most t*g/(mn), 0≤t≤1, then every cut obeys P(I,J)≥(1−t)p.
The nonpositive-demand branch uses nonnegative entries directly. For t<1,
this gives all actual cuts of P/(1−t); the independently proved rectangular
transport criterion constructs a balanced probability matrix B with
(1−t)B≤P. Positive scaling preserves every original zero.

The identity and homogeneity lemmas allow signed matrices. The grid lemma
allows arbitrary natural cardinal inputs. The scaled-cut inequality admits
t=1, while actual division and zero inheritance explicitly require t<1.
No conjectural optimizer, desired cut, or desired balanced matrix is a premise.
The analytic derivation of the discrepancy bound from a contender is separate.

Replay:

```sh
lake --wfail build Test.CutDeficit
```

Tests include an attained gcd grid, rejected larger divisor and zero-demand
mutations, a boundary 2×2 probability matrix with exact nonzero discrepancy,
all-subset checks, actual constructed balanced domination and inherited zero,
t=0, the t=1 failure of zero inheritance, and signed complementary cuts.
All production declarations receive standard-only axiom audits.
