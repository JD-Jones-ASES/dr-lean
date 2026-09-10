# Rectangular balanced domination from exact cuts

Mathematical source: Analytic-Lab,
`probes/P0174_rybin_semimatchings/PANG_RECTANGULAR_ENDPOINT.md`, section
“Rectangular domination by a balanced matrix.” The inspected source SHA-256 is
`180858fe7a6fb077c98c00b7e59f4bf082f6af6f1e49b71bc68589cf6c0b6ad2`.
Only its mathematical condition is used. No Lab implementation is imported.

For positive m,n and arbitrary nonnegative real capacities P, the theorem
proves that a dominated matrix B with row sums1/m and column sums1/n exists
if and only if every pair of row and column subsets satisfies

```
cutMass P I J ≥ |I|/m + |J|/n − 1.
```

All subsets are included, even when the right side is zero or negative.
The capacity matrix need not be normalized or balanced. The resulting B is
proved to be a probability board, and every zero capacity remains a zero.

The proof reuses the independently proved real square transport criterion
in `DR/Square/Transport.lean`. For m≤n, it adjoins n−m dummy rows of capacities
1/(mn), leaving original capacities unchanged. This is exactly
`(1/m) • rectangularPadding hmn P`. A square transport with common marginal
1/m must saturate every dummy cell: each dummy row's total capacity already
is1/m, and a finite sum of nonnegative capacity deficits can vanish only
when every deficit vanishes. Removing those rows leaves column mass1/n.

For a square cut selecting r dummy rows and a column set J, the difference
between its required bound and the supplied rectangular bound is controlled
by the exact nonnegative slack

```
((n−m)−r) * (n−|J|) / (mn).
```

The formal cut split uses the actual original/dummy row equivalence and
proves the finite cardinal identity. Transposition handles m>n. Necessity
follows from the exact complementary-rectangle identity and nonnegativity.
The proof assumes no unrestricted max-flow theorem, integrality,
algorithmic termination, or pre-existing balanced dominated matrix.

Production files:

- `DR/Endpoint/RectangularTransportCuts.lean`
- `DR/Endpoint/RectangularTransport.lean`

The explicit public interface is
`exists_balanced_dominated_of_rectangular_cuts`; structured transport,
necessity/sufficiency, probability, and zero-preservation APIs are also
provided. Positive dimensions are explicit hypotheses wherever needed.

Reproduction:

```bash
lake --wfail build +Test.RectangularTransport
```

Persistent tests cover a capacity matrix of mass5/3 with zeros, an exactly
saturated positive cut, a zero-demand equality cut, a negative-demand cut
with zero capacity, both dimension orderings, and the square case. Rejected
weakenings show that partial transports need not saturate dummy rows, that
sufficient total capacity alone does not replace individual cuts, and that
either positive-dimension hypothesis is necessary.
