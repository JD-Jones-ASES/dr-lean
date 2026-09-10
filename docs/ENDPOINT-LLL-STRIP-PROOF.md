# The collision-local endpoint strip

For an m×n nonnegative matrix P of total mass one, let F_k(P) be the
probability that k independent cell draws have distinct rows or distinct
columns, with inclusive OR. Write U_ij=1/(mn) and (n)_m=n(n−1)…(n−m+1).
At the endpoint k=m, put a=m!/m^m and b=(n)_m/n^m. The sharp statement is
F_m(P)≤a+b−ab, with equality if and only if P=U. A contender means a
probability board satisfying F_m(P)≥F_m(U).

`DR/Endpoint/LLLStrip.lean` exports the theorem
`DittertRybin.uniform_maximum_lll_endpoint`, proving both
`UniformMaximizer m n m` and `UniformMaximizer n m m` under exactly

```
128 <= m
m <= n
4096*m^3 <= n^2
20*n <= m*(m-1).
```

Equivalently, the column interval is 64m^(3/2)≤n≤m(m−1)/20.
The equivalence between the real-power lower bound and 4096m³≤n²
follows by nonnegative squaring, using (m^(3/2))²=m³; it also holds
at m=0. The other hypotheses imply m≤n. This interval is nonempty
at m=2^22,n=2^39, but need not be nonempty for each nominal m≥128.
The theorem permits arbitrary nonnegative entries of total mass one.
Its sharp value is

```
a_m + (1-a_m)*(n)_m/n^m,  a_m=m!/m^m,
```

and equality if and only if the board is uniform.

## Proof

1. Full-probability contender inequalities and the exact uniform avoidance
   product force scaled-row squared deviation below `1/1024` and column
   masses below `2/n`.
2. Deleting any two columns leaves mass above `15/16`, positive rows, and
   normalized row squared deviation below `1/81`. The retained board's own
   independent normalized-row law has column cap `C=4m/n` and `m*C^2<=1/256`.
3. The finite conditional local lemma proves positive actual no-collision
   probability. The proved exact one-doubleton, tripleton, and two-doubleton
   ratios supply all three localized collision bounds. Total collision
   intensity need not be small.
4. The exact injection-successor lower bound gives the elementary coefficient
   floor, with the correct `(m-2)!` normalization. Closed-simplex Maclaurin
   and the all-dimension factorial guard yield the fifth scalar bound.
5. Actual deleted-row rook normalization identifies the blend kernel,
   retaining its scale `product(rowSum)/h^2` and its own avoidance probability.
   The proved `3/32` square-completion criterion gives positive definiteness.
6. The literal midpoint blend identity forces every global maximizer's columns
   to agree. The independent one-sided endpoint rigidity adapter computes
   the resulting product-board probability and applies exact Maclaurin
   equality to force the uniform board. Compactness supplies existence.

The retained squared deviation bound `1/81<1/9` provides a strict margin
in the matrix criterion, including boards with some zero entries.

## Mathematical references

The conditional local-lemma framework is due to Haeupler, Saha and
Srinivasan, [New Constructive Aspects of the Lovasz Local Lemma](https://arxiv.org/abs/1001.1231v5),
Theorems 1.1 and 2.1. The finite argument here derives the conditional
product bound from finite weighted sums and independence of disjoint
row coordinates.

This interval combines with the [arithmetic](ENDPOINT-BOUNDARY-SCALING.md),
[transition](ENDPOINT-TRANSITION-PROOF.md), and
[quadratic](ENDPOINT-QUADRATIC.md) ranges in the
[all-aspect endpoint theorem](ENDPOINT-ALL-ASPECTS.md).

## Formal statements

[LLLStrip](../DR/Endpoint/LLLStrip.lean), [LLLStripDomain](../DR/Endpoint/LLLStripDomain.lean), [LLLStripDeletion](../DR/Endpoint/LLLStripDeletion.lean), [EndpointCoefficient](../DR/Endpoint/EndpointCoefficient.lean).
