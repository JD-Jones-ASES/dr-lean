# From eight small blocks to an actual K=3 theorem

`FiniteK3EnvelopeValid.uniformMaximizer` in
[FiniteK3EnvelopeSoundness](../DR/Certificates/FiniteK3EnvelopeSoundness.lean)
turns one complete rational certificate into the original sharp inequality
and exact uniform equality on the entire nonnegative mass-one simplex.
Its hypotheses are the literal 33 coefficient equations, four aggregate
kernel equations, and positive definiteness of four H and four B0 blocks.
It assumes neither the desired inequality nor a property of the full seed
matrices. The adapter has dimensions `2 ≤ m` and `4 ≤ n`; a concrete result
still requires an actual certificate at those dimensions.

The mathematical source is Analytic-Lab P0174
`FINITE_RECTANGLE_CERTIFICATES_K3.md`, equations (4)–(8) and its strict
uniqueness argument. The formalization keeps the source's original
coefficient roles and iid functional. The Lab source owns the mathematical
reduction and rational catalogue; the present Lean layers prove its
semantics. No claim of worldwide novelty follows from this implementation.

## Matrix meaning and indexing

Fix a multiplier representative meeting k distinguished columns and put
ell = n-k. The generic physical blocks are A on distinguished cells, G
between distinguished and ordinary cells, D within one ordinary column,
and O between distinct ordinary columns. Their entries come directly from
`finiteK3Entry`; two Bool labels supply virtual ordinary columns.

    H = D-O
    B = [[A,G],[G^T,O+(D-O)/ell]]
    v = (1 on distinguished cells, ell on aggregate rows)

[FiniteK3Ordinary](../DR/Certificates/FiniteK3Ordinary.lean) proves the
literal physical seed reindexes to the full ordinary-column matrix.
Distinguished cells are row-major: (row,column) has index row*k+column.
The m aggregate rows follow. B0 retains the first m*k+m-1 indices, deleting
the last aggregate row. The aggregate kernel is checked directly as Bv=0;
no unproved compression of the source's seventeen full-seed equations is
needed for this sufficient criterion.

[PrincipalKernel](../DR/Certificates/PrincipalKernel.lean) proves that a
symmetric B, its nonzero omitted component of v, Bv=0, and B0 positive
definite give B positive semidefinite with quadratic kernel exactly Rv.
This is a statement about every real vector, including zero.

[FiniteK3OrdinaryKernel](../DR/Certificates/FiniteK3OrdinaryKernel.lean)
uses the exact identity

    p^T Q p = (x,z)^T B (x,z) + sum_j w_j^T H w_j,
    z = sum_j y_j,  w_j = y_j-z/ell.

H positive definite forces every w_j=0 at equality. The aggregate kernel
then makes x and all y_j the same constant. Thus the actual physical seed
is positive semidefinite and its quadratic kernel is exactly the constant
vectors. This sufficient direction requires ell>0; it makes no converse
claim when there is only one ordinary column.

## Rational checks and pair coverage

[FiniteK3OrdinaryFlat](../DR/Certificates/FiniteK3OrdinaryFlat.lean) proves
the precise principal embedding and rational-to-real cast identities.
[FiniteK3Physical](../DR/Certificates/FiniteK3Physical.lean) uses the actual
bijection `(Fin k ⊕ Fin (n-k)) ≃ Fin n` to restore physical columns. It
retains the strict n>k gate before using the nonzero aggregate component.

[ConstantKernel](../DR/Certificates/ConstantKernel.lean) transports PSD
and the exact quadratic kernel under bijective indexing.
[FiniteK3Pairs](../DR/Certificates/FiniteK3Pairs.lean) covers every pair by
independent row and column permutations, with representatives in this order:

| Index | Second cell after first cell (0,0) | Distinguished columns |
|---|---|---:|
| 0 | (0,0) | 1 |
| 1 | (0,1) | 2 |
| 2 | (1,0) | 1 |
| 3 | (1,1) | 2 |

No row/column transpose is substituted for the two different middle roles.
The final adapter invokes the proved signed quartic iid identity and
`finiteK3_uniformMaximizer`. Nonnegative mass-one weights ensure a positive
diagonal pair even on a support face. Its exact constant kernel forces
uniform equality, with no positive-cell or positive-marginal assumption.

## Replay and scope

Run:

```sh
lake build Test.PrincipalKernel Test.FiniteK3Ordinary \
  Test.FiniteK3Physical Test.FiniteK3EnvelopeSoundness
```

The combined replay passed 2,463 jobs and fourteen axiom audits, each
reporting only `propext`, `Classical.choice`, and `Quot.sound`.

The tests retain the unequal aggregate kernel vector, row-major indexing,
empty ordinary-column identities and the strict nonempty requirement.
An actual three-cell star seed tests the complete physical PSD and exact
kernel bridge independently of the quartic equations. Replacing its
ordinary-column count by one fails the kernel equation. The end-to-end
4-by-6 test derives `UniformMaximizer 4 6 3` from the literal checked
`M4N6.valid`, obtains sharp value 13/18, and separately checks the signed,
unnormalized quartic identity.

The later complete replay has now checked every one of the 1,330 catalogue
entries and all 87 coverage shards. The [complete K=3 assembly](ORDER-THREE-COMPLETE.md)
applies this soundness theorem to every finite gap and joins the infinite
ranges. See the [replay receipt](../data/FINITE_K3_COMPLETE_REPLAY.md) for
coverage and the [certificate account](FINITE-K3-CERTIFICATES.md) for the identities.
