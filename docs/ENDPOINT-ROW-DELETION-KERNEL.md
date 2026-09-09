# Actual endpoint kernel conjugacy

`DR/Endpoint/RowDeletionKernel.lean` proves P0174
`ENDPOINT_LOCALIZED_COLLISION_KERNEL.md`, equation (1), and
`ENDPOINT_LLL_STRIP.md`, equation (12), directly from the actual rook sum
and independent row law.

Writing r for row masses and h for a nonzero scale, it proves

```
(r_i/h)(r_j/h) C_ij
 = E (r_i/h)(r_j/h) - gamma E[L_ij],
gamma = product(r_i)/h² = h^(m-2) product(r_i/h).
```

Here C is the existing `averagingKernel P (m-2)`, E is its actual
elementary-symmetric coefficient, and L is the zero-diagonal deletion
matrix sampled under `normalizeRows P`. Thus the kernel being bounded
is the one in the exact full-probability column-blending identity.
There is no factorial in gamma. The separate full-probability blend
formula retains its already-proved m! multiplier.

The row-mass and normalized-entry identities require nonzero row masses;
the scale is also explicitly nonzero. The algebra accepts signed masses
and signed vectors. The gamma power identity states m≥2, while the
entry identity retains empty and singleton row hosts whenever its inputs
exist. Applying the theorem to a column-deleted board uses that board's
own normalized law.

Replay: `lake build Test.RowDeletionKernel`. Tests retain the zero diagonal,
the event after deleting both rows of a two-row host, non-unit and signed
normalization scales, and a rejected omitted-denominator mutation.
The actual quadratic identity is available for the positive-kernel
criterion; no new endpoint dimension range follows from normalization alone.
