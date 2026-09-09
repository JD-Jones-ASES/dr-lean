# Literal doubleton, tripleton and two-doubleton probabilities

[RowCollisionClasses](../DR/Endpoint/RowCollisionClasses.lean) and
[RowCollisionTwoClasses](../DR/Endpoint/RowCollisionTwoClasses.lean) prove
the three estimates in Analytic-Lab P0174
`ENDPOINT_RELATIVE_COLLISIONS.md`, equation (1), for actual independent row
assignments. With nonnegative normalized rows and every collision load at
most `1/8`, the results are

```
Pr(exact doubleton {i,h}) / p0 <= (16/9) p_ih,
Pr(exact tripleton {i,h,l}) / p0 <= (64/27) sum_j X_ij X_hj X_lj,
Pr(exact disjoint doubletons e,f) / p0 <= (256/81) p_e p_f,
```

where `p0` is the proved positive `rowAvoidance X`. The last theorem
requires the two pairs to have disjoint row sets; the triple theorem
requires three distinct rows.

The event definitions are literal. Rows in each prescribed class choose
the same column, and every edge outside the internal class edge sets is
forbidden. For two classes, cross-class edges are outside the internal
sets and are therefore forbidden. Thus the exact numerator excludes an
accidental merger of the two prescribed classes and all additional
collisions among other rows.

The common-column moment of a nonempty selected row class is proved by
partitioning its actual event according to the common column. The
probability of the prescribed equalities in two disjoint classes factors
by actual complementary-row product splitting. These algebraic identities
permit signed normalized row weights. Nonnegativity is required when
applying the local-lemma ratio theorem. The nonempty condition in the
common-column identity is explicit and necessary.

Verification: `lake build Test.RowCollisionClasses` passed 2,192 jobs with
eight standard-only axiom audits and no warnings. A three-row model at
the closed `1/8` local-load threshold has exact positive tripleton mass
`1/64`. The tests show that overlapping pair classes do not factor
(`1/64` differs from `1/256`), reject a repeated-row disjointness gate,
and expose the false empty-class common-column formula. The actual
two-doubleton theorem is tested on four distinct row indices with its
full probability functional.

This freezes the exact pattern-ratio input. Summing these patterns into
the localized penalties and completing the collision-matrix argument
remain separate proof obligations. No new endpoint dimension range is
claimed here, and original and deleted row laws remain distinct.
