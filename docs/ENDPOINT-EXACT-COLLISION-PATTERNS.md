# Literal doubleton, tripleton and two-doubleton probabilities

Let X be a nonnegative matrix whose rows each sum to one. Draw one
column independently from each row, and suppose each row’s sum of pair
collision probabilities is at most 1/8. Then the exact collision-pattern
probabilities satisfy

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

Summing these exact pattern bounds gives the
[localized collision loads](ENDPOINT-LOCALIZED-COLLISION-LOADS.md).
Their [incidence identities](ENDPOINT-PARTICIPATION-LOCALIZATION.md)
then place them in the expected two-row deletion matrix. Each application
uses the original or retained board’s own normalized row law.

## Formal statements

[RowCollisionClasses](../DR/Endpoint/RowCollisionClasses.lean), [RowCollisionTwoClasses](../DR/Endpoint/RowCollisionTwoClasses.lean).
