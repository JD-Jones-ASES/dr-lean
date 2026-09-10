# Exact logarithmic collision bound

For an independent normalized row law X, let D be its total unordered
pair-collision intensity and p0 its probability of choosing distinct columns.
If every incident row load is at most d, then

```
-log(rowAvoidance X) <= rowCollisionIntensity X / (1-5*d),
exp(-rowCollisionIntensity X / (1-5*d)) <= rowAvoidance X.
```

The hypotheses are actual nonnegative independent row distributions,
each row of mass one, `0 <= d <= 1/8`, and every row collision load at most
`d`. The total collision intensity is unrestricted. The result applies to
the original row law or to a separately normalized deleted law without
identifying their avoidance probabilities.

The proof uses the proved refined local-lemma product from
[RowCollisionLocalLemma](../DR/Endpoint/RowCollisionLocalLemma.lean), the
exact increasing-edge sum for the intensity, and Mathlib's scalar
`Real.one_sub_inv_le_log_of_pos`. The scalar logarithm inequality is
summed over the actual edges. All factors and denominators are proved
positive. The exact algebra produces `1-5*d`; this denominator is not
dropped or replaced by an asymptotic approximation. Zero events and
`d=0` remain included.

## Formal statements

[RowCollisionLogBound](../DR/Endpoint/RowCollisionLogBound.lean).
