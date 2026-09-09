# Exact logarithmic collision bound

[RowCollisionLogBound](../DR/Endpoint/RowCollisionLogBound.lean) proves
equation (10) of the accepted Analytic-Lab P0174 note
`ENDPOINT_ALL_ASPECT_RATIOS_LARGE_M.md`:

```
-log(rowAvoidance X) <= rowCollisionIntensity X / (1-5*d),
exp(-rowCollisionIntensity X / (1-5*d)) <= rowAvoidance X.
```

The hypotheses are actual nonnegative independent row distributions,
each row of mass one, `0 <= d <= 1/8`, and every row collision load at most
`d`. The total collision intensity is unrestricted. The result applies to
the original row law or to a separately normalized deleted law without
identifying their avoidance probabilities.

The proof uses the already proved refined local-lemma product from
[RowCollisionLocalLemma](../DR/Endpoint/RowCollisionLocalLemma.lean), the
exact increasing-edge sum for the intensity, and Mathlib's scalar
`Real.one_sub_inv_le_log_of_pos`. The scalar logarithm inequality is
summed over the actual edges. All factors and denominators are proved
positive. The exact algebra produces `1-5*d`; this denominator is not
dropped or replaced by an asymptotic approximation. Zero events and
`d=0` remain included.

Verification: `lake build Test.RowCollisionLogBound` passed 2,113 jobs,
with four standard-only axiom audits. Persistent controls cover the zero
scalar boundary, mixed zero and positive parameters, empty row laws,
the exponential corollary at the closed local threshold, and the false
claim obtained by dropping the logarithmic denominator. The actual
33-row test with total intensity greater than one remains in the
upstream local-lemma test.

This supplies the continuous probability input to the transition
argument. It does not yet prove the source's subsequent uniform
benchmark comparison, contender concentration improvement, positive
blend matrix, or any new endpoint range.
