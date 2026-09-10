# Actual transition row-variance bootstrap

`TransitionBootstrap.lean` proves Section 4 of the accepted Lab
`ENDPOINT_ALL_ASPECT_RATIOS_LARGE_M.md`, on exactly the transition domain
`m>=10^18`, `m<=n`, `m*(m-1)<=20*n`, `n<=10000*m^2`.

The proved actual contender relation gives

```
1-pi <= (b-p_original)/(1-p_original).
```

The original-row avoidance comparison, `p_original<=b`, and
`1-b>=1/40001` imply the ratio is at most
`40001*(7000000000/m)<1/2000`. All denominators remain positive and the
exponential error follows from `exp(-u)>=1-u`.

The earlier finite-product logarithm bound then proves the actual
scaled-row estimate

```
sum (m*rowSum_i-1)^2 < 1/100.
```

The theorem assumes no positive entries, stationary condition, prescribed
row shape or endpoint gauge. It concerns every full-probability contender
on the closed simplex. Subsequent column deletion must introduce its own
normalized row law and its own avoidance probability.

Replay: `lake build Test.TransitionAvoidance Test.TransitionBootstrap`
passed 3174 jobs with eight standard-only axiom audits and no warnings.
Tests retain zero exponential error, reject an omitted avoidance comparison
and a removed denominator, check exact threshold constants, and instantiate
the full actual-matrix statement at nonempty transition dimensions.

This completes the transition row estimate. The final deletion/kernel and
optimization assembly remain separate from this theorem.
