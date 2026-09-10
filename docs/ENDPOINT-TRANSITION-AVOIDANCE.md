# Refined original-row avoidance on the transition range

`TransitionCollisionScalars.lean`, `TransitionCollisionBounds.lean`, and
`TransitionAvoidance.lean` prove Sections 2–3 of the accepted Lab
`ENDPOINT_ALL_ASPECT_RATIOS_LARGE_M.md` on exactly

```
10^18<=m, m<=n, m*(m-1)<=20*n, n<=10000*m^2.
```

For every actual full-probability contender, the normalized original-row
law has local collision load at most `6200000/m` and total intensity at
most `s+3200000001/m`, where `s=m^2/(2n)<=20`. The intensity estimate keeps
the reciprocal-row correction derived earlier; replacing it by the rough
minimum row would lose this estimate.

The already-proved finite local lemma supplies positivity and
`-log p_original<=D/(1-5d)`. Exact real arithmetic with the retained
positive denominator gives `-log p_original<=s+6000000000/m`. Combining
this with the actual uniform probability upper bound proves

```
b * exp(-7000000000/m) <= p_original.
```

Only an upper bound on `b` is used; no lower approximation to `log b` is
assumed. This entire chain concerns `originalRowAvoidance P`. No deleted
board or deleted-row avoidance probability is substituted.

Replay: `lake build Test.TransitionAvoidance`. Combined with the bootstrap
test, the completed package passed 3174 jobs and eight standard-only axiom
audits, without warnings. Tests include exact worst-case scalar arithmetic,
failed dropped reciprocal/denominator corrections, the nonempty dimension
pair `m=10^18,n=10^36`, and the full actual-contender signature.

These are probability inputs. They do not themselves assert a full
transition maximizer theorem or cover all endpoint aspect ratios.
