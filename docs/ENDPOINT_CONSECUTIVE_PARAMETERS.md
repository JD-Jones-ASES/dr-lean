# Consecutive endpoint tail from 30 rows

`uniform_maximum_consecutive_endpoint_of_thirty_le` proves the sharp
endpoint inequality with unique uniform equality on `m×(m+1)` and its
transpose for every `m≥30`. The entire closed probability simplex is
included. Together with the [finite cut bounds for 19≤m≤29](ENDPOINT_CONSECUTIVE_CUTS.md),
this proves the consecutive endpoint theorem for every m≥19.

The sufficient arithmetic criterion reduces to a scalar sequence. Put

```
W(m)=m^5(m+1)^3 gamma_(m+1)+m^6(m+1)^2 gamma_m.
```

The exact identity `b(m,m+1)=(m+1)gamma_(m+1)` makes the gain-one
criterion precisely `W(m)<512/289`. Lean verifies the rational base
`W(30)<(3/4)(512/289)`.

For every `m≥30`, the factors `m` and `m+1` grow by at most `31/30`
at the next dimension. Hence any weight of total degree eight grows by
at most `(31/30)^8<2`. The proved factorial bound halves each
gamma factor at the next dimension, proving `W(m+1)≤W(m)`. Actual
induction propagates the exact base to every larger integer. This
common degree-eight growth bound is sufficient for both summands of W.

## Formal statements

[ConsecutiveParameters](../DR/Endpoint/ConsecutiveParameters.lean), [ConsecutiveLarge](../DR/Endpoint/ConsecutiveLarge.lean).
