# Consecutive endpoint tail from 30 rows

`uniform_maximum_consecutive_endpoint_of_thirty_le` proves the sharp
endpoint inequality with unique uniform equality on `m×(m+1)` and its
transpose for every `m≥30`. The entire closed probability simplex is
included. This is the infinite tail of the accepted `m≥19` target;
the finite cases `19≤m≤29` remain a separate obligation.

The scalar source is the consecutive-dimension corollary in the Lab's
`P0174_rybin_semimatchings/PANG_RECTANGULAR_ENDPOINT.md`. Put

```
W(m)=m^5(m+1)^3 gamma_(m+1)+m^6(m+1)^2 gamma_m.
```

The exact identity `b(m,m+1)=(m+1)gamma_(m+1)` makes the gain-one
criterion precisely `W(m)<512/289`. Lean verifies the rational base
`W(30)<(3/4)(512/289)`.

For every `m≥30`, the factors `m` and `m+1` grow by at most `31/30`
at the next dimension. Hence any weight of total degree eight grows by
at most `(31/30)^8<2`. The already proved factorial bound halves each
gamma factor at the next dimension, proving `W(m+1)≤W(m)`. Actual
induction propagates the exact base to every larger integer. This
common growth bound replaces the source's separate inverse-ratio bounds
without altering the range or criterion.

Run `lake --wfail build Test.ConsecutiveParameters`. The seven examples
include the adjacent-factor normalization, an all-m induction application,
both orientations at the base, full closed-simplex equality, and exact
failure of the coarse criterion at `m=29`. That failure is not a P2
counterexample; the separate active-cut proof is needed there. Seven
axiom audits expose only the standard Lean axioms.
