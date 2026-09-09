# The collision-local endpoint strip

`DR/Endpoint/LLLStrip.lean` exports the fixed release declaration
`DittertRybin.uniform_maximum_lll_endpoint`, proving both
`UniformMaximizer m n m` and `UniformMaximizer n m m` under exactly

```
128 <= m
m <= n
4096*m^3 <= n^2
20*n <= m*(m-1).
```

These are the accepted Lab `ENDPOINT_LLL_STRIP.md` dimensions
`64*m^(3/2)<=n<=m*(m-1)/20`.
`DittertRybin.endpoint_lll_lower_edge_iff` in `LLLStripDomain.lean`
proves the exact real-power/integer equivalence by nonnegative squaring
and the real-power identity `(m^(3/2))^2=m^3`, including `m=0`.
The core theorem derives `m<=n`; the release wrapper retains it explicitly. The interval is nonempty, for example at
`m=2^22,n=2^39`, but is not claimed nonempty at every nominal row count.
The transposed theorem is also proved. Both retain arbitrary nonnegative
entries, mass one, the exact sharp value

```
a_m + (1-a_m)*(n)_m/n^m,  a_m=m!/m^m,
```

and equality if and only if the board is uniform.

## Actual proof chain

1. Full-probability contender inequalities and the exact uniform avoidance
   product force scaled-row squared deviation below `1/1024` and column
   masses below `2/n`.
2. Deleting any two columns leaves mass above `15/16`, positive rows, and
   normalized row squared deviation below `1/81`. The retained board's own
   independent normalized-row law has column cap `C=4m/n` and `m*C^2<=1/256`.
3. The finite conditional local lemma proves positive actual no-collision
   probability. The proved exact one-doubleton, tripleton, and two-doubleton
   ratios supply all three localized collision bounds. Total collision
   intensity need not be small.
4. The exact injection-successor lower bound gives the elementary coefficient
   floor, with the correct `(m-2)!` normalization. Closed-simplex Maclaurin
   and the all-dimension factorial guard yield the fifth scalar bound.
5. Actual deleted-row rook normalization identifies the blend kernel,
   retaining its scale `product(rowSum)/h^2` and its own avoidance probability.
   The proved `3/32` square-completion criterion gives positive definiteness.
6. The literal midpoint blend identity forces every global maximizer's columns
   to agree. The independent one-sided endpoint rigidity adapter computes
   the resulting product-board probability and applies exact Maclaurin
   equality to force the uniform board. Compactness supplies existence.

The source's retained norm bound `1/10` is replaced by a proved squared
bound `1/81`, still strictly below the criterion's `1/9`. This changes no
dimension assumption or final theorem.

## Attribution and verification boundary

The accepted mathematical argument and collision-pattern specialization
are the local P0174 Lab work. Published probabilistic antecedents are the
conditional local-lemma framework in Haeupler, Saha, and Srinivasan,
*New Constructive Aspects of the Lovasz Local Lemma*, arXiv:1001.1231v5,
Theorems 1.1 and 2.1. The finite conditional argument is proved here from
finite weighted sums and actual row independence; no external probability
or endpoint theorem is imported as an axiom. Mathlib supplies standard
finite algebra, real analysis, compactness, and matrix theory.

The foundational probability, deletion, normalization and strip assembly
were formalized by the collision-foundation agent. The root agent supplied
the exact scalar/matrix square completion, elementary coefficient lower
bound, factorial guard, and one-sided column-rigidity closure. Mathematical
interfaces receive independent semantic review before integration.

Replay: `lake build Test.LLLStrip Test.LLLStripDeletion Test.EndpointCoefficient`.
The principal tests retain the nonempty integer instance, transpose, explicit
closed-simplex sharp-value iff, actual contender-kernel signature, and a
vacuous-range control. The supporting tests retain zero entries, unequal
mass/deletion, signed exact identities, and failed normalization/conditioning
mutations. All proof checks use the ordinary Lean kernel. Independent CI for
an integrated exact commit remains a separate root-maintained release gate.

This is one complete endpoint range. It is neither the all-aspect-ratio
endpoint theorem nor full rectangular P2, and it does not change the scope
of any remaining target.
