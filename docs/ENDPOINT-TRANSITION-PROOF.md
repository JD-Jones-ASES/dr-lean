# Full endpoint P2 on the transition interval

For an m×n nonnegative matrix P of total mass one, let F_k(P) be the
probability that k independent cell draws have distinct rows or distinct
columns, with inclusive OR. Write U_ij=1/(mn) and (n)_m=n(n−1)…(n−m+1).
At the endpoint k=m, put a=m!/m^m and b=(n)_m/n^m. The sharp statement is
F_m(P)≤a+b−ab, with equality if and only if P=U. A contender means a
probability board satisfying F_m(P)≥F_m(U).

`DR/Endpoint/Transition.lean` proves

```
DittertRybin.uniform_maximum_transition_endpoint
  (hm : 10^18<=m) (hmn : m<=n)
  (hlower : m*(m-1)<=20*n) (hupper : n<=10000*m^2) :
  UniformMaximizer m n m ∧ UniformMaximizer n m m.
```

Thus the closed column interval is m(m−1)/20≤n≤10000m².
Both orientations include every nonnegative matrix of total mass one,
and equality holds exactly at uniformity. The sharp value is
a_m+(1−a_m)(n)_m/n^m, where a_m=m!/m^m.

## Original and deleted row laws

Let π=∏_i(m r_i), and let p_original be the probability of distinct
columns under one independent draw from each normalized original row.
The original board supplies the contender relation
`pi*(1-p_original)>=1-b`. Coarse row and reciprocal-deviation estimates
then bound its actual collision graph. The refined finite local lemma
compares `p_original` to `b`, giving product deficit `<1/2000` and original
scaled-row squared deviation `<1/100`.

For each pair of columns, the proof then constructs the actual retained
board `T`. It derives positive retained row masses, mass `h>15/16`, and
normalized retained row squared deviation `<1/9`. It separately normalizes
`T` by its own row masses, derives its column-load square bound, and invokes
the local lemma anew to obtain `p_deleted>0`. The two avoidance laws are
never equated or substituted.

The exact pattern ratios for the deleted law give mean pair, centered
pair and deficit-two bounds. The elementary-symmetric lower bound gives
`E/(gamma*p_deleted)>=4m^2`, where `gamma=product(rowSum T)/h^2` without
an extra factorial. Actual rook normalization and the `3/32` square
completion then prove the literal retained blending kernel positive definite.

`EndpointKernelClosure.lean` applies the exact midpoint blend identity to
force equal columns at a global maximum. The independent one-sided endpoint
column-rigidity theorem then computes the product-board probability and uses
closed-simplex Maclaurin equality to force the uniform board. Compactness
supplies existence. The transpose argument preserves both the exact value
and matrix equality.

## Mathematical references

The conditional local-lemma framework is due to Haeupler, Saha and
Srinivasan, [New Constructive Aspects of the Lovasz Local Lemma](https://arxiv.org/abs/1001.1231v5),
Theorems 1.1 and 2.1. The finite argument here derives the conditional
product bound from finite weighted sums and independence of disjoint
row coordinates.

## Formal statements

[Transition](../DR/Endpoint/Transition.lean), [EndpointKernelClosure](../DR/Endpoint/EndpointKernelClosure.lean), [TransitionDeletion](../DR/Endpoint/TransitionDeletion.lean).
