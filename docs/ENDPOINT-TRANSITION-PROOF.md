# Full endpoint P2 on the transition interval

`DR/Endpoint/Transition.lean` proves

```
DittertRybin.uniform_maximum_transition_endpoint
  (hm : 10^18<=m) (hmn : m<=n)
  (hlower : m*(m-1)<=20*n) (hupper : n<=10000*m^2) :
  UniformMaximizer m n m ∧ UniformMaximizer n m m.
```

This is precisely the closed transition interval
`m*(m-1)/20<=n<=10000*m^2` in the accepted Lab
`ENDPOINT_ALL_ASPECT_RATIOS_LARGE_M.md`. Both orientations retain arbitrary
nonnegative entries, total mass one, and equality if and only if the board
is uniform. The sharp value is `a_m+(1-a_m)*(n)_m/n^m`.

## Original and deleted row laws

The original board first supplies the full contender relation
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

## Attribution and verification boundary

The accepted transition argument and collision specialization are local
P0174 Lab work. The published probabilistic antecedents are Haeupler, Saha
and Srinivasan, *New Constructive Aspects of the Lovasz Local Lemma*,
arXiv:1001.1231v5, Theorems 1.1 and 2.1; the finite conditional probability
argument itself is proved in this project. Mathlib supplies standard finite
algebra, real analysis, compactness and matrix theory.

The collision-foundation agent formalized the actual probability,
normalization, transition estimates and assembly. The root agent supplied
the scalar/matrix square completion, sequential elementary coefficient
lower bound, factorial guard and one-sided product-equality closure.
Independent semantic review and exact-commit CI are separate integration
gates maintained by the root.

Verification: `lake build Test.Transition Test.TransitionDeletion` passed
3318 jobs, with twelve standard-only axiom audits and no warnings. Tests include
both closed interval endpoints at `m=10^18`, both orientations, the explicit
sharp-value iff on the full closed simplex, an actual contender-kernel
signature, the looser transition row budget, and a genuine one-column
boundary case for the generic optimization adapter. All proof checking uses
the ordinary Lean kernel.

This completes the transition interval. It does not alone establish all
endpoint aspect ratios: the arithmetic lower strip and quadratic upper
strip, and their exact overlaps with the LLL strip, remain separate inputs
to the all-aspect release target.
