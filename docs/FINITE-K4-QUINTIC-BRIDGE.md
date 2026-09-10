# From finite quintic equations to the actual probability

The coefficient and matrix identities connect to the original four-sample
probability on the entire closed simplex. Positivity is proved separately
from coefficient matching and then applied in the
[four-row theorem](FOUR-ROW-PROOF.md) and the
[fixed-board theorems](FIXED-BOARD-ORDER-FOUR.md).

## Literal coefficient meaning

[QuinticSampling](../DR/Certificates/QuinticSampling.lean) proves the signed
iid permutation identity, including empty outcome types and sample size zero.
[FiniteK4QuinticChoice](../DR/Certificates/FiniteK4QuinticChoice.lean)
uses the ten increasing choices of three positions among five; each choice
is followed by its two complementary positions. Every resulting order is
bijective. The deletion indicator uses the inclusive OR of distinct rows
and distinct columns on the four retained positions.

The multiplier correction is 6, 2, 1 for a triple with one, two, or three
distinct cells. Equality of a row alone does not identify two cells.
[WeightedTriple](../DR/Certificates/WeightedTriple.lean) supplies the
corresponding ordered-triple weights 1, 1/3, 1/6. These retain literal repeated
cells rather than assuming the five sampled outcomes are distinct.

[The generated data](../DR/Certificates/FiniteK4QuinticData.lean) contains
91 sparse monomial equations on 407 complete coefficient roles and the 52
row and 52 column equality patterns. Each sparse row is padded to ten slots
with zero coefficients. For each physical pattern the finite gates check:

- all ten actual role indices and repeated-cell weights;
- each selector's role and the weight sum of every selector fiber;
- the actual sum of the five deleted-success indicators;
- the exact integer relation between multiplicity and source successes.

If M is the positive monomial multiplicity, the selector identity is
`M * sum(choice weights in slot j) = 60 * source coefficient in slot j`.
The success identity is `12*M*sum(deleted success) = 60*source successes`.
[FiniteK4QuinticLocal](../DR/Certificates/FiniteK4QuinticLocal.lean)
therefore transfers one actual sparse equation to the ten-choice physical
identity by cancelling M. No division by matrix mass occurs.

## Actual homogeneous identity and equality

[FiniteK4QuinticSampling](../DR/Certificates/FiniteK4QuinticSampling.lean)
proves, for arbitrary signed real P with total mass S,

```
alpha*S^5 - S*F4(P)
  = sum_t weight(t) * product_i P(t_i) * quadraticValue(Q_t,P).
```

Here t ranges over actual ordered cell triples and Q_t is the matrix defined
by the literal 407-role coefficient function at t and the quadratic pair.
The ten choices contribute 60 times this sum. Each deleted-success term
integrates to `S*F4(P)`. These facts prove the displayed identity directly;
it is valid also at S=0 and on empty rectangles.

[FiniteK4Soundness](../DR/Certificates/FiniteK4Soundness.lean) uses PSD of
every actual Q_t and a constant kernel for repeated-cell triples to obtain
the sharp uniform inequality with exact equality on the closed simplex.
Mass one guarantees a positive cell; its repeated triple detects the
constant kernel even when other entries are zero.

## Four-row parameter families

[FiniteK4QuinticRows](../DR/Certificates/FiniteK4QuinticRows.lean) checks the
exact 91 padded lists, the 84 source rows and their 391-to407 role mapping.
Every physical tuple on four rows belongs to that 84-equation subset. The
adapter evaluates the separately verified rational numerator identities
and proves the real coefficient equations for `c=h(u)/u`, retaining `u≠0`.
A negative parameter is permitted by this algebraic adapter; positivity
of the blocks is a separate closed-interval fact.

[FourRowFiniteProbability](../DR/Rectangular/FourRowFiniteProbability.lean)
substitutes `u=a/N`, proves that the polynomial target is exactly the sharp
uniform probability, and derives both physical identities for every `N≥4`.
The matrix positivity intervals remain `5≤N≤50` and `50≤N≤500`.

[The fixed seed equations](../DR/Certificates/FiniteK4FixedSeedEquations.lean)
check all 182 rational equations for 5-by-5 and 20-by-20.
[FiniteK4FixedSeedProbability](../DR/Certificates/FiniteK4FixedSeedProbability.lean)
identifies their sharp constants as `5424/15625` and `14805351/16000000` from
the actual uniform probability definition. The seed vectors include negative
coefficients; the separate PSD and kernel proofs remain necessary.

## Physical matrix coverage

[FiniteTripleSeeds](../DR/Certificates/FiniteTripleSeeds.lean) checks all 25
pairs of three-position equality patterns and covers them by ten literal
multiplier triples. Its relabelings are permutations of the actual finite
row and column hosts. Repeated positions and hosts with no spare labels
are included.

[FiniteK4SeedTransport](../DR/Certificates/FiniteK4SeedTransport.lean)
proves symmetry of the actual matrix, invariance under multiplier-position
permutations and physical matrix conjugacy. PSD and the exact constant
kernel of the ten physical seed matrices therefore transfer to every
actual multiplier triple when both dimensions are at least three.

The [two-axis decomposition](../DR/Certificates/TwoAxisOrdinaryDecomposition.lean)
and [kernel theorem](../DR/Certificates/TwoAxisOrdinaryKernel.lean)
reduce these seed matrices to four actual sectors with aggregate weights
1, C, R, R*C. A standard or interaction sector is omitted only when its
fluctuation space is identically zero. Present standard sectors require
positive definiteness for the constant-kernel conclusion.

## Verification controls

Persistent tests include signed and empty iid laws, a missing total-mass
factor, lost repeated-cell weights, padding fibers, u=0, literal host
permutations, and a negative singleton matrix showing that coverage alone
is not PSD. The two-axis tests include negative absent sectors and a
counterexample to weakening a present standard sector from PD to PSD.

The finite gate generator splits the 52 proof rows across eight modules.
Each module checks every column in its rows by Lean kernel reduction.
The generator checks and their corruption controls also run under Python
`-O`; [Verification](VERIFICATION.md) gives the complete commands.
