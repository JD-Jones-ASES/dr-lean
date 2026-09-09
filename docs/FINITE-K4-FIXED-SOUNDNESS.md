# Fixed K4 seed matrix soundness

[FiniteK4FixedSoundness](../DR/Certificates/FiniteK4FixedSoundness.lean)
connects the actual rational coefficient sectors to full-simplex K4
maximization for boards with both dimensions at least five. The literal
5-by-5 and 20-by-20 gates are discharged separately; this generic theorem
keeps their exact finite obligations visible.

For each of the ten physical multiplier triples, the coefficient vector
specifies an actual relation matrix on distinguished and ordinary labels.
[FiniteK4FixedBlocks](../DR/Certificates/FiniteK4FixedBlocks.lean) defines
its compressed full, principal, row-standard, column-standard and interaction
matrices. The row and column counts are the actual integer differences
`R=m-nr` and `C=n-nc`. The lexicographic compressed weights are `1,C,R,R*C`.
Rational-to-real casts and the sector reindexings are exact theorems.

The principal block removes only the final ordinary/ordinary coordinate.
Its weight R*C is strictly positive. Symmetry, the full matrix's exact
weighted kernel and positive definiteness of the principal block therefore
imply PSD of the full compressed matrix and precisely the span of its weight
vector as quadratic kernel. The exact two-axis decomposition then transfers
this to the whole physical seed matrix. Both ambient dimensions are at
least five, while each multiplier uses at most three labels; thus all
standard sectors are present and require strict positivity.

Actual host conjugacy and the ten-seed coverage theorem extend the matrix
criterion to every multiplier triple. Finally the sharp 91 coefficient
equations and the signed homogeneous identity imply the probability bound
and iff uniform equality on the closed nonnegative simplex. Repeated-cell
triples detect constant kernels even when other matrix entries vanish.

The API `finiteK4Fixed_uniformMaximizer` asks for exactly ten weighted
kernel equations, ten positive principal blocks, ten row-standard blocks,
ten column-standard blocks and ten positive interaction scalars, together
with the sharp coefficient equations. No desired global inequality is
assumed. The fixed-board final declarations must discharge all these gates.

[Persistent tests](../Test/FiniteK4FixedSoundness.lean) verify the omitted
weights 4 and 289, a negative actual matrix despite a valid role lookup,
and nonzero weights at every index. The targeted build passed 3,239 jobs
with five examples, six standard-only axiom audits and no warnings. The
full soundness chain received an independent semantic review.
