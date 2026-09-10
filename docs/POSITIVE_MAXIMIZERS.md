# Closing the endpoint after boundary exclusion

`DR/Endpoint/PositiveMaximizers.lean` proves
`uniform_maximizer_of_all_global_positive`: for `2 ≤ k ≤ min(m,n)`, if
every global maximizer of the actual iid separation probability on the
closed probability simplex has positive entries, uniform is its unique
global maximizer. The sharp inequality and its equality case apply to
every nonnegative probability board, including zero entries.

The hypothesis concerns **all** global maximizers. The conclusion follows
by choosing a greatest-norm member of that compact set and using reverse
averaging. Boundary exclusion supplies the positivity hypothesis in each
unconditional endpoint application.

## Proof

1. The full global-maximizer set is a nonempty compact level set of the
   continuous separation probability. Choose a member `Q` with greatest
   squared Frobenius norm.
2. By the hypothesis, every entry of `Q` is positive. For each column
   pair there is an actual feasible negative blend parameter `t < 0`.
   A common positive entry floor and the probability entry bound `≤ 1`
   supply this parameter explicitly.
3. The already proved generic same-support averaging identity makes the
   objective exactly constant for every real `t`, including this negative
   parameter. The new signed norm identity is
   `norm²(blend_t Q) = norm²(Q) - 2t(1-t) Σ_i(Q_ia-Q_ib)²`.
   Greatest norm therefore forces every column pair to coincide.
4. Transposition preserves the objective, simplex, and squared norm. The
   same choice of `Q` also has equal rows, and its mass makes it uniform.
5. Every other global maximizer has norm at most that of `Q`. The exact
   centered-square identity on the full simplex says uniform uniquely
   minimizes this norm, so all global maximizers are uniform.

This compactness argument proves only the implication stated above.
It does not assume a pointwise theorem identifying an arbitrary positive
maximizer. For the classical square positive-maximizer result of Suk Geun
Hwang and its relation to Dittert's conjecture, see the Cheon–Wanless
reference in [Sources](SOURCES.md).

## Verification

Run `lake --wfail build Test.PositiveMaximizers`. Tests include a feasible
negative blend with its exact increased norm, the midpoint and swapping
parameters, an empty row type, a boundary board where reverse averaging
is impossible, the full closed-simplex norm equality, and an independent
order-two instantiation. Eight public dependency audits permit only the
standard Lean axioms. No target conclusion is supplied as an axiom.
