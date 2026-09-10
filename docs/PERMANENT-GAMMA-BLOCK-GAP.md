# Factor-two permanent gap for two nonempty blocks

For all positive integers k,l, `dittertConstant_mul_ge_twice` proves
`2 gamma_(k+l)<=gamma_k gamma_l`, where `gamma_n=n!/n^n`.

Expand `(k+l)^(k+l)` by the binomial theorem and retain the terms at
k−1,k,k+1. Relative to the central term, the two neighbors have factors
l/(l+1) and k/(k+1). Both are at least one half. Exact choose recurrences
and factorial cancellation yield the claim. The omitted binomial terms
are nonnegative; no asymptotics or dimension sampling is used.

The constant two is sharp at k=l=1. Both blocks must be nonempty: taking
k=0,l=1 is an explicit counterexample. This scalar statement is a
prerequisite for excluding decomposable permanent minimizers on the
two-zero face; it does not by itself prove a matrix support assertion.

`Test.GammaBlockGap` checks six examples and four standard-only axiom
audits, including sharp equality, unequal block sizes, exact neighboring
terms, and rejection of both an empty block and a strengthened factor.
