# The one-zero permanent floor and quantitative ratio

For every doubly stochastic real n by n matrix A with at least one zero,
`permanent_boundary_lower_bound` proves

    per(A) >= mu_n = (n-2)! * ((n-2)/(n-1)^2)^(n-2), n>=3.

No positivity of the other entries is required. This is the Knopp--Sinkhorn
boundary floor used in the accepted rectangular scaling argument. The exact
source checked here is [Pang, arXiv:2606.01531v1, Lemma 1 and equations (8)--(12)](https://arxiv.org/html/2606.01531v1). Pang states the boundary theorem for n>3
and cites the corollary following Knopp and Sinkhorn, *Minimum permanents of
doubly stochastic matrices with at least one zero entry*, Linear and
Multilinear Algebra 11 (1982), 351--355,
[DOI](https://doi.org/10.1080/03081088208817459). The original full paper was
not an input to this formalization.

The Lean proof derives the floor from the repository's proved capacity
foundations. Row and column permutations place the chosen zero at (0,0).
The first-deletion entropy product then has a factor one at that row; Jensen
on the remaining n-1 entries gives G(n-1). The actual reduced polynomial's
homogeneous capacity bound supplies gamma_(n-1), where gamma_k=k!/k^k.
Their product is exactly mu_n, and also equals
gamma_(n-1)^2/gamma_(n-2). This proves the full n>=3 domain directly, including
the additional small boundary case, without assuming the published floor.

Writing kappa_n=mu_n/gamma_n, `boundaryPermanentRatio_gap` proves

    (kappa_n-1)/kappa_n^2 > (16/17)^2 / (3*(n-1)^2), n>=18.

The exact algebraic formula matches Pang's equation (8). The internal proof
of kappa_n-1>1/(3*(n-1)^2), valid for n>=4, replaces the source's logarithmic
series by an inductively proved cubic Bernoulli lower bound. The induction
remainder is m(m-1)(m-2)t^4/6, hence nonnegative for m>=2. Substitution
t=1/(n-1)^2 leaves an explicit strictly positive rational remainder.
Finally kappa_n<(n-1)/(n-2)<=17/16 gives the stated ratio estimate.

Production modules are `DR/Endpoint/BoundaryPermanent.lean` and
`DR/Endpoint/BoundaryPermanentRatio.lean`. `Test/BoundaryPermanent.lean`
checks a sharp actual n=3 boundary matrix, exact small constants, an arbitrary
zero location, dimensions 18 and 1000, both Bernoulli endpoints, and incorrect
constant/truncation controls. The theorems introduce no axioms or assumed
boundary theorem. Validation is the warning-as-error Lean build of that test
plus its stored standard-axiom audits.
