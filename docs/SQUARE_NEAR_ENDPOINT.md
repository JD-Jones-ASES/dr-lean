# Square near-endpoint theorem

`DittertRybin.uniform_maximum_square_near_endpoint` proves
`UniformMaximizer n n (n-1)` for every natural n at least 21. Its domain is every
nonnegative real n by n matrix of total mass one, including all zero-entry
supports. The objective is the actual probability that n-1 independent cell
draws have distinct rows or distinct columns, with inclusive OR. The maximum
is `a*(2-a)`, where `a = n!/n^(n-1)`. Equality holds exactly at the constant
probability board with entries 1/n².

The final declaration has only the dimension hypothesis. It does not assume a
permanent bound, optimizer form, scalar certificate, positivity of the input
matrix, or existence of a balanced dominated matrix.

## Proof dependencies

The exact sampling and near-endpoint rook identities provide a shared deficit
for the row and column marginals. Actual finite transport yields balanced
domination. Padding a balanced board into order n+1 turns an original zero into
two independent zeros and converts its rook ratio into a permanent with the
exact boundary-floor normalization.

On the closed two-zero doubly stochastic face, compactness and least squared
norm select a genuine face minimum. Supported and one-sided cofactor arguments,
the proved repeated-row permanent inequality, and feasible averaging make all
ordinary rows and columns equal. The resulting two-parameter matrix has its
permanent evaluated by two Laplace expansions, valid even for signed parameters.
Equalization and the proved cubic bracket then bound the entire closed feasible
parameter rectangle.

For n=21,...,25 the full ordered active-cut certificates strengthen the bound
with the actual complementary zero rectangle of a minimum dilation. For n at
least 26 the logarithmic scalar tail supplies a dimension-uniform gap. Both
routes exclude every boundary contender, including zero deficit and unit
dilation. The existing positivity-of-all-global-maximizers theorem then gives
the sharp inequality and exact equality case on the full probability simplex.

## Source and replay

Mathematical source: Analytic-Lab P0174 `NEAR_ENDPOINT_SCALING.md`,
`TWO_ZERO_PERMANENT_GAP.md`, and `ACTIVE_CUT_RECTANGULAR_EXTENSIONS.md`.
Exact source receipts and the finite data checks are preserved in the
corresponding `data/NEAR_ENDPOINT_*` and `data/TWO_ZERO_*` notes.
These are mathematical sources; no external proof implementation is imported.

Replay `lake build Test.SquareNearEndpoint`. Tests instantiate all five finite
cases, the first analytic dimension, a large dimension, the exact closed-simplex
equality statement, transposition, strictness at an arbitrary zero cell, and
uniform attainment. A nonuniform n=2,K=1 probability matrix rejects removing the
dimension guard. The final declaration's axiom audit reports only the standard
Lean logical axioms. Parent integration separately checks the complete roots
and release wrappers on the checkpoint commit.
