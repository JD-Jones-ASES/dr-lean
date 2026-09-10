# Dittert and rectangular semimatching inequalities

This repository proves twenty principal statements, including Dittert's
inequality, about the probability of avoiding row or column collisions. The proofs are
written in Lean 4. The square argument is an alternative proof; earlier
work and the source of the rectangular question are credited in
[Sources](docs/SOURCES.md).

## The probability problem

Let $P=(p_{ij})$ be an $m\times n$ matrix with nonnegative real entries and
$\sum_{i,j}p_{ij}=1$. Draw $k$ cells independently with replacement, using
$P$ as their distribution. Write $F_k(P)$ for the probability that the draws
have distinct rows **or** distinct columns. The OR includes the event that
both are distinct.

For the uniform matrix $U_{ij}=1/(mn)$, put

$$
a=\frac{(m)_k}{m^k},\qquad b=\frac{(n)_k}{n^k},
\qquad F_k(U)=a+b-ab,
$$

where $(d)_k=d(d-1)\cdots(d-k+1)$. The rectangular question asks whether

$$
F_k(P)\leq F_k(U),\qquad F_k(P)=F_k(U)\iff P=U
$$

for every $2\leq k\leq\min(m,n)$. All statements here allow zero entries
and arbitrary row and column sums. At $k=1$, every probability matrix has
success probability one, so uniqueness is not asserted.

## Results

The [theorem list](docs/THEOREMS.md) gives every hypothesis, constant, and
Lean declaration. It includes:

- The square endpoint $m=n=k$ in every positive dimension: Dittert's
  inequality, with its unique equality case.
- Every admissible rectangle at $k=2$ and $k=3$; every four-row rectangle at
  $k=4$; and the $5\times5$ and $20\times20$ cases at $k=4$.
- Every $k\geq4$ when both dimensions are at least an explicit threshold;
  $\min(m,n)\geq k^{21}$ is a simpler sufficient condition.
- The endpoint $k=m$ for every $n\geq m$ once $m\geq10^{18}$, together
  with several sharper ranges at smaller $m$.
- The square near-endpoint $k=n-1$ for every $n\geq21$.

These results also give every admissible order when the smaller side is at
most four, and every admissible order on $5\times5$. **The unrestricted
rectangular problem remains open.**

## Dittert's inequality

For a nonnegative square matrix $A$ of order $n\geq1$ and total mass $n$,
let $r_i$ and $c_j$ be its row and column sums. Then

$$
\prod_i r_i+\prod_j c_j-\operatorname{per}(A)
\leq 2-\frac{n!}{n^n},
$$

with equality exactly when every entry is $1/n$. This is the square
probability theorem: setting $P=A/n$ multiplies the displayed functional
by $n!/n^n$ to give $F_n(P)$.

The proof classifies maximizers on the closed simplex. At orders one and
two the argument is elementary. At order three it excludes the possible
boundary supports. Order four uses an exact polynomial certificate. For
orders at least six, stationarity yields a spectral cut whose block
permanent lower bounds contradict nonuniformity; a separate argument
handles order five. The required transport theorem and sharp permanent
bound, including equality, are proved within the repository.

Read the [square proof map](docs/SQUARE-DEPENDENCIES.md), followed by the
[order-three](docs/ORDER-THREE-PROOF.md),
[order-four](docs/ORDER-FOUR-PROOF.md),
[order-five](docs/ORDER-FIVE-PROOF.md), and
[spectral](docs/SPECTRAL-PROOF.md) arguments.

## Rectangular proofs

The [collision method](docs/RECTANGULAR-FOUNDATIONS.md) controls the loss
from nonuniform marginals and then averages columns. At three samples,
support arguments, infinite ranges, and exact polynomial certificates
cover every rectangle. Each certificate has a Lean proof connecting its
coefficient identities and positive matrices to the original probability
and its equality case. See the [three-sample proof](docs/ORDER-THREE-COMPLETE.md)
and the [four-row proof](docs/FOUR-ROW-PROOF.md).

At the endpoint, marginal concentration combines with transport, permanent
bounds, and estimates for independent row assignments. The
[endpoint proof map](docs/ENDPOINT-ALL-ASPECTS.md) explains how the ranges
fit together; the [square near-endpoint proof](docs/SQUARE_NEAR_ENDPOINT.md)
uses a permanent bound for matrices with two independent zeros.

## Read and verify the Lean statements

[Challenge.lean](Challenge.lean) contains the twenty statements using only
ordinary matrix and probability definitions. Its intentional placeholders
are isolated from the proof library. [Solution.lean](Solution.lean) proves
the matching statements through the `DR` library. All proof dependencies
are included or pinned in [lake-manifest.json](lake-manifest.json).

```sh
lake exe cache get
python3 scripts/bounded_project_build.py --check-tracked-coverage
lake build Challenge
python3 scripts/check-source.py
```

See [Verification](docs/VERIFICATION.md) for the complete build, axiom,
statement-comparison, and independent-kernel checks. CI results apply only
to the exact commit they check; current outcomes are available in the
[verification workflow](https://github.com/JD-Jones-ASES/dr-lean/actions/workflows/development.yml).

Human responsibility: JD Jones. See [Disclosure](DISCLOSURE.md) for the use
of AI in the mathematical arguments and formalization. The repository
remains private for his inspection.
