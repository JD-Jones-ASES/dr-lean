# Near-endpoint foundation: actual sampling, padding, and transport

Mathematical source: Analytic-Lab P0174 `NEAR_ENDPOINT_SCALING.md`, especially
sections1–3 and the exact signed padding identity. The proof here was written
from the formulas using the existing self-contained Lean rook, elementary
symmetric, permanent, and transport foundations. No Lab implementation is
imported. `TWO_ZERO_PERMANENT_GAP.md` identifies the separate remaining
permanent estimate; this increment does not assume or prove that estimate.

For n−1 iid cells on an n×n signed board, the exact identity is
F=a(R+S−T), with a=(n)_(n−1)/n^(n−1). For probability contenders at n≥3,
the two nonnegative marginal deficits have shared budget dr+dc≤δ=a−T≤a.
Under explicit scalar smallness conditions, actual marginal estimates and
all transport cuts construct a balanced B with (1−t)B≤P and
t²=(4/3)n²δ. No desired balanced board is supplied as a hypothesis.

The new row/column are placed first, a simultaneous reindexing of the Lab
last-row/last-column convention. The corner is zero, border entries1/n,
and core(n−1)B. Balanced input produces a doubly stochastic square. Any
original zero becomes a second zero in a different row and column.
The signed exact permanent identity has coefficient(n−1)^(n−1)/n² times
the actual rook sum, with no sample factorial. The normalization is
per(D)=μ_(n+1)*T/a, where μ is the one-zero boundary floor. Uniform input
has per(D)=μ_(n+1).

`NearEndpointPaddingCounting` proves the actual omitted-index/increasing
embedding bijection, rook-as-permanent-minors identity, permanent Laplace
expansions, and signed corner-border formula. These include a one-cell core,
zero scalar and zero-draw empty minor. The empty original board remains
well-defined but is excluded from formulas requiring1/n normalization.

Validation: `lake --wfail build Test.NearEndpointFoundation`,3482jobs,
14 persistent examples and10 standard-only axiom reports. Controls retain
signed border factors, reject an extra degree-two factorial, distinguish
μ4=8/81 from gamma4=3/32, preserve an actual balanced boundary board and
its two independent zeros, and exhibit the n=2,K=1 nonuniform equality.

This is an unconditional foundation. It is not yet the full n≥21 theorem:
the two-independent-zero permanent gap and the finite21–25 comparisons
remain separate proof obligations.
