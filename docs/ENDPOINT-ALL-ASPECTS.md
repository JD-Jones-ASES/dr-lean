# Complete large-row endpoint theorem

For an m×n nonnegative matrix P of total mass one, let F_k(P) be the
probability that k independent cell draws have distinct rows or distinct
columns, with inclusive OR. Write U_ij=1/(mn) and (n)_m=n(n−1)…(n−m+1).
At the endpoint k=m, put a=m!/m^m and b=(n)_m/n^m. The sharp statement is
F_m(P)≤a+b−ab, with equality if and only if P=U. A contender means a
probability board satisfying F_m(P)≥F_m(U).

`uniform_maximum_large_endpoints` proves the sharp uniform maximum and unique
equality for K=m on every m by N probability matrix with m>=10^18 and N>=m,
including transpose, arbitrary marginals and zero entries.

The proof combines four independently established theorems. For
N>=10000m^2 it uses the [quadratic strip](ENDPOINT-QUADRATIC.md). Below that
cutoff, the [transition theorem](ENDPOINT-TRANSITION-PROOF.md) applies when
m(m−1)<=20N. Further below, the [LLL strip](ENDPOINT-LLL-STRIP-PROOF.md)
applies when 4096m^3<=N^2. Every remaining integer pair falls inside the
[arithmetic range](ENDPOINT-BOUNDARY-SCALING.md).

`AllAspectParameters` proves the last overlap for every m>=10^18.
The function log(x)/sqrt(x) is antitone after exp(2). At 10^18, the elementary
estimate log(10)<=9 gives log(10^18)<=162, while sqrt(10^18)=10^9.
Consequently `log(m)<sqrt(m)/2816`. If `N^2<4096m^3`, then
`N<64m sqrt(m)`, so `22N log(m)<=m^2/2<=m(m−1)`.
The constants have strict margins; no numerical interval sampling replaces
this all-integer overlap proof.

Each component proves the sharp bound and unique equality on the full
closed probability simplex. Their dimension conditions cover every N≥m
once m≥10^18, so choosing the applicable component proves the theorem
without any further assumption on the support or marginals.

## Formal statements

[AllAspectParameters](../DR/Endpoint/AllAspectParameters.lean), [AllAspects](../DR/Endpoint/AllAspects.lean).
