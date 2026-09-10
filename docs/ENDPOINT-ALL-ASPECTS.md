# Complete large-row endpoint theorem

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

The compactness and equality arguments belong to the component theorems;
the assembly preserves their actual `UniformMaximizer` statements. This
is the accepted P0174 `ENDPOINT_ALL_ASPECT_RATIOS_LARGE_M.md` result. The
other endpoint strips and square near-endpoint target are separate results.

`Test.AllAspects` covers the square boundary, an arbitrarily long rectangle,
representative points in all four intervals, the integer transition boundary,
the lower row cutoff and a rejected extension of the logarithmic estimate.
Three transitive axiom reports accompany its nine persistent examples.
