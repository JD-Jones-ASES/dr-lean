# Exact reduced-board permanent

Source: Analytic-Lab P0174 `TWO_ZERO_PERMANENT_GAP.md`, equations (3)--(4).
The source hash and scalar definition provenance are recorded in
`TWO_ZERO_POLYNOMIAL_SOURCE.md`.

`TwoZeroReducedCounting` proves the exact permanent of Schrodinger's actual
`twoZeroReducedBoard n a b` for every n>=2 and arbitrary signed real a,b.
The board has two exceptional diagonal entries 1-na,1-nb, two exceptional
off-diagonal zeros, symmetric borders a,b, and constant ordinary core
x=(1-a-b)/n. Its permanent is

    n! [ (1-na)(1-nb)x^n
       + n((1-na)b^2+(1-nb)a^2)x^(n-1)
       + n(n-1)a^2b^2 x^(n-2) ].

The proof works first with five independent signed parameters for the two
diagonal entries, borders and core. Two actual Laplace expansions leave
identical rows; summing their permutations contributes n!. Increasing column
deletion preserves the two exceptional coordinates when an ordinary column is
removed. The ordinary choices contribute n and n(n-1), respectively. No
division by entries, positive approximation, or assumed permanent formula is
used. The actual matrix definition is then identified entry by entry and the
displayed expansion is factored into `twoZeroReducedPermanent`.

Replay: `lake build Test.TwoZeroReducedCounting`. Controls retain ordinary
count two, a zero core, zero borders, zero exceptional diagonals, a negative
signed permanent, rejection of a missing factorial, and an independently
computed n=1 counterexample to removing the dimension guard.
