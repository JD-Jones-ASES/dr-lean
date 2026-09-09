# Finite K=3 certificates and the actual sampling probability

The separate 4-by-4 and 4-by-5 cases are complete, including all zero entries,
exact uniform equality, and the transposed 5-by-4 case. The finite-envelope
soundness bridge is now complete, the contiguous range 4-by-N for 6<=N<=21
is proved, and the 4-by-959 pilot certificate is checked.
Full replay and dimension coverage for all 1,330 finite
rectangles remain in progress. This account separates completed proofs from
those pending data.

## Literal coefficient roles and polynomial identity

The source is Analytic-Lab P0174 `FINITE_RECTANGLE_CERTIFICATES_K3.md`.
Each physical entry Q_ef[a,b] depends on the equality relations of four row
labels and four column labels. [FiniteK3Orbits](../DR/Certificates/FiniteK3Orbits.lean)
proves completeness of the fifteen patterns on each axis and checks the 225
pattern pairs against the source's 93 canonical roles. Multiplier-pair and
quadratic-pair reversal preserve the actual entry. Row/column transposition
remains a separate operation.

[The quartic template](../DR/Certificates/FiniteK3QuarticTemplate.lean) relates
the 33 literal coefficient equations to all ordered quartets. There are six
ways to choose the multiplier positions. Repeated multiplier cells have
integer weight two, distinct cells weight one. Ninety compression checks
and 1,350 role/weight checks identify these physical choices; 20,925 integer
coefficient relations and 225 deleted-success relations connect them to the
33 equations. The multiplicity is separately proved positive before cancellation.
[The local identity](../DR/Certificates/FiniteK3QuarticLocal.lean) transfers
this result to arbitrary ambient row and column labels.

[The probability bridge](../DR/Certificates/FiniteK3QuarticProbability.lean)
sums that identity against actual signed iid weights. Each position permutation
preserves sample mass. Deleting any one coordinate contributes the total mass
S, without division or normalization. The result is exactly

    alpha*S^4 - S*F3(p)
      = sum_e sum_f w(e,f)*p_e*p_f*(p^T Q_ef p),
    w(e,e)=1, and w(e,f)=1/2 when e differs from f.

F3 is the original ordered, with-replacement, inclusive-OR functional. The
identity includes signed weights, zero total mass and empty outcome types.
The tests distinguish row-only, column-only and simultaneous success, retain
repeated cells, and detect losing either the diagonal factor two or the extra S.

[Certificate soundness](../DR/Certificates/FiniteK3Soundness.lean) proves the
full sharp inequality and uniform iff equality from these equations, actual
PSD pair matrices and an exact constant quadratic kernel for diagonal pairs.
At mass one some diagonal multiplier is positive, including on support faces.
Thus no positive-entry premise is added to obtain strict uniqueness.

## Completed small cases

[The 4-by-4 proof](../DR/Rectangular/FourByFourThree.lean) establishes

    (1/20)*sum_ij(P_ij-1/16)^2 <= 39/64-F3(P).

It uses a separate cubic certificate and an exact shifted 15-coordinate
principal Gram matrix. [The 4-by-5 proof](../DR/Rectangular/FourByFiveThree.lean)
establishes

    (1/5)*sum_ij(P_ij-1/20)^2 <= 27/40-F3(P).

For the latter, all 33 equations are checked at alpha=27/40. Actual row and
column permutations cover every physical multiplier pair. Eighty-two
one-axis lookups are proved once, then used to check all four shifted
19-by-19 principal matrices: 76 positive pivots and 1,444 exact entries.
The actual pair matrices have floor 2/5 on the constant-orthogonal space;
nonnegative unordered-pair weights give the displayed 1/5 stability bound.
Squared distance vanishes exactly at uniform, independently of positivity.

## Remaining envelope

| Rows | Columns | Cases |
|---|---|---:|
| 4 | 6 through 959 | 954 |
| 5 | 5 through 120 | 116 |
| 6 | 6 through 237 | 232 |
| 7 | 7 through 24 | 18 |
| 8 | 8 through 14 | 7 |
| 9 | 9 through 11 | 3 |
| Total | | 1,330 |

The [complete physical block bridge](FINITE-K3-BLOCK-SOUNDNESS.md) now identifies
every seed from four representative pairs and transports its actual aggregate
kernel and eight strict H/B0 blocks. `FiniteK3EnvelopeValid.uniformMaximizer`
derives the original inequality and iff uniform equality directly from these
finite rational obligations. The checked 4-by-6 instance has sharp value 13/18.
[The first contiguous dispatcher](../DR/Rectangular/OrderThreeFourRowFiniteInitial.lean)
proves `UniformMaximizer 4 n 3` for every 6<=n<=21 from sixteen actual checked
certificates, with both endpoints included.

The [self-contained source record](../data/FINITE_K3_SOURCE.md) and
[exact dimension manifest](../data/finite_k3_manifest.json) contain all 1,330
planned cases. The manifest is a coverage specification, not a completion log.
Their bounded Lean replay and complete dispatcher must finish before the
all-rectangle K=3 theorem can be assembled with
[the infinite ranges](ORDER-THREE-RANGES.md).

The generators reproduce the present source data with
`python3 scripts/generate_finite_k3_quartic.py --check` and
`python3 scripts/generate_four_by_five_three.py --check`. Their validation
remains active under Python `-O`; Lean independently checks the generated
identities. No numerical discovery status is accepted as proof.
