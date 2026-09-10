# Permanent stationarity on a prescribed face

This prerequisite concerns an actual minimum of the permanent over the full
doubly stochastic face defined by a Boolean support mask. Additional zero entries
are permitted. It supplies the cofactor inequalities used in the
[two-zero support argument](TWO_ZERO_FACE_SUPPORT.md) and the
[repeated-support reduction](TWO_ZERO_REDUCTION.md).

`PermanentFaceCofactors` defines a cofactor directly by the permutation expansion.
It proves row and column Euler identities and the derivative of the permanent
along every signed matrix line, including the empty index type.
`PermanentCofactorAlgebra` proves row/column replacement and transpose identities.

For a face minimum A with permanent p, the direction
D(i,j) = A(i,j) (C(i,j) - p) has zero row and column sums. Small signed steps
preserve nonnegativity and every original zero. The derivative therefore vanishes;
the Euler identities turn it into the sum of A(i,j) (C(i,j) - p)^2.
Consequently every positive entry has cofactor p. This argument is implemented in
`PermanentFaceStationarity` without an assumed multiplier or support theorem.

`PermanentFaceDirections` also proves the one-sided derivative inequality toward
every matrix on the same closed face. A positive allowed cofactor supplies a
positive partial matching; adjoining the allowed cell gives a feasible
permutation matrix. The directional inequality then proves C(i,j) >= p.
The resulting boundary-inclusive statement is C(i,j) = 0 or C(i,j) >= p.
Removing that zero alternative requires another argument: the identity matrix
provides an explicit counterexample to unrestricted cofactor positivity.

The mathematical context is the classical supported-cofactor condition discussed
in [van Lint's permanent survey](https://pure.tue.nl/ws/files/4254844/696880.pdf)
and [Minc's note on London's lemma](https://msp.org/pjm/1975/58-1/pjm-v58-n1-p14-p.pdf).
The two-zero face application is described in
[Pula, Song and Wanless (2011)](https://cs.du.edu/~mathfiles/preprints/nsm-math-preprint-1022.pdf).
Those sources motivate the prerequisite; no external theorem or proof code is
assumed in these Lean statements.

Validation: `lake build +Test.PermanentFaceStationarity` checks eleven examples
and ten axiom audits. The examples include empty dimensions, signed row
replacement, extra zero entries, the identity-matrix zero-cofactor control, and
the exact public face-minimum hypotheses. Only the standard Lean axioms occur.
