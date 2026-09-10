# Finite K=3 rational coefficients

[finite_k3_coefficients.json](finite_k3_coefficients.json) contains 93 exact
rational coefficients for each of the 1,330 rectangles in the
[finite envelope](FINITE_K3_COMPLETE_REPLAY.md).
Its SHA-256 is `9195b006991d09b384269cc2a0df36691f1ded05489ee36c90237961d71cce0a`.

The 93 positions are coefficient roles for a pair of multiplier cells and a
quadratic pair. First-occurrence row and column labels identify equality
patterns, and four representative multiplier pairs distinguish equality in
both coordinates, only the row, only the column, or neither. The ordered role
catalogue is defined in [FiniteK3QuarticData](../DR/Certificates/FiniteK3QuarticData.lean).

The [generator](../scripts/generate_finite_k3_envelope.py) reconstructs the
four row-standard blocks and four aggregate blocks, then computes exact LDL
factors. Lean checks the quartic equations, weighted kernels and strict Gram
identities against the actual formula-defined blocks. The included JSON is
sufficient for regeneration; no other checkout is needed.

The [quartic probability identity](../DR/Certificates/FiniteK3QuarticProbability.lean)
connects these coefficients to the actual inclusive-OR sampling event.
The [envelope soundness theorem](../DR/Certificates/FiniteK3EnvelopeSoundness.lean)
then supplies the matrix inequality and equality case.
