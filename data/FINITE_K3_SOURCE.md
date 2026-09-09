# Finite K3 mathematical coefficient catalogue

`finite_k3_coefficients.json` is the exact rational mathematical data from
Analytic-Lab P0174 `finite_rectangle_certificates.json`, specified in
`FINITE_RECTANGLE_CERTIFICATES_K3.md`. It lists the complete 1330-case envelope,
with 93 rational coefficients per rectangle in the documented insertion-order
pair-role catalogue. It contains no implementation or numerical proof status.

Source SHA-256: `9195b006991d09b384269cc2a0df36691f1ded05489ee36c90237961d71cce0a`.

The local generator `scripts/generate_finite_k3_envelope.py` independently
reconstructs the eight documented blocks and exact LDL witnesses. Lean checks
all generated obligations against the actual coefficient and block formulas.
The source file is retained so regeneration does not require another checkout.
