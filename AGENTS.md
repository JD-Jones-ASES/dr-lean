# dr-lean — working rules

Keep this repository private for JD Jones to inspect. Do not change its
visibility or submit it to Palomar without a new explicit instruction.

Read [README](README.md), [theorems](docs/THEOREMS.md),
[sources](docs/SOURCES.md), and [verification](docs/VERIFICATION.md).
Documentation must be self-contained: state the mathematics, explain the
proofs, and link to their Lean declarations. Omit internal project provenance
and development history. Preserve published sources and attribution.

Preserve all twenty principal theorems, arbitrary real nonnegative matrices,
zero entries, quantifiers, sharp constants, and unique equality cases.
The unrestricted rectangular problem remains open.

Use the pinned Lean and Mathlib versions. No `sorry`, `admit`, custom `axiom`,
`unsafe`, `partial`, `native_decide`, or `Lean.ofReduceBool` in proof sources.
Only the isolated Challenge may contain statement placeholders. Solution and
the proof library must never import Challenge. Prove finite-certificate
soundness in Lean; a Python check is not a substitute for a proof.

Keep modules small, docstrings mathematical, imports targeted, and proofs
readable. Build edited modules before integration; verify DR, Test, Solution,
and Challenge, inspect transitive axioms and exact statement alignment, and
require independent CI and Comparator/NanoDa acceptance for all twenty
principal theorems on the exact candidate commit.

Work in coherent codex/ branches and commit and push private checkpoints.
Do not force-push. Distinguish completed checks from checks still pending.
