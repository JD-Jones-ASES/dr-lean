# dr-lean — working rules

This separate Lean project is authorized by JD. The full user goal is to
formalize the square Dittert alternative proof and the rectangular results,
then make the repository public only after every relevant verification gate
passes. JD will submit to Palomar manually. Do not submit on his behalf.

Read README.md, docs/THEOREMS.md, docs/VERIFICATION.md and the current
checkpoint in docs/PROGRESS.md. The Lab source is pinned in docs/SOURCES.md.
Preserve all release targets; a smaller passing development is progress,
not completion. Keep arbitrary real nonnegative matrices, zero entries,
quantifiers, sharp constants and unique equality cases intact.

Use the pinned Lean/Mathlib runtime. No `sorry`, `admit`, custom `axiom`,
`unsafe`, `partial`, `native_decide`, or `Lean.ofReduceBool` in proof sources.
Only an explicitly isolated Challenge may contain statement placeholders;
Solution and the proof library must never import Challenge. Prove the
mathematics behind finite certificate checks; a Python PASS is not a Lean
proof. Do not assume van der Waerden, transport, or another missing theorem
as a new axiom or a hypothesis of the advertised result.

Keep modules small, docstrings mathematical, imports targeted, and proofs
readable. Prefer genuine reusable lemmas to tactic loops matching one output.
Build edited modules before integration, build DR and Test, check source and
transitive axioms, and run the appropriate stronger gates before release.

Work in coherent codex/ branches and commit/push private checkpoints. No
force-push. Keep the release requirements distinct from development checks.
Before changing visibility, independently inspect every promised theorem,
exact source/type alignment, all axiom dependencies, CI and Comparator/NanoDa
for the exact main commit. The user's conditional public-release permission
is already given; once its conditions are genuinely met, carry it out.
