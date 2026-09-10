# Written metadata policy correction

The final policy review on 2026-09-10 found a difference between Palomar's
written requirements and its current parser. The policy, submission pipeline,
schema, and independent-verifier pins had not changed. The official parser
and upstream v0.4 schema permit arbitrary source-type text, but the binding
[specification](https://github.com/PalomarRegistry/PalomarPolicy/blob/e9c8c238f5695b10f75db7175648a1d0195352c1/docs/specification.md#L131-L134)
and [contribution rules](https://github.com/PalomarRegistry/PalomarPolicy/blob/e9c8c238f5695b10f75db7175648a1d0195352c1/CONTRIBUTING.md#L483-L499)
require a closed vocabulary.

Three labels in [formalization.yaml](../../formalization.yaml) were corrected:

| Source | Earlier type | Corrected type |
| --- | --- | --- |
| Analytic-Lab research notes | `research notes` | `other` |
| Rybin's supplied post | `web post` | `web discussion` |
| Earlier public Dittert proof project | `proof project` | `other` |

Titles, attribution, source relationships, and the mathematical scope are
preserved. In particular, the result remains source-based and the Dittert
argument remains an alternative proof. The policy reserves `original-proof`
for a different origin classification; it would be incorrect here.

The complete review of the written metadata requirements found no additional
field correction. The earlier official-parser and full-schema receipts remain
valid records of those checks on their recorded bytes; they did not establish
compliance with this additional written source-type rule.

The corrected release requires its own exact-commit verification under the
[release gate](../VERIFICATION.md). All Lean sources, statement definitions,
the twenty-target inventory, mathematical data, and dependency pins are
unchanged by this metadata correction. Full arbitrary-rectangle P2 remains
outside the proved scope.

A one-off cache proposal for this correction depended on a complete successful
Linux build of `da67b34f27d7b590bb4596435d0f77c48c192ccc`. That producer,
run `34432295599`, hit GitHub's six-hour limit before completing its build.
The proposed cache therefore could not be used. Its helper and dispatch option
were retired when the [two-stage workflow](../VERIFICATION.md#two-stage-independent-build)
was activated; the [timeout and replacement record](2026-09-10-staged-verification.md)
preserves the evidence. The replacement still requires the corrected metadata
and every exact-commit proof and independent-kernel gate.
