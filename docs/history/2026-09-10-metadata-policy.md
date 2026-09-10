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

To avoid repeating unchanged compilation for this correction, the workflow
also provides optional reuse of the reviewed producer's complete Linux build.
It compares all proof inputs exactly and still requires every consumer check
and fresh independent kernels. The [verification guide](../VERIFICATION.md#optional-reuse-of-the-reviewed-linux-build)
describes the requirements; the option itself is not evidence of a successful
artifact restore or release.
