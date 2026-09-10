# Reproducing the verification

The repository remains private for JD Jones's inspection. Successful checks
do not authorize publication or submission. Either action requires a new
explicit instruction.

The mathematical claims are stated in [Theorems](THEOREMS.md) and
[Challenge](../Challenge.lean), and proved by [Solution](../Solution.lean)
using the library. Verification must cover all twenty declarations with their
full hypotheses, sharp bounds and equality cases.

## Source and Lean checks

Use the versions in [lean-toolchain](../lean-toolchain) and
[lake-manifest.json](../lake-manifest.json). From the repository root:

```sh
lake exe cache get
python3 scripts/check-source.py
python3 scripts/check-release.py
python3 scripts/bounded_project_build.py --check-tracked-coverage --batch-size 2 \
  --report .verification/bounded-project-plan.json \
  --log .verification/bounded-project-build.jsonl
lake env lean Test/Axioms.lean
lake build +Challenge
python3 scripts/check-release.py --lean-controls
```

The source checker rejects proof placeholders and prohibited trust extensions.
Challenge alone contains intentional statement placeholders; neither Solution
nor the proof library may import it. The signature checker compares all twenty
statements and four fixed definitions, including controls for the inclusive
OR, the nonnegative domain, the overlap correction and exact uniform equality.

The bounded build follows the complete DR/Test/Solution import closure,
requests at most two project modules per batch, and explicitly builds the DR
and Test roots. Strict tracked coverage rejects omitted tracked modules and
imported untracked modules. Source bytes must remain unchanged. The direct
`Test/Axioms.lean` invocation recomputes the transitive axioms of project
declarations, public wrappers and private helpers. Only `propext`,
`Classical.choice` and `Quot.sound` are accepted; an empty audit fails.

The [workflow](../.github/workflows/development.yml) also lists the exact
certificate-generator and corruption controls. These complement the Lean
soundness proofs; they do not replace them. Helper controls can be run locally:

```sh
for check in scripts/test_bounded_project_build.py \
  scripts/test_staged_project_build.py scripts/test_stage_build_artifact.py \
  scripts/test_staged_workflow.py scripts/test_metadata_policy.py
do
  python3 "$check"
  python3 -O "$check"
done
```

## Two-stage Linux build

The workflow splits the same dependency-ordered build between
`build-prefix` and `build-final`, each with a 360-minute ceiling. The
prefix runs source, generator and helper controls and the first 679 batches.
Its receipt is explicitly partial. A hashed artifact binds the full plan,
source tree, workflow, dependencies, helpers and successful batch ledger to
the exact commit, run and attempt.

The final job uses a fresh checkout and pinned dependencies. It authenticates
the current attempt's successful prefix, checks every restored compiled file,
builds the entire remaining suffix and verifies an exhaustive ledger with no
overlaps or omissions. It then builds the complete roots, directly recomputes
the axiom audit, compiles Challenge, runs the semantic controls and creates
the complete archive for that SHA.

The exact staged commands and artifact names are in the workflow.
Rerunning `build-final` requires a successful prefix in the same attempt.
A later independent-kernel-only rerun may consume an accepted complete archive
for the identical SHA and must still pass every kernel check. Same-repository
PRs distinguish the tested merge commit from the API's head commit; fork PRs
are outside this artifact-transfer protocol.

The [toy handoff](../scripts/smoke_staged_handoff.py) can test the protocol
with the installed Lean 4.33.0 toolchain in two disposable checkouts:

```sh
python3 scripts/smoke_staged_handoff.py --lake-bin "$(command -v lake)" \
  --output .verification/staged-smoke.json
```

It performs actual small Lean builds and archive restoration but mocks GitHub
provenance. It is not a full proof replay, hosted CI run or independent-kernel
test. A dry build plan likewise checks the plan rather than its proofs.

## Metadata

`scripts/check-official-metadata.py --pipeline PINNED_PIPELINE_CHECKOUT`
uses the official parser/profile from
[PalomarSubmission](https://github.com/PalomarRegistry/PalomarSubmission/tree/ef2fa1eadcb246c2346ddba39b52eaa53d4bb763),
under Python 3.11.10 and PyYAML 6.0.3 installed from that checkout's
hash-pinned requirements. The workflow provides the full setup commands.
The checker verifies the exact official checkout and runtime, rejects empty
authors and maintainers, and binds its result to the metadata and checker
bytes.

A separate supplement checks the optional source-type vocabulary in the
[pinned written policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/e9c8c238f5695b10f75db7175648a1d0195352c1/docs/specification.md#L131-L134).
Its controls cover unsupported types, all six allowed types and omission.
Source-based origin remains an official-profile check. A metadata pass says
nothing about the correctness or novelty of the mathematical proofs.

## Independent statement and kernel checks

On Linux, after the complete build:

```sh
bash scripts/verify-comparator.sh --prepare-only
bash scripts/verify-comparator.sh --verify-only --expected-commit FULL_COMMIT_SHA
```

The tool cache is outside the project. Comparator uses Lean 4.34.0-rc1;
the project's exporter uses Lean 4.33.0. The real Landrun/systemd sandbox
retains the official process and network restrictions, excludes AF_UNIX
sockets and requires an available confined system or user manager. Failure
to establish that boundary stops verification.

Comparator must check all twenty statement pairs. Both the ordinary Lean
kernel and NanoDa must explicitly accept the complete Solution, and the
process must exit successfully. Missing acceptance lines, timeouts and
nonzero exits fail. The pinned revisions follow the
[official verifier workflow](https://github.com/PalomarRegistry/PalomarSubmission/blob/ef2fa1eadcb246c2346ddba39b52eaa53d4bb763/.github/workflows/submission.yml):

| Tool | Revision |
| --- | --- |
| Comparator | `575674928e239f5bc452aab72d1dd7b0f1326494` |
| lean4export | `15f6055e299ad5b89345e533cc2192f4cc00f659` |
| NanoDa | `68d5ca9db226849b41a6fff59d796ff19d0a8840` |
| Landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |

## Reading the evidence

Inspect the [exact-commit workflow](https://github.com/JD-Jones-ASES/dr-lean/actions/workflows/development.yml)
and its receipts. A complete verification requires successful build, metadata
and independent-kernel jobs for the same candidate SHA, with matching source
and artifact digests. A partial prefix or complete-build receipt alone is not
complete verification. A successful receipt for earlier bytes does not verify
a revised candidate.

The receipts distinguish source checks, Lean compilation, transitive axiom
audits, metadata checks, statement comparison and the two kernel results.
They do not establish human refereeing, registry intake or mathematical
novelty. Verification and JD Jones's private inspection are separate steps;
the repository remains private after both unless he explicitly directs otherwise.
