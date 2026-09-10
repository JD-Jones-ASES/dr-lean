# Verification and the public-release gate

## Complete source and Lean checks

```sh
python3 scripts/check-source.py
python3 scripts/check-release.py
python3 scripts/test_bounded_project_build.py
python3 scripts/bounded_project_build.py --check-tracked-coverage --batch-size 2 \
  --report .verification/bounded-project-plan.json \
  --log .verification/bounded-project-build.jsonl
lake build +Challenge
python3 scripts/check-release.py --lean-controls
```

The source check rejects proof placeholders and prohibited trust extensions.
Test.Axioms traverses the transitive axioms of all project declarations,
including all public Solution wrappers and private helpers. The allowed set is propext, Classical.choice,
and Quot.sound. A run matching no project declarations fails.

The build helper orders the actual DR/Test/Solution import closure by dependencies
and requests at most two project modules at a time. Strict tracked coverage
rejects omitted tracked modules and imported untracked modules; source hashes
must remain unchanged throughout the build. Final explicit DR and Test
builds include the complete project axiom audit. Fifteen helper controls
pass with and without Python optimization, including missing imports,
cycles, omitted modules, source changes and subprocess failures.

This limits overlap between project modules. It does not limit external
dependency jobs or asynchronous declarations within one Lean module.
Individual large finite checks also use small serialized kernel decisions.
Each staged build job has a 360-minute ceiling. The earlier single-job run
hit GitHub's six-hour limit; its completed batches all passed, but it did
not complete the proof gate. The [timeout record](history/2026-09-10-staged-verification.md)
separates measured work from the remaining unknown runtime.
All literal proof checks remain required. A dry run verifies the build plan,
not the Lean proofs.

The workflow frees unused preinstalled runner software with the same pinned
cleanup action as the official verifier, preserving its tool cache and swap.
The two build stages cover the complete source from the pinned dependencies.
Only their completed build can supply the final Linux proof archive. A separate job verifies
its source commit, toolchain and archive digest before restoring those outputs
and running the independent kernels. All required build, metadata and kernel
jobs must succeed for the same SHA.

### Two-stage independent build

Pushes, default workflow dispatches and same-repository pull requests use
`build-prefix`, followed by `build-final`. The first job retains all source,
generator and helper controls and builds the first 679 dependency-ordered
batches. Its receipt is explicitly partial: no complete-build or release pass.
The artifact binds the full plan, source tree, workflow, helper and dependency
pins, successful batch ledger, and hashes of the compiled files to the exact
commit, run and attempt.

The workflow invokes the prefix as follows:

```sh
python3 scripts/bounded_project_build.py --check-tracked-coverage --batch-size 2 \
  --stage prefix --cut 679 --stage-receipt .verification/build-prefix-stage.json \
  --report .verification/bounded-project-plan.json \
  --log .verification/bounded-project-build.jsonl
python3 scripts/stage_build_artifact.py pack --project . --cut 679 \
  --receipt .verification/build-prefix-stage.json \
  --ledger .verification/bounded-project-build.jsonl \
  --plan .verification/bounded-project-plan.json --output "$RUNNER_TEMP/proof-prefix"
```

The second job starts from a fresh checkout and pinned dependencies. The
restore helper authenticates the current attempt's successful prefix job and
its unique artifact, then safely restores only the checked `.lake/build`
files. It rejects missing, changed, unsafe or stale evidence. These commands
require the workflow's actual GitHub context; restore also requires `GH_TOKEN`:

```sh
python3 scripts/stage_build_artifact.py restore --project . --cut 679 \
  --output .verification/restored-prefix
python3 scripts/bounded_project_build.py --check-tracked-coverage --batch-size 2 \
  --stage final --cut 679 --prior-stage-dir .verification/restored-prefix \
  --stage-receipt .verification/build-complete-stage.json \
  --report .verification/bounded-project-plan.json \
  --log .verification/bounded-project-build.jsonl
lake env lean Test/Axioms.lean
lake build +Challenge
python3 scripts/check-release.py --lean-controls
```

The final helper builds every remaining batch, checks an exhaustive ledger
with no overlaps or omissions, and explicitly builds both `DR` and `Test`.
The workflow then directly recomputes the global axiom audit, compiles Challenge,
runs the actual semantic controls, and creates a new archive for this SHA.
Even the complete-build receipt retains `release_verified: false`. The metadata
job and fresh all-twenty Comparator/Lean-kernel/NanoDa checks must also pass.

Rerunning `build-final` must include the prefix job in the new attempt;
reusing an earlier attempt's partial prefix is rejected. A later kernel-only
rerun may consume the already accepted complete archive for the identical SHA
and must still pass every independent-kernel check. Same-repository PRs bind
the tested merge commit separately from the API's PR head commit. Fork PRs are outside this transfer
protocol. The former optional `da67` cache and its dispatch input are retired:
the proposed producer timed out before it could supply a complete artifact.

The reproducible [toy handoff](../scripts/smoke_staged_handoff.py) exercises
actual Lean compilation, packing, restoration, suffix completion and a direct
axiom audit in two disposable checkouts:

```sh
python3 scripts/smoke_staged_handoff.py --lake-bin "$(command -v lake)" \
  --output .verification/staged-smoke.json
```

It uses the installed Lean 4.33.0 toolchain and mocks GitHub provenance only.
Its success is not a hosted Linux CI or independent-kernel result. The
[activation record](history/2026-09-10-staged-verification.md) records the
offline controls and the exact limits of this smoke test.

### Public statement checks

The twenty public statements are independently written in Challenge with four
fully fixed definitions and Mathlib-only imports. Its twenty intentional holes
are statement markers; Solution imports none of them and has no proof holes.
The public signature checker selects every target, verifies the reviewed types
and definition bodies, and rejects semantic mutations of the inclusive-OR
event, nonnegative domain, overlap correction and iff equality.

## Independent kernel and metadata replay

On Linux after the complete build, with real Landrun and a systemd manager
that supports the official confinement properties, run the pinned verifier
script. Pass the exact expected commit:

```sh
bash scripts/verify-comparator.sh --prepare-only
bash scripts/verify-comparator.sh --verify-only --expected-commit FULL_COMMIT_SHA
```

The tool cache is outside the project. Comparator is built under its own
Lean 4.34.0-rc1 toolchain; the project's exporter uses Lean 4.33.0. The real
official sandbox adapter retains the inner exporter delimiter, and the
systemd boundary excludes AF_UNIX sockets and retains the official process
and network restrictions. A bounded property probe selects the system manager
with the caller's nonroot UID/GID, or an equally confined user manager; failure
of both stops the run. Project and cache paths must remain accessible inside
the private-tmp namespace, as in the workflow's runner-home paths.
Both the ordinary Lean kernel and
NanoDa must explicitly accept the complete twenty-theorem Solution and the
process must exit successfully. Timeouts and missing acceptance lines fail.

The workflow also runs the exact official Palomar metadata profile under
Python 3.11.10 with hash-pinned PyYAML 6.0.3. Negative controls must reject
missing authors and maintainers. A separate supplement enforces the six
source-type spellings in the pinned written policy, with controls for the
three rejected earlier labels, all six allowed spellings, and omission. The
receipt distinguishes this vocabulary check from the official parser and
origin checks. See the [metadata correction](history/2026-09-10-metadata-policy.md)
for the policy/parser difference and preserved attribution.

This component replay does not itself perform Palomar's protected-Challenge
provenance audit, external intake, human refereeing, or registration.
JD performs manual submission.

Tool revisions follow the reviewed official
[Palomar workflow](https://github.com/PalomarRegistry/PalomarSubmission/blob/ef2fa1eadcb246c2346ddba39b52eaa53d4bb763/.github/workflows/submission.yml):
Comparator `575674928e239f5bc452aab72d1dd7b0f1326494`, exporter
`15f6055e299ad5b89345e533cc2192f4cc00f659`, NanoDa
`68d5ca9db226849b41a6fff59d796ff19d0a8840`, and Landrun
`811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`. Source/binary hashes and actual
replay outcomes are preserved with the exact CI run.

## Required before changing visibility

1. Every target in release-targets.json must have an actual compiled proof
   with the exact intended hypotheses, quantifiers, sharp constant and
   equality case. Review the formal statements against docs/THEOREMS.md and
   the informal arguments. A finite calculation cannot replace a theorem
   on all nonnegative real matrices.
2. The small Challenge must use only permitted statement dependencies and
   contain the exact public definitions and principal claims. Solution must
   prove the corresponding declarations without importing Challenge.
   Intentional statement holes are confined to Challenge.
3. Build the complete proof, Challenge, Solution and every Test module.
   Run source checks, all-target transitive axiom checks, meaningful semantic
   and certificate corruption controls, and exact theorem/type comparison.
4. Run Comparator, the Lean kernel and NanoDa independently using compatible
   pinned tools. Check current Palomar policy and its official verifier pins.
   gn-lean is a reference, not authority for stale release requirements.
5. Inspect successful independent CI and verification receipts for the exact
   release commit. The verified commit must be on default-branch main.
   Check repository contents, provenance, license, manifest and metadata;
   ensure public readers can understand and replay the complete package.
6. Verify all preceding conditions against current evidence, then change the
   repository from private to public and verify the visibility change.
   JD has already authorized that conditional action; no second permission
   request is needed. Supply the exact public commit for JD's manual intake.

Until all conditions hold, keep the repository private and the goal active.
Do not substitute a narrower statement, an empty target list, a successful
foundation build, or a metadata status field for the completed objective.

## Current evidence

At the staged workflow's activation on 2026-09-10, run `34432295599` had timed
out and no replacement staged CI run had started or passed. See the
[dated record](history/2026-09-10-staged-verification.md) and subsequent
[exact-commit workflow runs](https://github.com/JD-Jones-ASES/dr-lean/actions/workflows/development.yml).

See [PROGRESS](PROGRESS.md) for actual build results and missing work. The
current toolchain is Lean 4.33.0 with the exact Mathlib dependency graph from
the successful gn-lean reference. The live Palomar minimum on 2026-09-09 was
v4.28.0; recheck compatibility before the release verification.
