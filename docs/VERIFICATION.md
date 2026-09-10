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
The expanded development job has a 360-minute ceiling to allow the full
serialized certificate replay. This changes only the time allowance; it
does not diagnose earlier exit-143 failures or waive any proof check.
All literal proof checks remain required. A dry run verifies the build plan,
not the Lean proofs.

The workflow frees unused preinstalled runner software with the same pinned
cleanup action as the official verifier, preserving its tool cache and swap.
It then builds the complete source from the pinned dependencies.
It archives only a successful exact-commit Linux build. A separate job verifies
its source commit, toolchain and archive digest before restoring those outputs
and running the independent kernels. Both jobs must succeed for the same SHA.

### Optional reuse of the reviewed Linux build

Normal pushes and default workflow dispatches build from pinned dependencies.
The optional `reuse_reviewed_proof_cache` dispatch input may reuse compiled
outputs from the exact reviewed commit
`da67b34f27d7b590bb4596435d0f77c48c192ccc`, run `34432295599`, attempt 1.
The helper requires that run's completed successful build job, full 2,736-module
plan and 1,368-batch success ledger, global axiom audit, Challenge/semantic
checks, exact archive digest and toolchain, and safe complete compiled files.
A pending, failed, partial, expired or mismatched producer build is rejected.

Every Git tree entry and mode outside eight named metadata, documentation,
workflow and helper paths must match the producer. All Lean sources, public
statements, target inventory, data, dependency pins and existing proof-verification
scripts must therefore be identical. The helper restores only `.lake/build`;
its receipt says `compiled_input_restored`, with `release_verified: false`.
Thirty-six offline controls cover provenance, source changes, incomplete
ledgers, unsafe archives and failed restores. They do not establish that a
real Linux artifact has been restored.

The consumer still runs the entire bounded build, then directly recomputes
`Test/Axioms.lean`, compiles Challenge, runs the actual semantic controls,
and creates a new archive bound to its own exact commit. Its corrected
metadata and fresh all-twenty Comparator/Lean-kernel/NanoDa verification must
succeed. Producer metadata or kernel status grants no consumer release pass.
The optional producer archive expires after seven days; future default runs
remain independent of it.

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

See [PROGRESS](PROGRESS.md) for actual build results and missing work. The
current toolchain is Lean 4.33.0 with the exact Mathlib dependency graph from
the successful gn-lean reference. The live Palomar minimum on 2026-09-09 was
v4.28.0; recheck compatibility before the release verification.
