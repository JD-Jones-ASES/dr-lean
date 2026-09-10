# Staged verification after the six-hour timeout

On 2026-09-10, the [build job](https://github.com/JD-Jones-ASES/dr-lean/actions/runs/34432295599/job/102730203710)
for commit `da67b34f27d7b590bb4596435d0f77c48c192ccc`, run `34432295599`,
attempt 1, ended as cancelled. GitHub's annotation states:
“The job has exceeded the maximum execution time of 6h0m0s”. This diagnoses
this run's timeout; it does not diagnose unrelated earlier exit-143 failures.

All 1,024 completed batches passed, covering 2,048 modules of the planned
2,736-module, 1,368-batch build. The remaining 344 batches include the batch
interrupted by cancellation. Their completion times and outcomes are unknown.
This is an incomplete verification run, not a mathematical counterexample
or a release pass. The downloaded API, annotation, ledger and timing evidence
is retained locally under `.verification/producer-failure-hwdewah7`.

The first 679 batches took **14,869.887 seconds** in the measured batch ledger,
about 4 hours 8 minutes. That excludes setup and archive work. Independent
timing review retained the cut at 679; the runtime of the full remaining
stage is still unmeasured. No claim that either stage will fit its ceiling
replaces an actual successful hosted run.

## Replacement and retained gates

The workflow now uses two sequential build jobs, each with a 360-minute
ceiling. `build-prefix` runs the existing source and generator checks, all
helper controls, and batches before cut 679. It produces an explicitly
partial receipt and a hashed artifact tied to the full dependency plan,
source tree, pins, workflow, commit, run and attempt.

`build-final` restores that same attempt's authenticated prefix into a fresh
checkout, builds every remaining batch, checks the disjoint exhaustive ledger,
and builds the complete `DR` and `Test` roots. It then directly reruns
`Test/Axioms.lean`, compiles Challenge, performs the actual semantic controls,
and archives the complete build for its own SHA. The separate official metadata
job and fresh all-twenty Comparator, Lean-kernel and NanoDa checks remain
required. A partial receipt, a restored archive, or a complete-build receipt
alone grants no release pass. Exact commands and receipt boundaries are in
the [verification guide](../VERIFICATION.md#two-stage-independent-build).

Rerunning `build-final` requires the prefix job in the current attempt; it
cannot reuse a prior attempt's partial prefix. A later kernel-only rerun can
use an already accepted complete archive for the identical SHA, while retaining
every independent-kernel check. Pushes, dispatches and
same-repository pull requests are supported; PR provenance distinguishes
the API's head commit from the actual tested merge commit. Fork PRs are
outside this artifact-transfer protocol.

The former optional cache proposal depended on the failed run's complete
build, so it never became usable. Its helper, tests and dispatch option are
retired. The [metadata correction](2026-09-10-metadata-policy.md) and its
supplemental written-policy checks remain intact. This infrastructure change
does not change Lean proofs, mathematical data, public statement types or
dependency pins. The work remains source-based, the square Dittert argument
is an alternative proof, and full arbitrary-rectangle Rybin P2 remains open.

## Local controls and pending hosted verification

The installed helper suite passed 89 controls both normally and under
Python optimization: 15 original build controls, 25 staged-build controls,
36 artifact controls and 13 workflow controls. Python compilation, workflow
shell parsing and whitespace checks also passed.

The reproducible [smoke script](../../scripts/smoke_staged_handoff.py) passed
an actual Lean 4.33.0 handoff between two disposable Git checkouts: five toy
modules, three batches, and cut 1. It packs and restores real compiled files,
checks that the prefix outputs retain their hashes and timestamps, builds
the suffix and roots, and directly audits the toy declarations. GitHub
provenance is mocked; this is neither a real artifact API test nor a Linux CI,
full-project proof replay or independent-kernel run. The integration receipt
is retained locally at `.verification/staged-integration-controls/lean-handoff.json`.

At this activation record, no replacement staged CI run had started or passed.
The repository remains private pending the complete
[exact-commit release gate](../VERIFICATION.md#required-before-changing-visibility).
