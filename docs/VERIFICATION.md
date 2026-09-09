# Verification and the public-release gate

## Development checks

```sh
python3 scripts/check-source.py
lake build DR Test
```

The source check rejects proof placeholders and prohibited trust extensions.
Test.Axioms traverses the transitive axioms of all project declarations,
including private helpers. The allowed set is propext, Classical.choice,
and Quot.sound. A run matching no project declarations fails.

The development workflow runs these checks independently on GitHub. A green
run validates the completed modules at that commit. It does not establish
that a pending theorem was proved or that the release target set is complete.

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
