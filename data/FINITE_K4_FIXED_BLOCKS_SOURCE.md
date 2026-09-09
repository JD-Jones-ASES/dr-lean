# Exact fixed-board K4 block certificates

The input is the frozen `finite_k4_fixed_seeds.json`, with provenance and
pinned source hashes in `FINITE_K4_FIXED_SEEDS_SOURCE.md`. No source program
is imported or executed. The generator uses exact rational arithmetic only.
The 407 coefficient positions use the independently checked universal role
catalogue; `finiteK4FixedRoleLookup_key` also verifies the balanced lookup in
Lean on every literal catalogue key.

For each of the ten multiplier seeds and each board order 5 or 20, the
formula-defined matrices use actual ordinary counts `R=n-nr` and `C=n-nc`.
The full trivial sector is indexed lexicographically on the compressed
`(nr+1)×(nc+1)` rectangle. Its exact kernel vector has weights `1,C,R,RC`.
The principal block deletes the last ordinary/ordinary coordinate. The other
three blocks are the row-standard, column-standard, and scalar interaction
sectors. There are 40 strict blocks and 150 positive LDL pivots per board.
The largest principal block is 15×15.

The exact two-axis definitions, casts and reindexing theorems are in
`FiniteK4FixedBlocks.lean`. Their field formulas retain signed values and
zero-count arithmetic, with no implicit positivity hypothesis. Physical
interpretation and matrix-positivity assembly require the appropriate
ordinary counts; the two fixed boards have `R,C≥2` for every seed.

`generate_finite_k4_fixed_blocks.py` reconstructs all matrices from the literal
seed values and computes an exact LDL factorization. Nonpositive pivots,
asymmetry, inexact entries and failed reconstruction are rejected. The Lean
case modules independently check the full weighted kernel and each exact
strict Gram identity against those actual formula-defined matrices. They
never accept a floating-point eigenvalue or a Python Boolean as a premise.

Generation scope and proof completion are distinct. The generator emits
all 20 case modules with `--all`; actual completed proofs are recorded in
`.verification/finite-k4-fixed-cases-replay.jsonl`. The generated
`FiniteK4FixedChecked5.lean` and `FiniteK4FixedChecked20.lean` each import
exactly their own ten cases and prove all-seed real matrix hypotheses. The
optional `FiniteK4FixedCheckedBlocks.lean` imports those two interfaces. Each
board interface is built only after its ten imported gates succeed.
The probability identity and final uniform-maximizer assembly are separate.

Reproduction:

```bash
python3 scripts/generate_finite_k4_fixed_blocks.py --all --check
python3 -O scripts/generate_finite_k4_fixed_blocks.py --all --check
python3 scripts/test_finite_k4_fixed_blocks.py
python3 -O scripts/test_finite_k4_fixed_blocks.py
lake --wfail build +DR.Certificates.FiniteK4FixedChecked5
lake --wfail build +DR.Certificates.FiniteK4FixedChecked20
lake --wfail build +Test.FiniteK4FixedBlocks +Test.FiniteK4FixedPilot
lake --wfail build +Test.FiniteK4FixedChecked5
lake --wfail build +Test.FiniteK4FixedChecked20
```

For a cold replay, compile case modules one at a time or use the repository's
bounded build helper. The generic full-root CI command bounds heavy project
modules and retains every tracked import. The persistent pilot tests retain
count-zero/count-one arithmetic, signed differences, actual kernel weights,
exact rational-to-real transport and rejection of an incorrect aggregate
kernel weight.

The Python suite has seven groups, including exact per-board import and gate
coverage and fourteen explicit rejection controls. It runs unchanged under
`python3 -O`. The all-seed Lean tests also preserve strict positivity for an
arbitrary nonzero real principal-block vector, negative literal coefficients,
and rejection of an unweighted full compressed kernel. The rational-to-real
kernel transport itself is tested at zero ordinary-count arithmetic, with
arbitrary signed coefficients and an explicit exact kernel premise.
