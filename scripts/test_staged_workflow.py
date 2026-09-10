#!/usr/bin/env python3
"""Offline controls for the staged workflow's fixed YAML layout.

This standard-library checker is deliberately specific to this workflow, not
a general YAML parser. It makes no network, tool-download, or Lean calls.
"""
from __future__ import annotations
import hashlib
from pathlib import Path
import re
import unittest

HEADER = "name: Complete proof and independent kernel checks\non:\n  push:\n  pull_request:\n  workflow_dispatch:\npermissions:\n  contents: read\n  actions: read\nconcurrency:\n  group: dr-development-${{ github.ref }}\n  cancel-in-progress: true\n"
SOURCE_COMMANDS = [
    "python3 scripts/check-release.py",
    "python3 -O scripts/check-release.py",
    "python3 scripts/test_verifier_driver.py",
    "python3 -O scripts/test_verifier_driver.py",
    "python3 scripts/test-source-guard.py",
    "python3 scripts/check-source.py",
    "python3 scripts/test_bounded_project_build.py",
    "python3 -O scripts/test_bounded_project_build.py",
    "python3 scripts/test_staged_project_build.py",
    "python3 -O scripts/test_staged_project_build.py",
    "python3 scripts/test_stage_build_artifact.py",
    "python3 -O scripts/test_stage_build_artifact.py",
    "python3 scripts/test_staged_workflow.py",
    "python3 -O scripts/test_staged_workflow.py",
    "python3 scripts/generate_finite_k3_envelope.py --all --dispatch --manifest --check",
    "python3 scripts/generate_finite_k3_strips.py --check",
    "python3 scripts/test_finite_k3_envelope.py",
    "python3 scripts/test_finite_k3_dispatch.py",
    "python3 -O scripts/generate_finite_k3_envelope.py --all --dispatch --manifest --check",
    "python3 -O scripts/generate_finite_k3_strips.py --check",
    "python3 -O scripts/test_finite_k3_envelope.py",
    "python3 -O scripts/test_finite_k3_dispatch.py",
    "python3 scripts/generate_order_four_sextic_checks.py --check",
    "python3 -O scripts/generate_order_four_sextic_checks.py --check",
    "python3 scripts/generate_finite_k4_fixed_blocks.py --all --check",
    "python3 -O scripts/generate_finite_k4_fixed_blocks.py --all --check",
    "python3 scripts/test_finite_k4_fixed_blocks.py",
    "python3 -O scripts/test_finite_k4_fixed_blocks.py",
    "python3 scripts/generate_four_row_finite_kernel.py --check",
    "python3 -O scripts/generate_four_row_finite_kernel.py --check",
    "python3 scripts/generate_four_row_finite_diagonal_cache.py --check",
    "python3 -O scripts/generate_four_row_finite_diagonal_cache.py --check"
]
METADATA_HASH = '50e25f1d58b56fc07a0d6e63327a5978172a1c8bc0bd8d9d1feb4e704e8e00cc'
KERNEL_HASH = 'b4304a23721fc7c1e32d47b276a92b79cbb03f8b842b732754cc42d69895c3e6'
BOOTSTRAP_HASH = '8403aba395ec9e64e61e051a01f2311cb3cc10e1b5fabd7ca4ed406fbb93e587'
FINAL_TAIL_HASH = '8507c897b8b23d1feb1a5f57f5cd18ea940d5e106fecb71d81c2511ea4f99d41'
PREFIX_ARTIFACT = 'linux-proof-prefix-${{ github.sha }}-${{ github.run_id }}-${{ github.run_attempt }}'
UPLOAD = 'actions/upload-artifact@043fb46d1a93c77aae656e7c1c64a875d1fc6a0a'
PREFIX_NAMES = (
    'Check proof source', 'Install pinned Elan', 'Free space for proof and verifier artifacts',
    'Fetch pinned mathematical dependencies', 'Build the dependency prefix',
    'Pack the exact successful prefix', 'Preserve the exact prefix for this attempt',
    'Preserve prefix source and build receipts',
)
FINAL_NAMES = (
    'Install pinned Elan', 'Free space for proof and verifier artifacts',
    'Fetch pinned mathematical dependencies', 'Restore the exact prefix from this run and attempt',
    'Build remaining proof modules and verify complete roots', 'Recompute the global axiom audit',
    'Compile public Challenge and check actual semantic controls',
    'Archive this exact successful Linux proof build', 'Preserve the exact Linux build for independent checking',
    'Preserve source and build receipts',
)
COMMANDS = {
    'Build the dependency prefix':
        'python3 scripts/bounded_project_build.py --check-tracked-coverage --batch-size 2 '
        '--stage prefix --cut 679 --stage-receipt .verification/build-prefix-stage.json '
        '--report .verification/bounded-project-plan.json --log .verification/bounded-project-build.jsonl',
    'Pack the exact successful prefix':
        'python3 scripts/stage_build_artifact.py pack --project . --cut 679 '
        '--receipt .verification/build-prefix-stage.json --ledger .verification/bounded-project-build.jsonl '
        '--plan .verification/bounded-project-plan.json --output "$RUNNER_TEMP/proof-prefix"',
    'Restore the exact prefix from this run and attempt':
        'python3 scripts/stage_build_artifact.py restore --project . --cut 679 --output .verification/restored-prefix',
    'Build remaining proof modules and verify complete roots':
        'python3 scripts/bounded_project_build.py --check-tracked-coverage --batch-size 2 '
        '--stage final --cut 679 --prior-stage-dir .verification/restored-prefix '
        '--stage-receipt .verification/build-complete-stage.json '
        '--report .verification/bounded-project-plan.json --log .verification/bounded-project-build.jsonl',
    'Recompute the global axiom audit': 'lake env lean Test/Axioms.lean',
}


def require(ok, reason):
    if not ok:
        raise ValueError(reason)


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


def jobs(source):
    require('\t' not in source and '\r' not in source, 'Unsupported indentation/line endings')
    require(source.count('\njobs:\n') == 1, 'Expected one jobs mapping')
    header, body = source.split('jobs:\n', 1)
    require(header == HEADER, 'Triggers, permissions or concurrency changed')
    marks = list(re.finditer(r'^  ([a-z][a-z0-9-]*):\n', body, re.M))
    require(marks and marks[0].start() == 0, 'Malformed jobs mapping')
    require([m.group(1) for m in marks] == ['build-prefix', 'build-final', 'metadata', 'independent-kernels'],
            'Job inventory/order changed')
    return {m.group(1):body[m.start():marks[i+1].start() if i+1<len(marks) else len(body)]
            for i,m in enumerate(marks)}


def fields(block, indent, strict=False):
    result = {}
    pattern = re.compile(r'^'+' '*indent+r'([A-Za-z_][A-Za-z0-9_-]*):(?: (.*))?$')
    for line in block.splitlines():
        match = pattern.fullmatch(line)
        if match is None:
            if strict and line.startswith(' '*indent) and len(line)>indent and not line[indent].isspace():
                require(line[indent:].startswith('#'), 'Unsupported structural YAML field')
            continue
        require(match.group(1) not in result, 'Duplicate YAML field: '+match.group(1))
        result[match.group(1)] = match.group(2) or ''
    return result


def steps(job):
    marks = list(re.finditer(r'^      - (name|uses): (.+)$', job, re.M))
    require(len(marks) == len(re.findall(r'^      - ', job, re.M)), 'Unsupported step layout')
    result = []
    for i,match in enumerate(marks):
        block = job[match.start():marks[i+1].start() if i+1<len(marks) else len(job)]
        props = fields(block, 8, strict=True)
        require(set(props) <= {'uses','with','env','run','shell','if'}, 'Unsupported step field')
        result.append((match.group(1),match.group(2),block,props))
    return result


def step(job, name):
    found = [item for item in steps(job) if item[0] == 'name' and item[1] == name]
    require(len(found) == 1, 'Missing/duplicate step: '+name)
    return found[0]


def run_text(item):
    require('run' in item[3], 'Missing run: '+item[1])
    if item[3]['run'] != '|':
        require(item[3]['run'] != '>', 'Unsupported folded run')
        return item[3]['run']
    tail = item[2].split('        run: |\n',1)[1]
    lines = []
    for line in tail.splitlines():
        if line and not line.startswith('          '):
            break
        lines.append(line[10:] if line else '')
    return '\n'.join(lines).rstrip()


def validate_workflow(source):
    for retired in ('reuse_reviewed_proof_cache','restore-reviewed-proof-cache.py','test_reviewed_proof_cache.py'):
        require(retired not in source, 'Retired da67 cache remains')
    blocks = jobs(source)
    prefix, final = blocks['build-prefix'], blocks['build-final']
    for name,block,names in (('build-prefix',prefix,PREFIX_NAMES),('build-final',final,FINAL_NAMES)):
        require(block.count('    steps:\n') == 1, 'Duplicate/missing steps mapping')
        attrs = fields(block.split('    steps:\n',1)[0],4,strict=True)
        expected = {'runs-on':'ubuntu-24.04','timeout-minutes':'360'}
        if name == 'build-final':
            expected['needs'] = '[build-prefix]'
        require(attrs == expected, 'Stage dependency/runner/timeout/condition changed')
        items = steps(block)
        require([item[1] for item in items if item[0]=='name'] == list(names), 'Gate inventory/order changed')
        require(len(items)==len(names)+1 and items[0][:2] ==
                ('uses','actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1'), 'Pinned checkout changed')
        require(set(items[0][3])=={'with'} and fields(items[0][2],10,strict=True)==
                {'persist-credentials':'false','fetch-depth':'0'}, 'Checkout options changed')
        for item in items[1:-1]:
            require('if' not in item[3], 'Required gate is conditional: '+item[1])
        require(items[-1][3].get('if')=='always()', 'Diagnostic upload must remain always')
    source_step = step(prefix,'Check proof source')
    require(set(source_step[3])=={'run'} and run_text(source_step).splitlines()==SOURCE_COMMANDS,
            'Source/test/generator gate or execution environment changed')
    for name,expected in COMMANDS.items():
        block = prefix if name in PREFIX_NAMES else final
        item = step(block,name)
        expected_fields = {'run','env'} if name.startswith('Restore ') else {'run'}
        require(set(item[3])==expected_fields, 'Stage/audit execution environment changed')
        actual = ' '.join(run_text(item).replace('\\\n',' ').split())
        require(actual==expected, 'Stage/audit command changed: '+name)
    upload = step(prefix,'Preserve the exact prefix for this attempt')
    require(set(upload[3])=={'uses','with'} and upload[3].get('uses')==UPLOAD and fields(upload[2],10,strict=True)=={
        'name':PREFIX_ARTIFACT,'path':'${{ runner.temp }}/proof-prefix/','compression-level':'0',
        'if-no-files-found':'error','retention-days':'7'}, 'Prefix identity or completeness changed')
    restore = step(final,'Restore the exact prefix from this run and attempt')
    require(fields(restore[2].split('        run:',1)[0],10,strict=True)==
            {'GH_TOKEN':'${{ github.token }}'}, 'Restore authentication changed')
    for block,end in ((prefix,'Build the dependency prefix'),(final,'Restore the exact prefix from this run and attempt')):
        bootstrap = block[block.index('      - name: Install pinned Elan\n'):block.index('      - name: '+end+'\n')]
        require(digest(bootstrap)==BOOTSTRAP_HASH, 'Pinned bootstrap/dependencies changed')
    final_tail = final[final.index('      - name: Compile public Challenge and check actual semantic controls\n'):]
    require(digest(final_tail)==FINAL_TAIL_HASH, 'Final semantic/archive/receipt gates changed')
    require(digest(blocks['metadata'])==METADATA_HASH, 'Official metadata/policy gates changed')
    require(digest(blocks['independent-kernels'])==KERNEL_HASH, 'Fresh all20 kernel or final/metadata dependency changed')
    return {'cut':679,'source_commands':len(SOURCE_COMMANDS),'retired_cache':True,
            'metadata_preserved':True,'fresh_all20_kernels_preserved':True}


def workflow_path():
    root = Path(__file__).resolve().parents[1]
    actual = root/'.github/workflows/development.yml'
    return actual if actual.exists() else root/'development.yml.proposed'


class StagedWorkflowTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = workflow_path().read_text()

    def reject_change(self, old, new):
        self.assertIn(old,self.source)
        with self.assertRaises(ValueError):
            validate_workflow(self.source.replace(old,new,1))

    def test_actual_workflow(self):
        self.assertEqual(validate_workflow(self.source), {
            'cut':679,'source_commands':32,'retired_cache':True,
            'metadata_preserved':True,'fresh_all20_kernels_preserved':True})

    def test_every_source_generator_and_test_command_is_required(self):
        for value in SOURCE_COMMANDS:
            with self.subTest(command=value):
                self.reject_change('          '+value+'\n','')

    def test_early_source_success_rejects(self):
        self.reject_change('          python3 scripts/check-release.py\n',
                           '          exit 0\n          python3 scripts/check-release.py\n')

    def test_critical_steps_must_be_unconditional(self):
        for name in ('Check proof source',*COMMANDS,'Preserve the exact prefix for this attempt'):
            with self.subTest(step=name):
                line='      - name: '+name+'\n'
                self.reject_change(line,line+'        if: false\n')

    def test_job_dependency_and_hidden_failures(self):
        for old,new in (
            ('  build-prefix:\n','  build-prefix:\n    if: false\n'),
            ('  build-prefix:\n','  build-prefix:\n    "if": false\n'),
            ('    needs: [build-prefix]\n',''),
            ('    needs: [build-final, metadata]\n','    needs: [build-prefix]\n'),
            ('      - name: Build the dependency prefix\n','      - name: Build the dependency prefix\n        continue-on-error: true\n'),
            ('      - name: Build the dependency prefix\n','      - name: Build the dependency prefix\n        run: true\n'),
            ('      - name: Build the dependency prefix\n','      - name: Build the dependency prefix\n        "if": false\n'),
            ('      - name: Check proof source\n','      - name: Check proof source\n        shell: echo {0}\n'),
            ('      - name: Build the dependency prefix\n','      - name: Build the dependency prefix\n        shell: echo {0}\n')):
            with self.subTest(change=new):
                self.reject_change(old,new)

    def test_cuts_and_receipt_coverage_arguments(self):
        for old,new in (
            ('--stage prefix --cut 679','--stage prefix --cut 680'),
            ('--stage final --cut 679','--stage final --cut 678'),
            ('--check-tracked-coverage --batch-size 2','--batch-size 2'),
            ('--prior-stage-dir .verification/restored-prefix','--prior-stage-dir .verification/other'),
            ('--stage-receipt .verification/build-complete-stage.json',''),
            ('--ledger .verification/bounded-project-build.jsonl',''),
            ('--receipt .verification/build-prefix-stage.json',''),
            ('--output .verification/restored-prefix','--output .verification/other')):
            with self.subTest(change=old):
                self.reject_change(old,new)

    def test_same_sha_run_and_attempt_are_material(self):
        for part in ('-${{ github.sha }}','-${{ github.run_id }}','-${{ github.run_attempt }}'):
            with self.subTest(part=part):
                self.reject_change(PREFIX_ARTIFACT,PREFIX_ARTIFACT.replace(part,''))

    def test_authenticated_restore_and_complete_upload(self):
        for old,new in (
            ('restore --project . --cut 679','restore --project . --cut 679 --run 123'),
            ('          path: ${{ runner.temp }}/proof-prefix/','          path: ${{ runner.temp }}/proof-prefix/build.tar.gz'),
            ('          if-no-files-found: error','          if-no-files-found: warn'),
            ('GH_TOKEN: ${{ github.token }}','GH_TOKEN: untrusted')):
            with self.subTest(change=old):
                self.reject_change(old,new)

    def test_fresh_direct_audit(self):
        for replacement in ('run: lake build +Test.Axioms','run: true'):
            self.reject_change('run: lake env lean Test/Axioms.lean',replacement)

    def test_preserved_metadata_semantic_archive_and_kernel_blocks(self):
        for old,new in (
            ('python3 -O scripts/test_metadata_policy.py\n','true\n'),
            ('--require-hashes --no-deps','--no-deps'),
            ('python-version: "3.11.10"','python-version: "3.14"'),
            ('--verify-only --expected-commit "$GITHUB_SHA"','--prepare-only'),
            ('python3 scripts/check-release.py --lean-controls','true'),
            ('lake build +Challenge','true'),
            ("'archive_sha256': digest","'archive_sha256': 'unchecked'"),
            ('name: linux-proof-build-${{ github.sha }}','name: previous-proof-build'),
            ("receipt['commit'] != commit",'False')):
            with self.subTest(change=old):
                self.reject_change(old,new)

    def test_duplicate_job_or_step_and_commented_gate(self):
        self.reject_change('  build-final:\n','  build-prefix:\n')
        line='      - name: Recompute the global axiom audit\n'
        self.reject_change(line,line+'        run: true\n'+line)
        self.reject_change(line,'      # - name: Recompute the global axiom audit\n')

    def test_old_cache_feature_retired(self):
        for value in ('reuse_reviewed_proof_cache','restore-reviewed-proof-cache.py','test_reviewed_proof_cache.py'):
            with self.subTest(value=value):
                self.reject_change('  workflow_dispatch:\n','  workflow_dispatch:\n    # '+value+'\n')

    def test_pinned_bootstrap(self):
        self.reject_change('download/v4.2.3/elan-x86_64','download/latest/elan-x86_64')
        self.reject_change('run: lake exe cache get','run: true')


if __name__ == '__main__':
    unittest.main()
