#!/usr/bin/env python3
"""Offline staged-build protocol controls. No project proof build or GitHub call."""
from contextlib import redirect_stdout
import copy
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import bounded_project_build as b


def fixture(root):
    sources = {
        'DR.lean': 'import DR.Base\n',
        'DR/Base.lean': 'namespace DittertRybin\ntheorem base : True := True.intro\nend DittertRybin\n',
        'Solution.lean': 'import DR\n',
        'Test/Axioms.lean': 'import DR\nimport Solution\n',
        'Test.lean': 'import Test.Axioms\n',
    }
    for name, source in sources.items():
        path = root / name; path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source)
    plan = b.make_plan(root)
    b.validate_tracked_coverage(plan, list(sources))
    return plan


def fake_context(plan, cut=1):
    report = json.loads(json.dumps(plan.report()))
    return {'schema': 1, 'repository': 'JD-Jones-ASES/dr-lean', 'run_id': 10,
            'run_attempt': 1, 'commit': 'a'*40, 'git_tree': 'b'*40,
            'workflow': '.github/workflows/development.yml', 'workflow_sha256': 'c'*64,
            'toolchain': 'leanprover/lean4:v4.33.0',
            'platform': {'system': 'Linux', 'machine': 'x86_64'},
            'inputs': {'lake-manifest.json': 'd'*64}, 'dependencies': {},
            'plan': report, 'plan_sha256': b.sha256_bytes(b.canonical_bytes(report)), 'cut': cut}


def success(argv, **kwargs):
    return subprocess.CompletedProcess(argv, 0, 'fixture compile passed\n')


class StageBuildTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='staged-build-controls-')
        self.root = Path(self.temp.name)
        self.plan = fixture(self.root)
        self.context = fake_context(self.plan)

    def tearDown(self):
        self.temp.cleanup()

    def build(self, stage, runner=success, receipt=None, ledger=None, context_reader=None):
        log, printed = io.StringIO(), io.StringIO()
        def current(plan, cut):
            b.verify_sources(plan)
            return self.context
        with redirect_stdout(printed):
            records, output = b.run_stage(self.plan, stage, self.context['cut'],
                self.context, log, runner=runner, prior_receipt=receipt,
                prior_ledger=ledger, context_reader=context_reader or current)
        return records, output, log.getvalue(), printed.getvalue()

    def prefix(self):
        return self.build('prefix')

    def rejected_receipt(self, receipt, ledger, context=None):
        with self.assertRaises(ValueError):
            b.validate_prefix_receipt(receipt, ledger, context or self.context)

    def test_prefix_is_explicitly_partial_and_has_no_root_check(self):
        records, receipt, ledger, output = self.prefix()
        self.assertEqual(len(records), 1)
        self.assertEqual(receipt['status'], 'partial_stage_passed')
        self.assertEqual(receipt['interval'], [0, 1])
        self.assertIs(receipt['build_complete'], False)
        self.assertIs(receipt['root_check'], False)
        self.assertIs(receipt['release_verified'], False)
        self.assertNotIn('root_check', output)
        self.assertNotIn('complete_build', output)
        self.assertEqual(b.validate_prefix_receipt(receipt, ledger, self.context), records)

    def test_split_commands_cover_all_modules_once_then_one_root_check(self):
        calls = []
        def runner(argv, **kwargs):
            calls.append(argv)
            return success(argv, **kwargs)
        _, prefix, ledger, _ = self.build('prefix', runner)
        records, final, full, output = self.build('final', runner, prefix, ledger)
        requested = [arg[1:] for command in calls[:-1] for arg in command[3:]]
        self.assertEqual(requested, list(self.plan.order))
        self.assertTrue(all(1 <= len(command[3:]) <= 2 for command in calls))
        self.assertEqual(calls[-1], ['lake', '--wfail', 'build', '+DR', '+Test'])
        self.assertEqual(sum(r['phase'] == 'root_check' for r in records), 1)
        self.assertEqual(final['status'], 'complete_build')
        self.assertIs(final['build_complete'], True)
        self.assertIs(final['release_verified'], False)
        self.assertEqual(final['covered_batches'], len(self.plan.batches))
        self.assertTrue(full.startswith(ledger))
        self.assertEqual(final['previous_receipt_sha256'], b.sha256_bytes(b.canonical_bytes(prefix)))
        self.assertEqual(b.validate_stage_ledger(full, self.context, complete=True), records)

    def test_default_and_split_actual_target_sequences_match(self):
        calls = []
        def runner(argv, **kwargs):
            calls.append(argv)
            return success(argv, **kwargs)
        with redirect_stdout(io.StringIO()):
            b.run_plan(self.plan, runner=runner)
        whole = copy.deepcopy(calls); calls.clear()
        _, receipt, ledger, _ = self.build('prefix', runner)
        self.build('final', runner, receipt, ledger)
        self.assertEqual(calls, whole)

    def test_final_without_prefix_is_rejected_before_commands(self):
        with patch(__name__ + '.success') as runner:
            with self.assertRaises(ValueError):
                self.build('final', runner)
            runner.assert_not_called()

    def test_prefix_cannot_inherit_a_prior_receipt(self):
        _, receipt, ledger, _ = self.prefix()
        with self.assertRaises(ValueError):
            self.build('prefix', receipt=receipt, ledger=ledger)

    def test_wrong_commit_run_attempt_tree_toolchain_or_plan_rejects(self):
        _, receipt, ledger, _ = self.prefix()
        for key, value in (('commit', 'f'*40), ('git_tree', 'f'*40), ('run_id', 11),
                           ('run_attempt', 2), ('repository', 'wrong/repo'),
                           ('toolchain', 'wrong'), ('workflow_sha256', 'f'*64),
                           ('inputs', {'lake-manifest.json': 'changed'}),
                           ('dependencies', {'mathlib': {'revision': 'changed'}}),
                           ('platform', {'system': 'Darwin', 'machine': 'arm64'}),
                           ('plan_sha256', 'f'*64), ('cut', 2)):
            with self.subTest(key=key):
                changed = copy.deepcopy(self.context); changed[key] = value
                self.rejected_receipt(receipt, ledger, changed)

    def test_prefix_cannot_forge_complete_or_change_scope(self):
        _, receipt, ledger, _ = self.prefix()
        for key, value in (('status', 'complete_build'), ('stage', 'final'),
                           ('interval', [1, 2]), ('covered_batches', 2),
                           ('interval', [False, True]), ('covered_batches', True), ('schema', True),
                           ('root_check', True), ('build_complete', True),
                           ('release_verified', True), ('previous_receipt_sha256', 'f'*64)):
            with self.subTest(key=key):
                self.rejected_receipt({**receipt, key:value}, ledger)

    def test_ledger_digest_rejects_tampered_bytes(self):
        _, receipt, ledger, _ = self.prefix()
        self.rejected_receipt(receipt, ledger + '\n')
        self.rejected_receipt({**receipt, 'ledger_sha256':'f'*64}, ledger)

    def test_rehashed_missing_extra_and_reordered_batches_reject(self):
        self.context = fake_context(self.plan, 2)
        records, receipt, _, _ = self.prefix()
        for changed in (records[:1], records + records[:1], list(reversed(records))):
            ledger = ''.join(json.dumps(r) + '\n' for r in changed)
            self.rejected_receipt({**receipt, 'ledger_sha256': b.sha256_bytes(ledger.encode())}, ledger)

    def test_rehashed_failed_unbounded_or_weakened_commands_reject(self):
        records, receipt, _, _ = self.prefix()
        for key, value in (('status', 'failed'), ('exit_code', 143), ('exit_code', False),
                           ('batch_index', 1), ('batch_index', False), ('phase', 'root_check'),
                           ('argv', ['lake', 'build', '+DR.Base', '+DR']),
                           ('modules', ['DR.Base']), ('seconds', float('nan')), ('output', None)):
            with self.subTest(key=key):
                changed = copy.deepcopy(records); changed[0][key] = value
                ledger = ''.join(json.dumps(r) + '\n' for r in changed)
                self.rejected_receipt({**receipt, 'ledger_sha256': b.sha256_bytes(ledger.encode())}, ledger)

    def test_duplicate_json_keys_reject(self):
        with self.assertRaisesRegex(ValueError, 'Duplicate'):
            b.strict_json('{"status":"failed","status":"passed"}')

    def test_failed_prefix_retains_failure_log_without_complete_receipt(self):
        log, output = io.StringIO(), io.StringIO()
        calls = []
        def failed(argv, **kwargs):
            calls.append(argv)
            return subprocess.CompletedProcess(argv, -15, 'interrupted')
        with redirect_stdout(output), self.assertRaises(subprocess.CalledProcessError) as caught:
            b.run_stage(self.plan, 'prefix', 1, self.context, log, runner=failed,
                        context_reader=lambda p,c:self.context)
        self.assertEqual(caught.exception.returncode, -15)
        self.assertEqual(b.subprocess_exit_status(caught.exception.returncode), 143)
        self.assertEqual(len(calls), 1)
        self.assertIn('"status": "failed"', log.getvalue())
        self.assertNotIn('partial_stage_passed', output.getvalue())

    def test_failed_suffix_or_root_never_emits_complete(self):
        _, receipt, ledger, _ = self.prefix()
        for fail_call in (1, len(self.plan.batches)):
            calls = []
            log, output = io.StringIO(), io.StringIO()
            def failed(argv, **kwargs):
                calls.append(argv)
                return subprocess.CompletedProcess(argv, 1 if len(calls) == fail_call else 0, 'result')
            with redirect_stdout(output), self.assertRaises(subprocess.CalledProcessError):
                b.run_stage(self.plan, 'final', 1, self.context, log, runner=failed,
                    prior_receipt=receipt, prior_ledger=ledger, context_reader=lambda p,c:self.context)
            self.assertTrue(log.getvalue().startswith(ledger))
            self.assertNotIn('complete_build', output.getvalue())

    def test_source_change_during_prefix_rejects_completion(self):
        def changed(argv, **kwargs):
            (self.root / 'DR/Base.lean').write_text('changed')
            return success(argv, **kwargs)
        with self.assertRaisesRegex(ValueError, 'source changed'):
            self.build('prefix', runner=changed)

    def test_source_change_between_stages_rejects_before_suffix(self):
        _, receipt, ledger, _ = self.prefix()
        (self.root / 'DR/Base.lean').write_text('changed')
        with self.assertRaisesRegex(ValueError, 'source changed'):
            self.build('final', receipt=receipt, ledger=ledger)

    def test_context_change_after_successful_commands_rejects(self):
        calls = []
        def changed(plan, cut):
            calls.append(1)
            return self.context if len(calls) == 1 else {**self.context, 'run_attempt': 2}
        with self.assertRaisesRegex(ValueError, 'context changed during'):
            self.build('prefix', context_reader=changed)

    def test_complete_ledger_cannot_be_replaced_by_a_prefix(self):
        _, _, ledger, _ = self.prefix()
        with self.assertRaises(ValueError):
            b.validate_stage_ledger(ledger, self.context, complete=True)

    def test_receipt_invalidated_before_a_new_invalid_stage_invocation(self):
        receipt = self.root / 'old-receipt.json'; receipt.write_text('{"status":"complete_build"}')
        result = subprocess.run([sys.executable, b.__file__, '--root-dir', str(self.root),
            '--stage', 'prefix', '--cut', '0', '--stage-receipt', str(receipt),
            '--report', str(self.root / 'plan.json'), '--log', str(self.root / 'log.jsonl')],
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(receipt.exists())

    def test_atomic_receipt_write_and_no_symlink_write(self):
        path = self.root / 'receipt.json'
        b.invalidate_stage_receipt(path)
        b.write_stage_receipt(path, {'status':'partial_stage_passed'})
        self.assertEqual(json.loads(path.read_text()), {'status':'partial_stage_passed'})
        victim = self.root / 'victim'; victim.write_text('unchanged')
        path.unlink(); path.symlink_to(victim)
        with self.assertRaises(ValueError):
            b.invalidate_stage_receipt(path)
        self.assertEqual(victim.read_text(), 'unchanged')

    def test_final_cli_cannot_invalidate_or_overwrite_prefix_evidence(self):
        directory = self.root / 'prefix'; directory.mkdir()
        receipt = directory / 'stage.json'; receipt.write_text('preserve original prefix')
        result = subprocess.run([sys.executable, b.__file__, '--root-dir', str(self.root),
            '--stage', 'final', '--cut', '1', '--prior-stage-dir', str(directory),
            '--stage-receipt', str(receipt), '--report', str(self.root / 'plan.json'),
            '--log', str(self.root / 'log.jsonl')], text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(receipt.read_text(), 'preserve original prefix')

    def test_unsafe_other_output_rejects_and_invalidates_safe_old_receipt(self):
        directory = self.root / 'prefix'; directory.mkdir()
        evidence = directory / 'stage.json'; evidence.write_text('preserve prefix evidence')
        receipt = self.root / 'old-final.json'
        for flag in ('--report', '--log'):
            receipt.write_text('{"status":"complete_build"}')
            outputs = {'--report':str(self.root/'plan.json'), '--log':str(self.root/'log.jsonl')}
            outputs[flag] = str(evidence)
            result = subprocess.run([sys.executable, b.__file__, '--root-dir', str(self.root),
                '--stage', 'final', '--cut', '1', '--prior-stage-dir', str(directory),
                '--stage-receipt', str(receipt), '--report', outputs['--report'],
                '--log', outputs['--log']], text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            self.assertNotEqual(result.returncode, 0)
            self.assertFalse(receipt.exists())
            self.assertEqual(evidence.read_text(), 'preserve prefix evidence')

    def real_context_fixture(self):
        (self.root / '.github/workflows').mkdir(parents=True)
        (self.root / '.github/workflows/development.yml').write_text('name: fixture\n')
        (self.root / 'scripts').mkdir()
        (self.root / 'scripts/bounded_project_build.py').write_bytes(Path(b.__file__).read_bytes())
        (self.root / 'scripts/stage_build_artifact.py').write_text('# fixture context only\n')
        (self.root / 'lean-toolchain').write_text('leanprover/lean4:v4.33.0\n')
        (self.root / 'lake-manifest.json').write_text('{"packages":[]}\n')
        (self.root / 'lakefile.toml').write_text('name = "stageFixture"\n')
        (self.root / '.gitignore').write_text('.lake/\n.verification/\n__pycache__/\n')
        def git(*args):
            return subprocess.check_output(['git','-C',str(self.root),*args], stderr=subprocess.PIPE).decode().strip()
        git('init','-q'); git('config','user.name','Stage Test'); git('config','user.email','stage@example.invalid')
        git('add','.'); git('commit','-qm','fixture')
        env = {'GITHUB_SHA':git('rev-parse','HEAD'),'GITHUB_REPOSITORY':'JD-Jones-ASES/dr-lean',
               'GITHUB_RUN_ID':'10','GITHUB_RUN_ATTEMPT':'1'}
        return git, env

    def test_actual_clean_git_context_is_json_stable_and_source_bound(self):
        _, env = self.real_context_fixture()
        with patch.dict(os.environ, env):
            context = b.stage_context(self.plan, 1)
        self.assertEqual(context, json.loads(json.dumps(context)))
        self.assertEqual(context['commit'], env['GITHUB_SHA'])
        self.assertEqual(context['cut'], 1)
        self.assertIn('scripts/bounded_project_build.py', context['inputs'])
        self.assertEqual(context['plan_sha256'], b.sha256_bytes(b.canonical_bytes(context['plan'])))

    def test_actual_context_rejects_dirty_tree_wrong_sha_run_and_cuts(self):
        _, env = self.real_context_fixture()
        for key, value in (('GITHUB_SHA','f'*40), ('GITHUB_REPOSITORY','other/repo'),
                           ('GITHUB_RUN_ID',''), ('GITHUB_RUN_ATTEMPT','0')):
            with patch.dict(os.environ, {**env,key:value}), self.assertRaises(ValueError):
                b.stage_context(self.plan,1)
        with patch.dict(os.environ, env):
            for cut in (0,len(self.plan.batches),True):
                with self.assertRaises(ValueError): b.stage_context(self.plan,cut)
            (self.root / 'formalization.yaml').write_text('unexpected untracked source')
            with self.assertRaisesRegex(ValueError,'clean'):
                b.stage_context(self.plan,1)

    def test_missing_critical_helper_and_changed_tracked_coverage_reject(self):
        git, env = self.real_context_fixture()
        (self.root / 'scripts/stage_build_artifact.py').unlink()
        git('add','-u'); git('commit','-qm','remove helper')
        env['GITHUB_SHA'] = git('rev-parse','HEAD')
        with patch.dict(os.environ,env), self.assertRaisesRegex(ValueError,'staged input'):
            b.stage_context(self.plan,1)
        (self.root / 'DR/Extra.lean').write_text('example : True := True.intro\n')
        git('add','.'); git('commit','-qm','unimported module')
        env['GITHUB_SHA'] = git('rev-parse','HEAD')
        with patch.dict(os.environ,env), self.assertRaisesRegex(ValueError,'coverage mismatch'):
            b.stage_context(self.plan,1)

    def test_actual_dependency_revision_and_dirty_source_are_rejected(self):
        git, env = self.real_context_fixture()
        dependency = self.root / '.lake/packages/example'; dependency.mkdir(parents=True)
        def dep(*args):
            return subprocess.check_output(['git','-C',str(dependency),*args], stderr=subprocess.PIPE).decode().strip()
        dep('init','-q'); dep('config','user.name','Stage Test'); dep('config','user.email','stage@example.invalid')
        (dependency / 'Source.lean').write_text('def x : Nat := 0\n')
        dep('add','.'); dep('commit','-qm','dependency')
        revision = dep('rev-parse','HEAD')
        manifest = {'packages':[{'name':'example','type':'git','rev':revision,'url':'https://example.invalid/pinned'}]}
        (self.root / 'lake-manifest.json').write_text(json.dumps(manifest))
        git('add','.'); git('commit','-qm','pin dependency'); env['GITHUB_SHA'] = git('rev-parse','HEAD')
        with patch.dict(os.environ,env):
            context = b.stage_context(self.plan,1)
            self.assertEqual(context['dependencies']['example']['revision'], revision)
            (dependency / 'Source.lean').write_text('changed source')
            with self.assertRaisesRegex(ValueError,'dirty'):
                b.stage_context(self.plan,1)
            dep('add','.'); dep('commit','-qm','different revision')
            with self.assertRaisesRegex(ValueError,'revision changed'):
                b.stage_context(self.plan,1)


if __name__ == '__main__':
    unittest.main(verbosity=2)
