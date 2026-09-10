#!/usr/bin/env python3
"""Offline controls for pinned compiled-input reuse; no GitHub/Lean/kernel calls."""
from __future__ import annotations

from contextlib import ExitStack, redirect_stdout
import copy
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch
import zipfile

SPEC = importlib.util.spec_from_file_location('reviewed_cache',
    Path(__file__).with_name('restore-reviewed-proof-cache.py'))
cache = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = cache
SPEC.loader.exec_module(cache)


def producer():
    run = {'id': cache.RUN_ID, 'head_sha': cache.PRODUCER, 'run_attempt': 1,
           'path': cache.WORKFLOW, 'event': 'push', 'status': 'in_progress',
           'repository': {'full_name': cache.REPOSITORY},
           'head_repository': {'full_name': cache.REPOSITORY}}
    job = {'id': 42, 'name': 'build', 'run_id': cache.RUN_ID,
           'head_sha': cache.PRODUCER, 'run_attempt': 1,
           'status': 'completed', 'conclusion': 'success',
           'steps': [{'name': n, 'status': 'completed', 'conclusion': 'success'}
                     for n in cache.BUILD_STEPS]}
    return run, {'total_count': 1, 'jobs': [job]}


def artifacts():
    return {'total_count': 2, 'artifacts': [
        {'id': i, 'name': kind + '-' + cache.PRODUCER, 'expired': False,
         'workflow_run': {'id': cache.RUN_ID, 'head_sha': cache.PRODUCER}}
        for i, kind in enumerate(('linux-proof-build', 'proof-receipts'), 1)]}


def plan_and_ledger():
    names = ['DR', 'Solution', 'Test.Axioms', 'Test']
    batches = [names[:2], names[2:]]
    plan = {'project_module_count': 4, 'batch_count': 2, 'batches': batches,
            'modules': [{'name': n} for n in names],
            'tracked_project_modules': names, 'tracked_coverage_checked': True}
    records = []
    for batch, phase in [(b, 'module_batch') for b in batches] + [(['DR', 'Test'], 'root_check')]:
        records.append({'status': 'passed', 'exit_code': 0, 'phase': phase,
                        'modules': batch, 'argv': ['lake', '--wfail', 'build', *('+' + n for n in batch)],
                        'output': 'Audited 123 project declarations.\n' if 'Test.Axioms' in batch else ''})
    return plan, records


def ledger(records):
    return ''.join(json.dumps(r) + '\n' for r in records)


def tar_bytes(extra=(), omit=None):
    entries = [('.lake/build', tarfile.DIRTYPE, b'')]
    for module in ('DR', 'Solution', 'Test/Axioms', 'Test', 'Challenge'):
        for suffix in ('.olean', '.trace'):
            name = '.lake/build/lib/lean/' + module + suffix
            if name != omit:
                entries.append((name, tarfile.REGTYPE, b'compiled fixture\n'))
    entries.extend(extra)
    output = io.BytesIO()
    with tarfile.open(fileobj=output, mode='w:gz') as archive:
        for name, kind, data in entries:
            entry = tarfile.TarInfo(name)
            entry.type = kind
            entry.mode = 0o644
            entry.size = len(data) if kind == tarfile.REGTYPE else 0
            if kind in (tarfile.LNKTYPE, tarfile.SYMTYPE):
                entry.linkname = '/tmp/outside'
            archive.addfile(entry, io.BytesIO(data) if entry.size else None)
    return output.getvalue()


class ReviewedCacheTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='reviewed-cache-controls-')
        self.root = Path(self.temp.name)

    def tearDown(self):
        self.temp.cleanup()

    def reject(self, function, *args):
        with self.assertRaises((ValueError, OSError, tarfile.TarError, zipfile.BadZipFile,
                                subprocess.CalledProcessError)):
            function(*args)

    def check_ledger(self, plan, records, expected=None):
        with patch.object(cache, 'MODULE_COUNT', 4), patch.object(cache, 'BATCH_COUNT', 2):
            return cache.validate_ledger(plan, plan if expected is None else expected, ledger(records))

    def test_exact_pin_and_allowlist(self):
        self.assertEqual(cache.PRODUCER, 'da67b34f27d7b590bb4596435d0f77c48c192ccc')
        self.assertEqual((cache.RUN_ID, cache.RUN_ATTEMPT), (34432295599, 1))
        self.assertEqual(cache.ALLOWLIST, frozenset({
            'formalization.yaml', 'scripts/check-official-metadata.py',
            'scripts/test_metadata_policy.py', 'scripts/restore-reviewed-proof-cache.py',
            'scripts/test_reviewed_proof_cache.py', '.github/workflows/development.yml',
            'docs/VERIFICATION.md', 'docs/history/2026-09-10-metadata-policy.md'}))

    def test_allowed_metadata_helper_changes_are_reported(self):
        original = {'formalization.yaml': ('100644', 'blob', 'a'),
                    'DR.lean': ('100644', 'blob', 'proof')}
        changed = {**original, 'formalization.yaml': ('100644', 'blob', 'b'),
                   'scripts/test_reviewed_proof_cache.py': ('100755', 'blob', 'c')}
        self.assertEqual(cache.compare_trees(original, changed),
                         ['formalization.yaml', 'scripts/test_reviewed_proof_cache.py'])

    def test_all_proof_interface_dependency_and_gate_changes_reject(self):
        paths = ('DR.lean', 'Test.lean', 'Challenge.lean', 'Solution.lean', 'DR/X.lean',
                 'comparator.json', 'release-targets.json', 'lake-manifest.json', 'lakefile.toml',
                 'lean-toolchain', 'data/seed.json', 'scripts/check-source.py',
                 'scripts/check-release.py', 'scripts/bounded_project_build.py',
                 'scripts/verify-comparator.py', 'README.md', 'DISCLOSURE.md', 'docs/SOURCES.md')
        for path in paths:
            with self.subTest(path=path):
                self.reject(cache.compare_trees, {path: ('100644', 'blob', 'a')},
                            {path: ('100644', 'blob', 'b')})

    def test_extra_deleted_and_mode_changed_proof_files_reject(self):
        entry = {'DR/X.lean': ('100644', 'blob', 'a')}
        self.reject(cache.compare_trees, {}, entry)
        self.reject(cache.compare_trees, entry, {})
        self.reject(cache.compare_trees, entry, {'DR/X.lean': ('100755', 'blob', 'a')})

    def test_allowlist_prefix_and_symlink_mutations_reject(self):
        self.reject(cache.compare_trees, {}, {'docs/history/other.md': ('100644', 'blob', 'x')})
        self.reject(cache.compare_trees, {}, {'formalization.yaml': ('120000', 'blob', 'x')})

    def test_complete_build_can_be_used_before_unrelated_job_finishes(self):
        run, jobs = producer()
        self.assertEqual(cache.validate_producer(run, jobs), 42)
        run.update(status='completed', conclusion='failure')  # Metadata status is not a kernel pass.
        self.assertEqual(cache.validate_producer(run, jobs), 42)

    def test_wrong_run_sha_attempt_workflow_event_repository_reject(self):
        run, jobs = producer()
        for key, value in (('id', 1), ('head_sha', 'f'*40), ('run_attempt', 2),
                           ('path', 'other.yml'), ('event', 'pull_request'),
                           ('repository', {'full_name': 'other/repo'}),
                           ('head_repository', {'full_name': 'other/repo'})):
            with self.subTest(key=key):
                self.reject(cache.validate_producer, {**run, key: value}, jobs)

    def test_pending_failed_cancelled_timedout_build_rejects(self):
        run, jobs = producer()
        for state, conclusion in (('in_progress', None), ('completed', 'failure'),
                                  ('completed', 'cancelled'), ('completed', 'timed_out')):
            changed = copy.deepcopy(jobs)
            changed['jobs'][0].update(status=state, conclusion=conclusion)
            self.reject(cache.validate_producer, run, changed)

    def test_job_identity_missing_duplicate_truncated_reject(self):
        run, jobs = producer()
        for key, value in (('head_sha', 'f'*40), ('run_attempt', 2), ('run_id', 1)):
            changed = copy.deepcopy(jobs)
            changed['jobs'][0][key] = value
            self.reject(cache.validate_producer, run, changed)
        self.reject(cache.validate_producer, run, {'total_count': 0, 'jobs': []})
        self.reject(cache.validate_producer, run, {'total_count': 2, 'jobs': jobs['jobs'] * 2})
        self.reject(cache.validate_producer, run, {'total_count': 2, 'jobs': jobs['jobs']})

    def test_skipped_source_build_audit_semantic_archive_steps_reject(self):
        run, jobs = producer()
        for i in range(len(cache.BUILD_STEPS)):
            changed = copy.deepcopy(jobs)
            changed['jobs'][0]['steps'][i]['conclusion'] = 'skipped'
            self.reject(cache.validate_producer, run, changed)

    def test_exact_complete_artifacts_selected(self):
        result = cache.select_artifacts(artifacts())
        self.assertEqual(set(result), {'linux-proof-build', 'proof-receipts'})

    def test_expired_partial_missing_duplicate_wrong_artifacts_reject(self):
        for key, value in (('expired', True), ('id', 0), ('name', 'partial-build'),
                           ('workflow_run', {'id': 1, 'head_sha': cache.PRODUCER}),
                           ('workflow_run', {'id': cache.RUN_ID, 'head_sha': 'f'*40})):
            changed = artifacts()
            changed['artifacts'][0][key] = value
            self.reject(cache.select_artifacts, changed)
        changed = artifacts()
        changed['artifacts'].append(changed['artifacts'][0]); changed['total_count'] = 3
        self.reject(cache.select_artifacts, changed)
        changed = artifacts(); changed['total_count'] = 3
        self.reject(cache.select_artifacts, changed)

    def test_duplicate_json_key_rejected_under_optimization(self):
        self.reject(cache.load_json, '{"status":"failed","status":"passed"}')

    def test_complete_ledger_and_audit_accept(self):
        plan, records = plan_and_ledger()
        self.check_ledger(plan, records)

    def test_ledger_prefix_extra_reordered_missing_root_reject(self):
        plan, records = plan_and_ledger()
        for changed in (records[:-1], records[:1], records + records[-1:],
                        [records[1], records[0], records[2]]):
            self.reject(self.check_ledger, plan, changed)

    def test_ledger_failed_command_changed_missing_warning_policy_reject(self):
        plan, records = plan_and_ledger()
        for key, value in (('status', 'failed'), ('exit_code', 143),
                           ('modules', ['DR']), ('phase', 'partial'),
                           ('argv', ['lake', 'build', '+DR', '+Solution'])):
            changed = copy.deepcopy(records); changed[0][key] = value
            self.reject(self.check_ledger, plan, changed)

    def test_missing_or_empty_global_audit_reject(self):
        plan, records = plan_and_ledger()
        for output in ('', 'Audited 0 project declarations.', 'Axiom audit skipped.'):
            changed = copy.deepcopy(records); changed[1]['output'] = output
            self.reject(self.check_ledger, plan, changed)

    def test_changed_consumer_plan_and_duplicate_module_reject(self):
        plan, records = plan_and_ledger()
        expected = copy.deepcopy(plan); expected['modules'][0]['sha256'] = 'changed'
        self.reject(self.check_ledger, plan, records, expected)
        changed = copy.deepcopy(plan); changed['batches'][1][0] = 'DR'
        self.reject(self.check_ledger, changed, records)
        changed = copy.deepcopy(plan); changed['tracked_coverage_checked'] = False
        self.reject(self.check_ledger, changed, records)

    def test_archive_receipt_exact_digest_commit_toolchain(self):
        archive = self.root / 'build.tar.gz'; archive.write_bytes(tar_bytes())
        receipt = {'commit': cache.PRODUCER, 'toolchain': cache.TOOLCHAIN,
                   'archive_sha256': cache.digest(archive)}
        cache.check_receipt(receipt, archive)
        for key, value in (('commit', 'f'*40), ('toolchain', 'other'), ('archive_sha256', '0'*64)):
            self.reject(cache.check_receipt, {**receipt, key: value}, archive)
        archive.write_bytes(archive.read_bytes() + b'corrupt')
        self.reject(cache.check_receipt, receipt, archive)

    def unpack(self, data):
        archive = self.root / 'build.tar.gz'; archive.write_bytes(data)
        target = self.root / 'staged'; target.mkdir(exist_ok=True)
        return cache.unpack_build(archive, target, ['DR', 'Solution', 'Test.Axioms', 'Test'])

    def test_safe_regular_build_files_and_traces_restored(self):
        self.assertGreater(self.unpack(tar_bytes()), 0)
        self.assertEqual((self.root / 'staged/.lake/build/lib/lean/DR.olean').read_bytes(),
                         b'compiled fixture\n')
        self.assertFalse((self.root / 'staged/DR.lean').exists())

    def test_archive_traversal_absolute_other_tree_backslash_reject(self):
        for path in ('../escape', '/tmp/escape', '.lake/build/../../DR.lean',
                     '.lake/packages/mathlib/Mathlib.olean', 'DR.lean', '.lake/build\\escape'):
            with self.subTest(path=path):
                self.reject(self.unpack, tar_bytes([(path, tarfile.REGTYPE, b'x')]))
        self.assertFalse((self.root / 'escape').exists())

    def test_archive_links_devices_fifo_reject_before_extraction(self):
        for kind in (tarfile.SYMTYPE, tarfile.LNKTYPE, tarfile.CHRTYPE, tarfile.BLKTYPE, tarfile.FIFOTYPE):
            self.reject(self.unpack, tar_bytes([('.lake/build/bad', kind, b'')]))
        self.assertFalse((self.root / 'staged/.lake').exists())

    def test_duplicate_archive_file_reject(self):
        self.reject(self.unpack, tar_bytes([('.lake/build/lib/lean/DR.olean', tarfile.REGTYPE, b'x')]))

    def test_missing_required_olean_trace_challenge_reject(self):
        for path in ('.lake/build/lib/lean/DR.olean', '.lake/build/lib/lean/Test/Axioms.trace',
                     '.lake/build/lib/lean/Challenge.olean'):
            self.reject(self.unpack, tar_bytes(omit=path))

    def test_archive_size_cap_rejects_before_extraction(self):
        with patch.object(cache, 'MAX_BYTES', 1):
            self.reject(self.unpack, tar_bytes())

    def test_unsafe_zip_duplicate_and_missing_members_reject(self):
        for name in ('../escape', '/tmp/escape', 'safe'):
            file = self.root / 'archive.zip'
            with zipfile.ZipFile(file, 'w') as z:
                z.writestr(name, b'content')
            self.reject(cache.read_zip_files, file, {'wanted'}, self.root)

    def test_duplicate_zip_members_reject(self):
        file = self.root / 'duplicate.zip'
        with zipfile.ZipFile(file, 'w') as z:
            z.writestr('wanted', b'one')
            with self.assertWarns(UserWarning):
                z.writestr('wanted', b'two')
        self.reject(cache.read_zip_files, file, {'wanted'}, self.root)

    def test_corrupt_tar_and_zip_reject(self):
        self.reject(self.unpack, b'not a gzip archive')
        file = self.root / 'bad.zip'; file.write_bytes(b'not a zip')
        self.reject(cache.read_zip_files, file, {'wanted'}, self.root)

    def test_download_pins_artifact_id_and_checks_zip_digest(self):
        target = self.root / 'download.zip'
        def run(argv, **kwargs):
            self.assertEqual(argv, ['gh', 'api', 'repos/JD-Jones-ASES/dr-lean/actions/artifacts/123/zip'])
            self.assertIs(kwargs['check'], True)
            self.assertNotIn('shell', kwargs)
            kwargs['stdout'].write(b'archive bytes')
        with patch.object(cache.subprocess, 'run', side_effect=run):
            cache.download_artifact({'id': 123,
                'digest': 'sha256:' + hashlib.sha256(b'archive bytes').hexdigest()}, target)
            self.reject(cache.download_artifact, {'id': 123, 'digest': 'sha256:' + '0'*64},
                        self.root / 'bad-download.zip')

    def test_stale_receipt_invalidated_even_wrong_platform(self):
        parent = self.root / '.verification'; parent.mkdir()
        receipt = parent / 'reviewed-proof-cache.json'; receipt.write_text('{"status":"old"}')
        with patch.object(cache.platform, 'system', return_value='Darwin'):
            self.reject(cache.restore, self.root, 'f'*40)
        self.assertFalse(receipt.exists())

    def test_receipt_symlink_cannot_overwrite_other_file(self):
        victim = self.root / 'outside'; victim.write_text('preserved')
        parent = self.root / '.verification'; parent.mkdir()
        (parent / 'reviewed-proof-cache.json').symlink_to(victim)
        self.reject(cache.receipt_path, self.root)
        self.assertEqual(victim.read_text(), 'preserved')

    def test_safe_subprocess_argv_no_shell(self):
        with patch.object(cache.subprocess, 'check_output', return_value=b'ok') as run:
            self.assertEqual(cache.git(Path('/a path;$literal'), 'show', 'HEAD:file'), b'ok')
        self.assertEqual(run.call_args.args[0], ['git', '-C', '/a path;$literal', 'show', 'HEAD:file'])
        self.assertNotIn('shell', run.call_args.kwargs)

    def test_workflow_keeps_cache_opt_in_and_all_consumer_gates(self):
        root = Path(__file__).resolve().parents[1]
        path = root / '.github/workflows/development.yml'
        if not path.exists():
            path = root / 'development.yml.proposed'  # Ignored review draft only.
        source = path.read_text()
        self.assertIn('type: boolean\n        default: false', source)
        condition = "if: ${{ github.event_name == 'workflow_dispatch' && inputs.reuse_reviewed_proof_cache }}"
        self.assertEqual(source.count(condition), 2)  # Restore and extra audit only.
        self.assertIn('fetch-depth: 0', source)
        self.assertIn('needs: [build, metadata]', source)
        for step, required in (
            ('Check proof source', 'python3 -O scripts/generate_finite_k3_envelope.py --all --dispatch --manifest --check'),
            ('Build completed proof modules and audit all project axioms',
             'python3 scripts/bounded_project_build.py --check-tracked-coverage --batch-size 2'),
            ('Compile public Challenge and check actual semantic controls', 'python3 scripts/check-release.py --lean-controls'),
            ('Compare all twenty statements and replay both kernels',
             'bash scripts/verify-comparator.sh --verify-only --expected-commit "$GITHUB_SHA"')):
            section = source.split('      - name: ' + step + '\n', 1)[1].split('      - name:', 1)[0]
            self.assertIn(required, section)
            self.assertNotIn('        if:', section)
        self.assertIn('run: lake env lean Test/Axioms.lean', source)
        self.assertIn('name: linux-proof-build-${{ github.sha }}', source)
        self.assertIn('--name "linux-proof-build-$GITHUB_SHA"', source)
        metadata = source.split('  metadata:\n', 1)[1].split('  independent-kernels:\n', 1)[0]
        self.assertIn('python3 scripts/test_metadata_policy.py\n', metadata)
        self.assertIn('python3 -O scripts/test_metadata_policy.py\n', metadata)
        self.assertLess(metadata.index('python3 -O scripts/test_metadata_policy.py'),
                        metadata.index('Validate the pinned official metadata profile'))

    def test_real_git_tree_equality_dirty_consumer_and_wrong_workflow(self):
        def git(*args):
            return subprocess.check_output(['git', '-C', str(self.root), *args], stderr=subprocess.PIPE).decode().strip()
        git('init', '-q'); git('config', 'user.name', 'Cache Test'); git('config', 'user.email', 'cache@example.invalid')
        (self.root / '.github/workflows').mkdir(parents=True)
        workflow = self.root / cache.WORKFLOW; workflow.write_text('reviewed workflow\n')
        (self.root / 'lean-toolchain').write_text(cache.TOOLCHAIN + '\n')
        (self.root / 'DR.lean').write_text('theorem t : True := True.intro\n')
        (self.root / 'formalization.yaml').write_text('old metadata\n')
        git('add', '.'); git('commit', '-qm', 'producer'); old = git('rev-parse', 'HEAD')
        (self.root / 'formalization.yaml').write_text('new metadata\n')
        git('add', '.'); git('commit', '-qm', 'metadata'); new = git('rev-parse', 'HEAD')
        with patch.object(cache, 'PRODUCER', old), patch.object(cache, 'WORKFLOW_SHA256', cache.digest(workflow)):
            self.assertEqual(cache.check_consumer(self.root, new), ['formalization.yaml'])
            (self.root / 'DR.lean').write_text('changed proof\n')
            self.reject(cache.check_consumer, self.root, new)
            git('checkout', '--', 'DR.lean')
            (self.root / 'unexpected').write_text('untracked')
            self.reject(cache.check_consumer, self.root, new)
            (self.root / 'unexpected').unlink()
            with patch.object(cache, 'WORKFLOW_SHA256', '0'*64):
                self.reject(cache.check_consumer, self.root, new)
            self.reject(cache.check_consumer, self.root, 'f'*40)

    def test_real_unchanged_build_helper_plan_has_producer_json_shape(self):
        source = subprocess.check_output(['git', '-C', str(Path(__file__).resolve().parent),
            'show', cache.PRODUCER + ':scripts/bounded_project_build.py'])
        (self.root / 'scripts').mkdir()
        (self.root / 'scripts/bounded_project_build.py').write_bytes(source)
        for name, contents in {
            'DR.lean': 'import DR.Base\n', 'DR/Base.lean': 'def base : Nat := 0\n',
            'Solution.lean': 'import DR\n', 'Test.lean': 'import Test.Axioms\n',
            'Test/Axioms.lean': 'import DR\nimport Solution\n'}.items():
            path = self.root / name; path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(contents)
        subprocess.run(['git', '-C', str(self.root), 'init', '-q'], check=True)
        subprocess.run(['git', '-C', str(self.root), 'add', '.'], check=True)
        plan = cache.current_plan(self.root)
        self.assertEqual(plan, json.loads(json.dumps(plan)))
        self.assertEqual(plan['project_module_count'], 5)
        self.assertEqual(plan['batch_count'], 3)
        self.assertTrue(plan['tracked_coverage_checked'])
        entry = next(m for m in plan['modules'] if m['name'] == 'Test.Axioms')
        self.assertIsInstance(entry['project_imports'], list)
        self.assertEqual(entry['project_imports'], ['DR', 'Solution'])

    def test_end_to_end_offline_restore_is_input_only_then_rejects_failed_producer(self):
        plan, records = plan_and_ledger()
        run, jobs = producer()
        listing = artifacts()
        old = self.root / '.lake/build'; old.mkdir(parents=True)
        (old / 'old-cache-only').write_text('replace after validation')
        archive = tar_bytes()
        receipt = {'commit': cache.PRODUCER, 'toolchain': cache.TOOLCHAIN,
                   'archive_sha256': hashlib.sha256(archive).hexdigest()}
        def download(item, target):
            with zipfile.ZipFile(target, 'w') as z:
                if item['id'] == 1:
                    z.writestr('dr-proof-build.tar.gz', archive)
                    z.writestr('dr-proof-build.json', json.dumps(receipt))
                else:
                    z.writestr('bounded-project-plan.json', json.dumps(plan))
                    z.writestr('bounded-project-build.jsonl', ledger(records))
        calls = []
        def api(path):
            calls.append(path)
            return jobs if '/jobs?' in path else listing if '/artifacts?' in path else run
        with ExitStack() as stack:
            stack.enter_context(patch.object(cache.platform, 'system', return_value='Linux'))
            stack.enter_context(patch.object(cache.platform, 'machine', return_value='x86_64'))
            stack.enter_context(patch.dict(cache.os.environ, {'GITHUB_SHA': 'f'*40, 'GITHUB_REPOSITORY': cache.REPOSITORY}))
            checked = stack.enter_context(patch.object(cache, 'check_consumer', return_value=['formalization.yaml']))
            stack.enter_context(patch.object(cache, 'current_plan', return_value=plan))
            stack.enter_context(patch.object(cache, 'MODULE_COUNT', 4))
            stack.enter_context(patch.object(cache, 'BATCH_COUNT', 2))
            stack.enter_context(patch.object(cache, 'api', side_effect=api))
            stack.enter_context(patch.object(cache, 'download_artifact', side_effect=download))
            with redirect_stdout(io.StringIO()): cache.restore(self.root, 'f'*40)
            output = self.root / '.verification/reviewed-proof-cache.json'
            result = json.loads(output.read_text())
            self.assertEqual(result['status'], 'compiled_input_restored')
            self.assertIs(result['release_verified'], False)
            self.assertEqual(result['consumer_commit'], 'f'*40)
            self.assertEqual(checked.call_count, 3)
            self.assertEqual(calls, ['/actions/runs/34432295599',
                '/actions/runs/34432295599/attempts/1/jobs?per_page=100',
                '/actions/runs/34432295599/artifacts?per_page=100'])
            self.assertTrue((self.root / '.lake/build/lib/lean/Challenge.olean').is_file())
            self.assertFalse((self.root / '.lake/build/old-cache-only').exists())
            jobs['jobs'][0]['conclusion'] = 'failure'
            self.reject(cache.restore, self.root, 'f'*40)
            self.assertFalse(output.exists())
            self.assertTrue((self.root / '.lake/build/lib/lean/Challenge.olean').is_file())


if __name__ == '__main__':
    unittest.main(verbosity=2)
