#!/usr/bin/env python3
"""Offline prefix-artifact controls; fixture oleans are never claimed as proofs."""
from __future__ import annotations

from contextlib import ExitStack, redirect_stdout
import copy
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch
import zipfile

SCRIPT = Path(__file__).with_name('stage_build_artifact.py')
BUILDER = Path(__file__).with_name('bounded_project_build.py')
SPEC = importlib.util.spec_from_file_location('prefix_artifact_tests', SCRIPT)
a = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = a
SPEC.loader.exec_module(a)


class PrefixArtifactTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='dr-prefix-artifact-tests-')
        self.base = Path(self.temp.name)
        self.project = self.base / 'project'; self.project.mkdir()
        for name, content in {
            '.gitignore': '.lake/\n.verification/\n__pycache__/\n',
            '.github/workflows/development.yml': 'name: offline fixture only\n',
            'lean-toolchain': 'leanprover/lean4:v4.33.0\n',
            'lake-manifest.json': '{"packages":[]}\n',
            'lakefile.toml': 'name = "tiny_fixture"\n',
            'DR/Base.lean': 'def fixtureBase : Nat := 1\n',
            'DR.lean': 'import DR.Base\n',
            'Test.lean': 'import DR\n',
        }.items():
            p = self.project / name; p.parent.mkdir(parents=True, exist_ok=True); p.write_text(content)
        (self.project / 'scripts').mkdir()
        shutil.copyfile(SCRIPT, self.project / 'scripts/stage_build_artifact.py')
        shutil.copyfile(BUILDER, self.project / 'scripts/bounded_project_build.py')
        self.git('init', '-q'); self.git('config', 'user.name', 'Offline Artifact Test')
        self.git('config', 'user.email', 'artifact@example.invalid')
        self.git('add', '.'); self.git('commit', '-qm', 'Synthetic source fixture; no proof replay')
        self.commit = self.git('rev-parse', 'HEAD').decode().strip()
        self.env = patch.dict(os.environ, {'GITHUB_REPOSITORY': a.REPOSITORY,
            'GITHUB_SHA': self.commit, 'GITHUB_RUN_ID': '1234', 'GITHUB_RUN_ATTEMPT': '2'})
        self.env.start()
        self.builder, self.context = a.current_context(self.project, 1)
        self.modules = a.prefix_modules(self.context)
        for name in self.modules:
            for suffix in ('.olean', '.trace'):
                p = self.project / ('.lake/build/lib/lean/' + name.replace('.', '/') + suffix)
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_bytes(('uncompiled offline cache fixture ' + name + suffix).encode())
        record = {'status': 'passed', 'phase': 'module_batch', 'modules': self.modules,
                  'argv': ['lake', '--wfail', 'build', *('+' + n for n in self.modules)],
                  'seconds': 0, 'exit_code': 0, 'output': 'Offline mocked compiler result', 'batch_index': 0}
        self.ledger = json.dumps(record) + '\n'
        self.receipt = {'schema': 1, 'status': 'partial_stage_passed', 'stage': 'prefix',
            'interval': [0, 1], 'covered_batches': 1, 'context': self.context,
            'context_sha256': a.value_digest(self.context),
            'ledger_sha256': hashlib.sha256(self.ledger.encode()).hexdigest(),
            'previous_receipt_sha256': None, 'root_check': False,
            'build_complete': False, 'release_verified': False}
        self.evidence = self.project / '.verification/prefix'; self.evidence.mkdir(parents=True)
        a.write_json(self.evidence / 'stage.json', self.receipt)
        (self.evidence / 'build.jsonl').write_text(self.ledger)
        a.write_json(self.evidence / 'plan.json', self.context['plan'])
        self.bundle = self.base / 'bundle'

    def tearDown(self):
        self.env.stop(); self.temp.cleanup()

    def git(self, *args):
        return subprocess.check_output(['git', '-C', str(self.project), *args], stderr=subprocess.PIPE)

    def reject(self, fn, *args, **kwargs):
        with self.assertRaises((ValueError, OSError, tarfile.TarError, zipfile.BadZipFile,
                                subprocess.CalledProcessError)):
            fn(*args, **kwargs)

    def pack(self):
        with redirect_stdout(io.StringIO()):
            a.pack(self.project, self.evidence / 'stage.json', self.evidence / 'build.jsonl',
                   self.evidence / 'plan.json', self.bundle, 1)

    def producer(self, event='push'):
        head = self.commit if event != 'pull_request' else 'f' * 40
        run = {'id': 1234, 'run_attempt': 2, 'path': self.context['workflow'], 'event': event,
               'head_sha': head, 'repository': {'full_name': a.REPOSITORY},
               'head_repository': {'full_name': a.REPOSITORY}, 'status': 'in_progress'}
        job = {'id': 17, 'name': 'build-prefix', 'run_id': 1234, 'run_attempt': 2,
               'head_sha': head, 'status': 'completed', 'conclusion': 'success',
               'steps': [{'name': name, 'status': 'completed', 'conclusion': 'success'}
                         for name in a.PREFIX_STEPS]}
        artifact = {'id': 29, 'name': a.artifact_name(self.context), 'expired': False,
                    'workflow_run': {'id': 1234, 'head_sha': head}}
        return run, {'total_count': 1, 'jobs': [job]}, {'total_count': 1, 'artifacts': [artifact]}

    def restore(self, event='push'):
        run, jobs, listing = self.producer(event)
        def api(path):
            if '/jobs?' in path: return jobs
            if '/artifacts?' in path: return listing
            return run
        def download(item, destination):
            self.assertEqual(item['id'], 29)
            with zipfile.ZipFile(destination, 'w') as archive:
                for p in self.bundle.iterdir(): archive.write(p, p.name)
        output = self.project / '.verification/restored-prefix'
        with patch.object(a, 'api', side_effect=api) as calls, \
                patch.object(a, 'download_artifact', side_effect=download), redirect_stdout(io.StringIO()):
            a.restore(self.project, 1, output)
        self.assertEqual([c.args[0] for c in calls.call_args_list], [
            '/actions/runs/1234', '/actions/runs/1234/attempts/2/jobs?per_page=100',
            '/actions/runs/1234/artifacts?per_page=100'])
        return output

    def test_real_git_context_and_complete_plan(self):
        self.assertEqual(self.context['commit'], self.commit)
        self.assertEqual(self.context['run_id'], 1234)
        self.assertEqual(self.context['run_attempt'], 2)
        self.assertEqual(self.context['plan']['project_module_count'], 3)
        self.assertEqual(self.context['plan']['batch_count'], 2)
        self.assertEqual(self.modules, ['DR.Base', 'DR'])
        self.assertEqual(a.value_digest(self.context), self.builder.sha256_bytes(self.builder.canonical_bytes(self.context)))

    def test_dirty_source_wrong_commit_and_run_reject(self):
        p = self.project / 'DR.lean'; original = p.read_bytes(); p.write_bytes(original + b'\n')
        self.reject(a.current_context, self.project, 1); p.write_bytes(original)
        for key, value in [('GITHUB_SHA', '0'*40), ('GITHUB_RUN_ID', '0'), ('GITHUB_RUN_ATTEMPT', 'x')]:
            with patch.dict(os.environ, {key: value}): self.reject(a.current_context, self.project, 1)

    def test_zero_full_and_boolean_cuts_reject(self):
        for cut in (0, 2, True): self.reject(a.current_context, self.project, cut)

    def test_pack_genuine_protocol_and_required_files(self):
        self.pack()
        self.assertEqual({p.name for p in self.bundle.iterdir()}, a.BUNDLE_FILES | {'artifact.json'})
        manifest, receipt, ledger = a.check_bundle(self.builder, self.bundle, self.context)
        self.assertEqual(receipt, self.receipt); self.assertEqual(ledger, self.ledger)
        self.assertFalse(manifest['build_complete']); self.assertFalse(manifest['release_verified'])
        self.assertNotIn('.lake/build/lib/lean/Challenge.olean', manifest['cache_files'])

    def test_pack_fails_on_missing_trace(self):
        (self.project / '.lake/build/lib/lean/DR.trace').unlink()
        self.reject(self.pack); self.assertFalse(self.bundle.exists())

    def test_pack_does_not_overwrite_output(self):
        self.bundle.mkdir(); (self.bundle / 'preserve').write_text('original')
        self.reject(self.pack); self.assertEqual((self.bundle / 'preserve').read_text(), 'original')

    def test_pack_cannot_archive_itself_inside_cache(self):
        self.bundle = self.project / '.lake/build/bundle'
        self.reject(self.pack); self.assertFalse(self.bundle.exists())

    def test_failed_or_complete_prefix_receipt_reject(self):
        for key, value in [('build_complete', True), ('release_verified', True), ('root_check', True),
                           ('interval', [0, 2]), ('context_sha256', '0'*64)]:
            changed = {**self.receipt, key: value}; a.write_json(self.evidence / 'stage.json', changed)
            self.reject(self.pack)

    def test_ledger_missing_changed_or_extra_root_reject(self):
        for value in ('', self.ledger.replace('"exit_code": 0', '"exit_code": 1'), self.ledger + self.ledger):
            (self.evidence / 'build.jsonl').write_text(value); self.reject(self.pack)

    def test_bundle_metadata_or_archive_mutation_reject(self):
        self.pack()
        for name in a.BUNDLE_FILES:
            p = self.bundle / name; data = p.read_bytes(); p.write_bytes(data + b'\n')
            self.reject(a.check_bundle, self.builder, self.bundle, self.context); p.write_bytes(data)

    def test_artifact_manifest_wrong_inventory_or_completion_reject(self):
        self.pack(); p = self.bundle / 'artifact.json'; original = a.load_json(p.read_bytes())
        for key, value in [('release_verified', True), ('build_complete', True), ('status', 'complete_build'),
                           ('files', {**original['files'], 'extra': '0'*64})]:
            a.write_json(p, {**original, key: value})
            self.reject(a.check_bundle, self.builder, self.bundle, self.context)

    def test_rehashed_wrong_context_plan_and_ledger_still_reject(self):
        self.pack(); path = self.bundle / 'artifact.json'; original = path.read_bytes()
        changed = copy.deepcopy(self.context); changed['run_attempt'] = 3
        self.reject(a.check_bundle, self.builder, self.bundle, changed)
        plan = self.bundle / 'plan.json'; before = plan.read_bytes(); plan.write_text('{}')
        manifest = a.load_json(original); manifest['files']['plan.json'] = a.digest(plan); a.write_json(path, manifest)
        self.reject(a.check_bundle, self.builder, self.bundle, self.context)
        plan.write_bytes(before); path.write_bytes(original)
        ledger = self.bundle / 'build.jsonl'; ledger.write_text('')
        manifest = a.load_json(original); manifest['files']['build.jsonl'] = a.digest(ledger); a.write_json(path, manifest)
        self.reject(a.check_bundle, self.builder, self.bundle, self.context)

    def test_json_duplicate_keys_reject(self):
        self.reject(a.load_json, '{"status":"failed","status":"passed"}')

    def test_cache_symlink_and_other_tree_reject(self):
        (self.project / '.lake/build/link').symlink_to(self.project / 'DR.lean')
        self.reject(a.cache_manifest, self.project, self.modules)
        self.reject(a.check_cache_names, {'DR.lean': '0'*64}, self.modules)

    def tar(self, extras=(), omit=None):
        data = io.BytesIO()
        files = a.cache_manifest(self.project, self.modules)
        entries = [(n, tarfile.REGTYPE, (self.project / n).read_bytes()) for n in files if n != omit]
        with tarfile.open(fileobj=data, mode='w:gz') as target:
            for name, kind, contents in entries + list(extras):
                info = tarfile.TarInfo(name); info.type = kind
                info.size = len(contents) if kind == tarfile.REGTYPE else 0
                if kind in (tarfile.SYMTYPE, tarfile.LNKTYPE): info.linkname = '/tmp/outside'
                target.addfile(info, io.BytesIO(contents) if info.size else None)
        p = self.base / 'test.tar.gz'; p.write_bytes(data.getvalue()); return p, files

    def unpack(self, extras=(), omit=None):
        p, files = self.tar(extras, omit)
        dest = self.base / 'extract'; dest.mkdir(exist_ok=True)
        return a.unpack_cache(p, dest, self.modules, files)

    def test_archive_regular_file_roundtrip(self):
        self.assertGreater(self.unpack(), 0)
        self.assertEqual(a.cache_manifest(self.base/'extract', self.modules), a.cache_manifest(self.project, self.modules))

    def test_archive_traversal_absolute_other_tree_backslash_reject(self):
        for name in ('../escape', '/tmp/escape', '.lake/build/../../DR.lean',
                     '.lake/packages/dependency/file', '.lake/build\\bad'):
            self.reject(self.unpack, [(name, tarfile.REGTYPE, b'x')])
        self.assertFalse((self.base/'extract/.lake').exists())

    def test_archive_links_devices_special_files_reject_before_extract(self):
        for kind in (tarfile.SYMTYPE, tarfile.LNKTYPE, tarfile.CHRTYPE, tarfile.BLKTYPE, tarfile.FIFOTYPE):
            self.reject(self.unpack, [('.lake/build/bad', kind, b'')])
        self.assertFalse((self.base/'extract/.lake').exists())

    def test_archive_duplicate_missing_and_changed_content_reject(self):
        name = '.lake/build/lib/lean/DR.olean'
        self.reject(self.unpack, [(name, tarfile.REGTYPE, b'other')])
        self.reject(self.unpack, omit=name)
        p, files = self.tar(); files[name] = '0'*64
        dest = self.base/'extract'; dest.mkdir(exist_ok=True)
        self.reject(a.unpack_cache, p, dest, self.modules, files)

    def test_archive_size_limits_reject(self):
        p, files = self.tar()
        with patch.object(a, 'MAX_BYTES', 1): self.reject(a.unpack_cache, p, self.base/'extract', self.modules, files)
        with patch.object(a, 'MAX_MEMBERS', 1): self.reject(a.unpack_cache, p, self.base/'extract', self.modules, files)

    def test_zip_exact_inventory_no_traversal_symlink_duplicates(self):
        for kind in ('missing', 'traversal', 'symlink', 'duplicate'):
            p = self.base/(kind+'.zip'); dest=self.base/kind; dest.mkdir()
            with zipfile.ZipFile(p, 'w') as archive:
                if kind == 'traversal': archive.writestr('../escape', b'x')
                elif kind == 'symlink':
                    info=zipfile.ZipInfo('artifact.json'); info.external_attr=0o120777 << 16
                    archive.writestr(info,b'/tmp/outside')
                elif kind == 'duplicate':
                    archive.writestr('artifact.json',b'a')
                    with self.assertWarns(UserWarning): archive.writestr('artifact.json',b'b')
                else: archive.writestr('artifact.json',b'{}')
            self.reject(a.unpack_zip,p,dest)

    def test_zip_size_limit_rejects(self):
        self.pack(); p=self.base/'size.zip'; dest=self.base/'size-extract';dest.mkdir()
        with zipfile.ZipFile(p,'w') as archive:
            for file in self.bundle.iterdir(): archive.write(file,file.name)
        with patch.object(a,'MAX_BYTES',1): self.reject(a.unpack_zip,p,dest)

    def test_corrupt_zip_tar_reject(self):
        p=self.base/'corrupt';p.write_bytes(b'not an archive')
        self.reject(a.unpack_zip,p,self.base)
        self.reject(a.unpack_cache,p,self.base,self.modules,a.cache_manifest(self.project,self.modules))

    def test_successful_same_run_prefix_and_pr_merge_commit(self):
        for event in ('push','workflow_dispatch','pull_request'):
            run,jobs,listing=self.producer(event)
            artifact,job=a.validate_producer(run,jobs,listing,self.context)
            self.assertEqual((artifact['id'],job),(29,17))

    def test_wrong_run_attempt_workflow_repo_and_commit_reject(self):
        run,jobs,listing=self.producer()
        for key,value in [('id',8),('run_attempt',1),('path','other.yml'),('head_sha','0'*40),
                          ('repository',{'full_name':'other/repo'}),('event','schedule')]:
            self.reject(a.validate_producer,{**run,key:value},jobs,listing,self.context)

    def test_pending_failed_skipped_prefix_jobs_reject(self):
        run,jobs,listing=self.producer()
        for status,conclusion in [('in_progress',None),('completed','failure'),('completed','cancelled'),('completed','timed_out')]:
            changed=copy.deepcopy(jobs);changed['jobs'][0].update(status=status,conclusion=conclusion)
            self.reject(a.validate_producer,run,changed,listing,self.context)
        for index in range(len(a.PREFIX_STEPS)):
            changed=copy.deepcopy(jobs);changed['jobs'][0]['steps'][index]['conclusion']='skipped'
            self.reject(a.validate_producer,run,changed,listing,self.context)

    def test_wrong_duplicate_or_truncated_prefix_jobs_reject(self):
        run,jobs,listing=self.producer()
        for field,value in [('run_attempt',1),('run_id',0),('head_sha','0'*40)]:
            changed=copy.deepcopy(jobs);changed['jobs'][0][field]=value
            self.reject(a.validate_producer,run,changed,listing,self.context)
        self.reject(a.validate_producer,run,{'total_count':2,'jobs':jobs['jobs']},listing,self.context)
        self.reject(a.validate_producer,run,{'total_count':2,'jobs':jobs['jobs']*2},listing,self.context)

    def test_wrong_expired_duplicate_truncated_artifacts_reject(self):
        run,jobs,listing=self.producer()
        for field,value in [('name','linux-proof-build-'+self.commit),('expired',True),('id',False),
                            ('workflow_run',{'id':9,'head_sha':self.commit})]:
            changed=copy.deepcopy(listing);changed['artifacts'][0][field]=value
            self.reject(a.validate_producer,run,jobs,changed,self.context)
        self.reject(a.validate_producer,run,jobs,{'total_count':2,'artifacts':listing['artifacts']},self.context)
        self.reject(a.validate_producer,run,jobs,{'total_count':2,'artifacts':listing['artifacts']*2},self.context)

    def test_exact_artifact_id_download_and_optional_digest(self):
        def run(argv,**kwargs):
            self.assertEqual(argv,['gh','api','repos/'+a.REPOSITORY+'/actions/artifacts/29/zip'])
            self.assertTrue(kwargs['check']);self.assertNotIn('shell',kwargs)
            kwargs['stdout'].write(b'zip fixture')
        with patch.object(a.subprocess,'run',side_effect=run):
            a.download_artifact({'id':29,'digest':'sha256:'+hashlib.sha256(b'zip fixture').hexdigest()},self.base/'ok.zip')
            self.reject(a.download_artifact,{'id':29,'digest':'sha256:'+'0'*64},self.base/'bad.zip')

    def test_full_mock_restore_and_final_validation(self):
        self.pack();output=self.restore()
        result=a.validate_restored(self.project,self.receipt,self.ledger,self.context,output)
        self.assertFalse(result['release_verified']);self.assertFalse(result['build_complete'])
        self.assertEqual(result['status'],'partial_prefix_restored')
        self.assertEqual({p.name for p in output.iterdir()}, {'stage.json','build.jsonl','plan.json','artifact.json','restored.json'})
        self.assertFalse((output/'build.tar.gz').exists())

    def test_restored_cache_or_evidence_mutation_rejects_before_suffix(self):
        self.pack();output=self.restore()
        p=self.project/'.lake/build/lib/lean/DR.olean';original=p.read_bytes();p.write_bytes(b'changed')
        self.reject(a.validate_restored,self.project,self.receipt,self.ledger,self.context,output);p.write_bytes(original)
        q=output/'build.jsonl';q.write_text(self.ledger+'\n')
        self.reject(a.validate_restored,self.project,self.receipt,self.ledger,self.context,output)

    def test_restored_context_completion_and_producer_mutations_reject(self):
        self.pack();output=self.restore();p=output/'restored.json';original=a.load_json(p.read_bytes())
        for key,value in [('build_complete',True),('release_verified',True),('context_sha256','0'*64),
                          ('producer',{**original['producer'],'run_attempt':1})]:
            a.write_json(p,{**original,key:value})
            self.reject(a.validate_restored,self.project,self.receipt,self.ledger,self.context,output)

    def test_failed_restoration_preserves_previous_cache_and_no_receipt(self):
        self.pack();sentinel=self.project/'.lake/build/old-cache';sentinel.write_text('preserve')
        p=self.bundle/'build.tar.gz';p.write_bytes(p.read_bytes()+b'corrupt')
        self.reject(self.restore)
        self.assertEqual(sentinel.read_text(),'preserve')
        self.assertFalse((self.project/'.verification/restored-prefix').exists())

    def test_existing_restore_output_rejects_without_api(self):
        output=self.project/'.verification/restored-prefix';output.mkdir();(output/'preserve').write_text('kept')
        with patch.object(a,'api',side_effect=AssertionError('Must reject before API')):
            self.reject(a.restore,self.project,1,output)
        self.assertEqual((output/'preserve').read_text(),'kept')

    def test_restore_outside_verification_and_symlink_reject_before_api(self):
        with patch.object(a,'api',side_effect=AssertionError('Must reject before API')):
            self.reject(a.restore,self.project,1,self.base/'outside')
            output=self.project/'.verification/unsafe';output.symlink_to(self.base/'outside')
            self.reject(a.restore,self.project,1,output)

    def test_metadata_preparation_failure_preserves_old_cache(self):
        self.pack();sentinel=self.project/'.lake/build/old-cache';sentinel.write_text('preserve')
        with patch.object(a.shutil,'copyfile',side_effect=OSError('Simulated metadata copy failure')):
            self.reject(self.restore)
        self.assertEqual(sentinel.read_text(),'preserve')
        self.assertFalse((self.project/'.verification/restored-prefix').exists())

    def test_postreplacement_failure_rolls_back_cache(self):
        self.pack();sentinel=self.project/'.lake/build/old-cache';sentinel.write_text('preserve')
        with patch.object(a,'validate_restored',side_effect=ValueError('Simulated final consistency failure')):
            self.reject(self.restore)
        self.assertEqual(sentinel.read_text(),'preserve')
        self.assertFalse((self.project/'.verification/restored-prefix').exists())


if __name__ == '__main__':
    unittest.main(verbosity=2)
