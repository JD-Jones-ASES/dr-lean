#!/usr/bin/env python3
"""Restore compiled input from one reviewed producer; never certify a release.

The caller must subsequently run every normal source, bounded-build, audit,
semantic and independent-kernel gate at the consumer's exact commit.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import platform
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import zipfile

REPOSITORY = 'JD-Jones-ASES/dr-lean'
PRODUCER = 'da67b34f27d7b590bb4596435d0f77c48c192ccc'
RUN_ID = 34432295599
RUN_ATTEMPT = 1
WORKFLOW = '.github/workflows/development.yml'
WORKFLOW_SHA256 = '6ae27fa4a9295824244508bf91c3cefea18e68ab8b2a89a4236a51f54e2d34e8'
TOOLCHAIN = 'leanprover/lean4:v4.33.0'
MODULE_COUNT = 2736
BATCH_COUNT = 1368
ALLOWLIST = frozenset({
    'formalization.yaml',
    'scripts/check-official-metadata.py',
    'scripts/test_metadata_policy.py',
    'scripts/restore-reviewed-proof-cache.py',
    'scripts/test_reviewed_proof_cache.py',
    WORKFLOW,
    'docs/VERIFICATION.md',
    'docs/history/2026-09-10-metadata-policy.md',
})
BUILD_STEPS = (
    'Check proof source',
    'Fetch pinned mathematical dependencies',
    'Build completed proof modules and audit all project axioms',
    'Compile public Challenge and check actual semantic controls',
    'Archive this exact successful Linux proof build',
    'Preserve the exact Linux build for independent checking',
    'Preserve source and build receipts',
)
MAX_BYTES = 64 * 1024**3
MAX_MEMBERS = 250000


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    with path.open('rb') as source:
        return hashlib.file_digest(source, 'sha256').hexdigest()


def load_json(data):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, 'Duplicate JSON key: ' + key)
            result[key] = value
        return result
    return json.loads(data, object_pairs_hook=unique)


def command(argv, cwd=None):
    return subprocess.check_output(argv, cwd=cwd)


def git(project, *args):
    return command(['git', '-C', str(project), *args])


def git_tree(project, revision):
    result = {}
    for entry in git(project, 'ls-tree', '-rz', '--full-tree', revision).split(b'\0'):
        if not entry:
            continue
        header, name = entry.split(b'\t', 1)
        mode, kind, oid = header.decode('ascii').split()
        path = name.decode('utf-8')
        require(path not in result, 'Duplicate Git tree path')
        result[path] = (mode, kind, oid)
    return result


def compare_trees(producer, consumer):
    changed = sorted(p for p in producer.keys() | consumer.keys()
                     if producer.get(p) != consumer.get(p))
    require(not set(changed) - ALLOWLIST,
            'Changed proof/input paths: ' + ', '.join(set(changed) - ALLOWLIST))
    for path in changed:
        for entry in (producer.get(path), consumer.get(path)):
            if entry is not None:
                require(entry[0] in ('100644', '100755') and entry[1] == 'blob',
                        'Allowed change is not a regular file: ' + path)
    return changed


def check_consumer(project, expected):
    require(re.fullmatch(r'[0-9a-f]{40}', expected) is not None, 'Invalid expected commit')
    require(expected != PRODUCER, 'Consumer must be the new release commit')
    require(git(project, 'rev-parse', 'HEAD').decode().strip() == expected,
            'Consumer HEAD differs from its exact expected commit')
    require(not git(project, 'status', '--porcelain=v1', '--untracked-files=all'),
            'Consumer checkout is dirty or has untracked source')
    git(project, 'merge-base', '--is-ancestor', PRODUCER, expected)
    old = git_tree(project, PRODUCER)
    new = git_tree(project, expected)
    changed = compare_trees(old, new)
    require(hashlib.sha256(git(project, 'show', PRODUCER + ':' + WORKFLOW)).hexdigest()
            == WORKFLOW_SHA256, 'Reviewed producer workflow differs')
    require((project / 'lean-toolchain').read_text().strip() == TOOLCHAIN,
            'Consumer toolchain differs')
    return changed


def api(path):
    return load_json(command(['gh', 'api', 'repos/' + REPOSITORY + path]))


def validate_producer(run, jobs):
    require(run.get('id') == RUN_ID and run.get('head_sha') == PRODUCER
            and run.get('run_attempt') == RUN_ATTEMPT, 'Wrong producer run/SHA/attempt')
    require(run.get('path') == WORKFLOW and run.get('event') == 'push',
            'Wrong producer workflow/event')
    for field in ('repository', 'head_repository'):
        require(run.get(field, {}).get('full_name') == REPOSITORY,
                'Wrong producer repository')
    entries = jobs.get('jobs', [])
    require(jobs.get('total_count') == len(entries), 'Truncated job list')
    matching = [j for j in entries if j.get('name') == 'build']
    require(len(matching) == 1, 'Missing or duplicate producer build job')
    job = matching[0]
    require(job.get('run_id') == RUN_ID and job.get('head_sha') == PRODUCER
            and job.get('run_attempt') == RUN_ATTEMPT, 'Wrong producer job identity')
    require(job.get('status') == 'completed' and job.get('conclusion') == 'success',
            'Producer build has not completed successfully')
    for name in BUILD_STEPS:
        steps = [s for s in job.get('steps', []) if s.get('name') == name]
        require(len(steps) == 1 and steps[0].get('status') == 'completed'
                and steps[0].get('conclusion') == 'success',
                'Producer step did not succeed: ' + name)
    # Overall metadata/kernel status is deliberately not inherited as evidence.
    return job['id']


def select_artifacts(document):
    entries = document.get('artifacts', [])
    require(document.get('total_count') == len(entries), 'Truncated artifact list')
    result = {}
    for kind in ('linux-proof-build', 'proof-receipts'):
        name = kind + '-' + PRODUCER
        matches = [a for a in entries if a.get('name') == name]
        require(len(matches) == 1, 'Missing or duplicate complete artifact: ' + name)
        item = matches[0]
        require(item.get('expired') is False and type(item.get('id')) is int
                and item['id'] > 0, 'Expired or invalid artifact')
        origin = item.get('workflow_run', {})
        require(origin.get('id') == RUN_ID and origin.get('head_sha') == PRODUCER,
                'Artifact belongs to another producer')
        result[kind] = item
    return result


def safe_name(name):
    require(name and '\\' not in name and not any(ord(c) < 32 for c in name),
            'Unsafe archive name')
    path = PurePosixPath(name)
    require(not path.is_absolute() and all(p not in ('', '.', '..') for p in name.rstrip('/').split('/')),
            'Unsafe archive path: ' + name)
    return path


def download_artifact(item, target):
    with target.open('xb') as output:
        subprocess.run(['gh', 'api', 'repos/' + REPOSITORY + '/actions/artifacts/'
                        + str(item['id']) + '/zip'], stdout=output, check=True)
    if item.get('digest') is not None:
        require(item['digest'] == 'sha256:' + digest(target), 'Artifact ZIP digest mismatch')


def read_zip_files(archive, wanted, destination):
    found = {}
    with zipfile.ZipFile(archive) as source:
        infos = source.infolist()
        require(len(infos) <= MAX_MEMBERS, 'Too many ZIP entries')
        names = set()
        for info in infos:
            safe_name(info.filename)
            require(info.filename not in names, 'Duplicate ZIP entry')
            names.add(info.filename)
            require(not ((info.external_attr >> 16) & 0o170000) == 0o120000,
                    'ZIP symlink rejected')
            if info.filename in wanted:
                require(not info.is_dir() and 0 <= info.file_size <= MAX_BYTES,
                        'Invalid requested ZIP member')
                target = destination / info.filename
                with source.open(info) as data, target.open('xb') as output:
                    shutil.copyfileobj(data, output, length=1024*1024)
                require(target.stat().st_size == info.file_size, 'Truncated ZIP member')
                found[info.filename] = target
    require(set(found) == set(wanted), 'Complete artifact files are missing')
    return found


def current_plan(project):
    path = project / 'scripts/bounded_project_build.py'
    spec = importlib.util.spec_from_file_location('_reviewed_bounded_build', path)
    require(spec is not None and spec.loader is not None, 'Cannot load fixed build helper')
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    plan = module.make_plan(project, 2)
    module.check_tracked_coverage(plan)
    require(not plan.excluded, 'Excluded local project modules')
    # The retained producer JSON has arrays, whereas the helper uses tuples
    # internally for imports. Compare the same serialized representation.
    return load_json(json.dumps(plan.report()))


def validate_ledger(plan, expected, ledger):
    require(plan == expected, 'Producer full plan differs from exact consumer sources')
    require(plan['project_module_count'] == MODULE_COUNT
            and plan['batch_count'] == BATCH_COUNT
            and plan['tracked_coverage_checked'] is True, 'Wrong complete proof scope')
    batches = plan['batches']
    require(len(batches) == BATCH_COUNT, 'Incomplete batch plan')
    flat = [n for batch in batches for n in batch]
    require(len(flat) == len(set(flat)) == MODULE_COUNT, 'Duplicate or missing module')
    require(flat == [m['name'] for m in plan['modules']], 'Wrong plan order')
    require(set(flat) == set(plan['tracked_project_modules']), 'Incomplete tracked coverage')
    records = [load_json(line) for line in ledger.splitlines() if line.strip()]
    phases = [(b, 'module_batch') for b in batches] + [(['DR', 'Test'], 'root_check')]
    require(len(records) == len(phases), 'Incomplete or extra build ledger')
    audit = False
    for record, (batch, phase) in zip(records, phases):
        require(1 <= len(batch) <= 2, 'Unbounded build batch')
        require(record.get('status') == 'passed' and record.get('exit_code') == 0
                and record.get('modules') == batch and record.get('phase') == phase
                and record.get('argv') == ['lake', '--wfail', 'build', *('+' + n for n in batch)],
                'Failed, reordered, incomplete or altered build batch')
        require(isinstance(record.get('output'), str), 'Missing compiler output')
        if 'Test.Axioms' in batch:
            audit = re.search(r'Audited [1-9][0-9]* project declarations\.', record['output']) is not None
    require(audit, 'Missing nonempty global project axiom audit')


def check_receipt(receipt, archive):
    require(set(receipt) == {'commit', 'archive_sha256', 'toolchain'}, 'Unexpected build receipt')
    require(receipt['commit'] == PRODUCER and receipt['toolchain'] == TOOLCHAIN,
            'Wrong archive commit/toolchain')
    require(receipt['archive_sha256'] == digest(archive), 'Build archive digest mismatch')


def unpack_build(archive, destination, modules):
    """Materialize only regular build files/dirs into a fresh private stage."""
    with tarfile.open(archive, 'r:gz') as source:
        members = source.getmembers()
        require(len(members) <= MAX_MEMBERS, 'Too many TAR members')
        names = set()
        total = 0
        for member in members:
            path = safe_name(member.name)
            require(path.parts[:2] == ('.lake', 'build'), 'Archive escapes .lake/build')
            name = path.as_posix()
            require(name not in names, 'Duplicate TAR member')
            names.add(name)
            require((member.isdir() or member.isreg()) and not member.issparse(),
                    'TAR links, devices, special or sparse files rejected')
            require(member.size >= 0, 'Negative TAR size')
            total += member.size
            require(total <= MAX_BYTES, 'Build archive exceeds extraction limit')
        files = {PurePosixPath(m.name).as_posix() for m in members if m.isreg()}
        for name in [*modules, 'Challenge']:
            stem = '.lake/build/lib/lean/' + name.replace('.', '/')
            require(stem + '.olean' in files and stem + '.trace' in files,
                    'Incomplete compiled cache: ' + name)
        for member in members:
            path = destination.joinpath(*PurePosixPath(member.name).parts)
            if member.isdir():
                path.mkdir(parents=True, exist_ok=True)
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                data = source.extractfile(member)
                require(data is not None, 'Unreadable TAR member')
                with data, path.open('xb') as output:
                    shutil.copyfileobj(data, output, length=1024*1024)
                require(path.stat().st_size == member.size, 'Truncated TAR member')
                path.chmod(0o755 if member.mode & 0o111 else 0o644)
    return total


def receipt_path(project):
    parent = project / '.verification'
    require(not parent.is_symlink(), 'Unsafe receipt directory')
    parent.mkdir(exist_ok=True)
    path = parent / 'reviewed-proof-cache.json'
    require(not path.is_symlink(), 'Unsafe receipt file')
    path.unlink(missing_ok=True)
    return path


def restore(project, expected):
    output = receipt_path(project)  # A failed new request must not leave old success.
    require(platform.system() == 'Linux' and platform.machine() == 'x86_64',
            'Reviewed cache is for Linux x86_64 only')
    changed = check_consumer(project, expected)
    require(os.environ.get('GITHUB_REPOSITORY') == REPOSITORY
            and os.environ.get('GITHUB_SHA') == expected, 'Wrong consumer workflow identity')
    plan = current_plan(project)
    run = api('/actions/runs/' + str(RUN_ID))
    job = validate_producer(run, api('/actions/runs/' + str(RUN_ID)
                                   + '/attempts/1/jobs?per_page=100'))
    artifacts = select_artifacts(api('/actions/runs/' + str(RUN_ID) + '/artifacts?per_page=100'))
    lake = project / '.lake'
    require(not lake.is_symlink(), 'Symlinked .lake directory')
    lake.mkdir(exist_ok=True)
    target = lake / 'build'
    require(not target.is_symlink() and (not target.exists() or target.is_dir()),
            'Unsafe existing build destination')
    with tempfile.TemporaryDirectory(prefix='reviewed-proof-download-') as directory, \
            tempfile.TemporaryDirectory(prefix='.reviewed-stage-', dir=lake) as staged:
        temp = Path(directory)
        for kind, item in artifacts.items():
            download_artifact(item, temp / (kind + '.zip'))
        proof = read_zip_files(temp / 'linux-proof-build.zip',
                               {'dr-proof-build.tar.gz', 'dr-proof-build.json'}, temp)
        logs = read_zip_files(temp / 'proof-receipts.zip',
                              {'bounded-project-plan.json', 'bounded-project-build.jsonl'}, temp)
        validate_ledger(load_json(logs['bounded-project-plan.json'].read_bytes()), plan,
                        logs['bounded-project-build.jsonl'].read_text())
        archive = proof['dr-proof-build.tar.gz']
        check_receipt(load_json(proof['dr-proof-build.json'].read_bytes()), archive)
        unpacked = unpack_build(archive, Path(staged), [m['name'] for m in plan['modules']])
        require(changed == check_consumer(project, expected), 'Consumer changed during restoration')
        check_receipt(load_json(proof['dr-proof-build.json'].read_bytes()), archive)
        # The old build directory is local cache only; preserve it until all checks pass.
        backup = Path(staged) / 'previous-build'
        if target.exists():
            target.rename(backup)
        try:
            (Path(staged) / '.lake/build').rename(target)
        except BaseException:
            if backup.exists():
                backup.rename(target)
            raise
        receipt = {'status': 'compiled_input_restored', 'release_verified': False,
                   'consumer_commit': expected, 'producer_commit': PRODUCER,
                   'producer_run': RUN_ID, 'producer_attempt': RUN_ATTEMPT,
                   'producer_build_job': job, 'toolchain': TOOLCHAIN,
                   'artifact_ids': {k:v['id'] for k,v in artifacts.items()},
                   'archive_sha256': digest(archive), 'extracted_bytes': unpacked,
                   'plan_sha256': hashlib.sha256(json.dumps(plan, sort_keys=True).encode()).hexdigest(),
                   'allowed_changed_paths': changed,
                   'required_next': 'all normal source/build/audit/semantic gates and fresh all20 kernels'}
        require(changed == check_consumer(project, expected), 'Consumer changed after restoration')
        with tempfile.NamedTemporaryFile(mode='w', dir=output.parent,
                prefix='.reviewed-cache-receipt-', delete=False) as data:
            temporary = Path(data.name)
            data.write(json.dumps(receipt, indent=2) + '\n')
        try:
            temporary.replace(output)
        finally:
            temporary.unlink(missing_ok=True)
    print('Reviewed compiled input restored. No build, audit, kernel or release pass is granted.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--expected-commit', required=True)
    args = parser.parse_args()
    restore(args.project.resolve(), args.expected_commit)


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, tarfile.TarError, zipfile.BadZipFile,
            subprocess.CalledProcessError) as error:
        print('Reviewed cache restore rejected: ' + str(error), file=sys.stderr)
        raise SystemExit(1)
