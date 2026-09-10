#!/usr/bin/env python3
"""Pack or restore one exact same-run compiled prefix; never certify a build.

The final bounded builder must validate the restored prefix, run every suffix
batch and both roots, and then run all public/independent verification gates.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys
import tarfile
import tempfile
import zipfile

REPOSITORY = 'JD-Jones-ASES/dr-lean'
MAX_BYTES = 64 * 1024**3
MAX_MEMBERS = 250000
BUNDLE_FILES = frozenset({'build.tar.gz', 'stage.json', 'build.jsonl', 'plan.json'})
PREFIX_STEPS = ('Check proof source', 'Build the dependency prefix',
                'Pack the exact successful prefix', 'Preserve the exact prefix for this attempt')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    with path.open('rb') as source:
        return hashlib.file_digest(source, 'sha256').hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True).encode()


def value_digest(value):
    return hashlib.sha256(canonical(value)).hexdigest()


def load_json(data):
    def unique(pairs):
        result = {}
        for name, value in pairs:
            require(name not in result, 'Duplicate JSON key: ' + name)
            result[name] = value
        return result
    return json.loads(data, object_pairs_hook=unique)


def write_json(path, value):
    require(not path.is_symlink(), 'Unsafe JSON destination')
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def load_build(project):
    path = project / 'scripts/bounded_project_build.py'
    spec = importlib.util.spec_from_file_location('_artifact_bounded_build', path)
    require(spec is not None and spec.loader is not None, 'Cannot load bounded builder')
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def current_context(project, cut):
    builder = load_build(project)
    plan = builder.make_plan(project, 2)
    builder.check_tracked_coverage(plan)
    require(not plan.excluded, 'Local modules are excluded from the complete plan')
    return builder, builder.stage_context(plan, cut)


def prefix_modules(context):
    plan, cut = context['plan'], context['cut']
    require(type(cut) is int and 0 < cut < len(plan['batches']), 'Invalid proper prefix cut')
    names = [name for batch in plan['batches'][:cut] for name in batch]
    require(names and len(names) == len(set(names)), 'Duplicate or empty prefix modules')
    return names


def safe_name(name):
    require(isinstance(name, str) and name and '\\' not in name
            and not any(ord(c) < 32 for c in name), 'Unsafe archive name')
    path = PurePosixPath(name)
    require(not path.is_absolute()
            and all(p not in ('', '.', '..') for p in name.rstrip('/').split('/')),
            'Unsafe archive path: ' + name)
    return path


def check_cache_names(files, modules):
    require(isinstance(files, dict) and files, 'Empty cache-file manifest')
    for name, expected in files.items():
        require(safe_name(name).parts[:2] == ('.lake', 'build'), 'Cache path escapes build directory')
        require(isinstance(expected, str) and len(expected) == 64
                and all(c in '0123456789abcdef' for c in expected), 'Invalid cache-file digest')
    for name in modules:
        stem = '.lake/build/lib/lean/' + name.replace('.', '/')
        require(stem + '.olean' in files and stem + '.trace' in files,
                'Missing required prefix olean/trace: ' + name)


def cache_manifest(project, modules):
    root = project / '.lake/build'
    require(not (project / '.lake').is_symlink() and root.is_dir() and not root.is_symlink(),
            'Unsafe or missing build directory')
    files = {}
    total = 0
    for path in sorted(root.rglob('*')):
        require(not path.is_symlink() and (path.is_dir() or path.is_file()),
                'Build contains a symlink or special file')
        if path.is_file():
            name = path.relative_to(project).as_posix()
            total += path.stat().st_size
            require(total <= MAX_BYTES and len(files) < MAX_MEMBERS, 'Build cache exceeds limits')
            files[name] = digest(path)
    check_cache_names(files, modules)
    return files


def pack_cache(project, archive, modules):
    before = cache_manifest(project, modules)
    with tarfile.open(archive, 'w:gz', dereference=False, compresslevel=1) as target:
        for name in sorted(before):
            path = project / name
            require(path.is_file() and not path.is_symlink(), 'Cache file changed kind')
            info = tarfile.TarInfo(name)
            info.size = path.stat().st_size
            info.mode = 0o755 if path.stat().st_mode & 0o111 else 0o644
            with path.open('rb') as source:
                target.addfile(info, source)
    require(cache_manifest(project, modules) == before, 'Cache changed while packing')
    return before


def unpack_cache(archive, destination, modules, expected_files):
    """Validate all members before materializing regular build files only."""
    check_cache_names(expected_files, modules)
    with tarfile.open(archive, 'r:gz') as source:
        members = source.getmembers()
        require(len(members) <= MAX_MEMBERS, 'Too many TAR members')
        names, files, total = set(), set(), 0
        for member in members:
            path = safe_name(member.name)
            require(path.parts[:2] == ('.lake', 'build'), 'Archive escapes build directory')
            name = path.as_posix()
            require(name not in names, 'Duplicate TAR member')
            names.add(name)
            require((member.isdir() or member.isreg()) and not member.issparse(),
                    'TAR links, devices and sparse/special files are forbidden')
            require(member.size >= 0, 'Negative TAR member size')
            total += member.size
            require(total <= MAX_BYTES, 'Archive exceeds extraction limit')
            if member.isreg():
                files.add(name)
        require(files == set(expected_files), 'Archive and cache-file manifest differ')
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
    require(cache_manifest(destination, modules) == expected_files, 'Extracted cache digest differs')
    return total


def check_bundle(builder, directory, context, require_archive=True):
    artifact = load_json((directory / 'artifact.json').read_bytes())
    require(set(artifact) == {'schema', 'status', 'context_sha256', 'files', 'cache_files',
                              'build_complete', 'release_verified'}, 'Unexpected artifact manifest fields')
    require(artifact['schema'] == 1 and artifact['status'] == 'partial_compiled_prefix'
            and artifact['build_complete'] is False and artifact['release_verified'] is False,
            'Artifact claims a complete build or wrong stage')
    require(artifact['context_sha256'] == value_digest(context), 'Artifact context differs')
    require(set(artifact['files']) == BUNDLE_FILES, 'Bundle file inventory differs')
    for name, expected in artifact['files'].items():
        require(isinstance(expected, str) and len(expected) == 64, 'Invalid bundle digest')
        if require_archive or name != 'build.tar.gz':
            path = directory / name
            require(path.is_file() and not path.is_symlink(), 'Missing or unsafe bundle file')
            require(digest(path) == expected, 'Bundle digest differs: ' + name)
    plan = load_json((directory / 'plan.json').read_bytes())
    require(plan == context['plan'], 'Bundle plan differs from complete current plan')
    receipt = load_json((directory / 'stage.json').read_bytes())
    ledger_text = (directory / 'build.jsonl').read_text()
    builder.validate_prefix_receipt(receipt, ledger_text, context)
    check_cache_names(artifact['cache_files'], prefix_modules(context))
    return artifact, receipt, ledger_text


def pack(project, receipt_path, ledger_path, plan_path, output, cut):
    builder, context = current_context(project, cut)
    receipt_bytes, ledger_bytes, plan_bytes = (p.read_bytes() for p in
                                               (receipt_path, ledger_path, plan_path))
    builder.validate_prefix_receipt(load_json(receipt_bytes), ledger_bytes.decode(), context)
    require(load_json(plan_bytes) == context['plan'], 'Pack plan differs from complete source plan')
    require(not output.exists() and not output.is_symlink(), 'Pack output must be a new directory')
    require(not output.resolve().is_relative_to((project / '.lake/build').resolve()),
            'Cannot pack an archive inside the cache being archived')
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='.prefix-pack-', dir=output.parent) as temp:
        stage = Path(temp) / 'bundle'
        stage.mkdir()
        for name, data in [('stage.json', receipt_bytes), ('build.jsonl', ledger_bytes), ('plan.json', plan_bytes)]:
            (stage / name).write_bytes(data)
        files = pack_cache(project, stage / 'build.tar.gz', prefix_modules(context))
        artifact = {'schema': 1, 'status': 'partial_compiled_prefix',
                    'context_sha256': value_digest(context),
                    'files': {name: digest(stage / name) for name in sorted(BUNDLE_FILES)},
                    'cache_files': files, 'build_complete': False, 'release_verified': False}
        write_json(stage / 'artifact.json', artifact)
        check_bundle(builder, stage, context)
        require(current_context(project, cut)[1] == context, 'Source context changed while packing')
        require(receipt_path.read_bytes() == receipt_bytes and ledger_path.read_bytes() == ledger_bytes
                and plan_path.read_bytes() == plan_bytes, 'Prefix evidence changed while packing')
        stage.rename(output)
    print('Packed a partial same-run prefix. No complete-build or release pass is granted.')


def artifact_name(context):
    return f"linux-proof-prefix-{context['commit']}-{context['run_id']}-{context['run_attempt']}"


def api(path):
    return load_json(subprocess.check_output(['gh', 'api', 'repos/' + REPOSITORY + path]))


def validate_producer(run, jobs, listing, context):
    require(context['repository'] == REPOSITORY, 'Wrong current repository')
    require(run.get('id') == context['run_id'] and run.get('run_attempt') == context['run_attempt']
            and run.get('path') == context['workflow'], 'Wrong run, attempt or workflow')
    for field in ('repository', 'head_repository'):
        require(run.get(field, {}).get('full_name') == REPOSITORY, 'Wrong producer repository')
    event = run.get('event')
    require(event in ('push', 'workflow_dispatch', 'pull_request'), 'Unsupported workflow event')
    head = run.get('head_sha')
    require(isinstance(head, str) and len(head) == 40, 'Invalid API head SHA')
    # PR APIs name the source head; Actions tests GITHUB_SHA's merge commit.
    # The exact tested tree/commit remains mandatory in both stage contexts.
    if event != 'pull_request':
        require(head == context['commit'], 'Producer head differs from current commit')
    entries = jobs.get('jobs', [])
    require(jobs.get('total_count') == len(entries), 'Truncated job list')
    selected = [job for job in entries if job.get('name') == 'build-prefix']
    require(len(selected) == 1, 'Missing or duplicate prefix job')
    job = selected[0]
    require(job.get('run_id') == context['run_id'] and job.get('run_attempt') == context['run_attempt']
            and job.get('head_sha') == head, 'Wrong prefix job identity')
    require(job.get('status') == 'completed' and job.get('conclusion') == 'success',
            'Prefix job is not successfully complete')
    for name in PREFIX_STEPS:
        steps = [step for step in job.get('steps', []) if step.get('name') == name]
        require(len(steps) == 1 and steps[0].get('status') == 'completed'
                and steps[0].get('conclusion') == 'success', 'Prefix step did not pass: ' + name)
    artifacts = listing.get('artifacts', [])
    require(listing.get('total_count') == len(artifacts), 'Truncated artifact list')
    selected = [a for a in artifacts if a.get('name') == artifact_name(context)]
    require(len(selected) == 1, 'Missing or duplicate current-attempt prefix artifact')
    artifact = selected[0]
    require(type(artifact.get('id')) is int and artifact['id'] > 0
            and artifact.get('expired') is False, 'Invalid or expired prefix artifact')
    origin = artifact.get('workflow_run', {})
    require(origin.get('id') == context['run_id'] and origin.get('head_sha') == head,
            'Prefix artifact belongs to a different workflow run')
    return artifact, job['id']


def download_artifact(artifact, destination):
    with destination.open('xb') as output:
        subprocess.run(['gh', 'api', 'repos/' + REPOSITORY + '/actions/artifacts/'
                        + str(artifact['id']) + '/zip'], stdout=output, check=True)
    if artifact.get('digest') is not None:
        require(artifact['digest'] == 'sha256:' + digest(destination), 'Artifact ZIP digest differs')


def unpack_zip(archive, destination):
    wanted = BUNDLE_FILES | {'artifact.json'}
    with zipfile.ZipFile(archive) as source:
        members = source.infolist()
        require(len(members) <= MAX_MEMBERS, 'Too many ZIP members')
        names = set()
        for member in members:
            safe_name(member.filename)
            require(member.filename not in names, 'Duplicate ZIP member')
            names.add(member.filename)
            require(not ((member.external_attr >> 16) & 0o170000) == 0o120000, 'ZIP symlink rejected')
        require(names == wanted, 'Partial artifact ZIP file inventory differs')
        total = 0
        for member in members:
            total += member.file_size
            require(not member.is_dir() and 0 <= member.file_size and total <= MAX_BYTES,
                    'Invalid or oversized ZIP member')
            path = destination / member.filename
            with source.open(member) as data, path.open('xb') as output:
                shutil.copyfileobj(data, output, length=1024*1024)
            require(path.stat().st_size == member.file_size, 'Truncated ZIP member')


def validate_restored(project, receipt, ledger_text, context, restore_dir):
    builder = load_build(project)
    artifact, actual_receipt, actual_ledger = check_bundle(builder, restore_dir, context, require_archive=False)
    require(actual_receipt == receipt and actual_ledger == ledger_text, 'Final prefix evidence differs')
    restored = load_json((restore_dir / 'restored.json').read_bytes())
    require(set(restored) == {'schema', 'status', 'build_complete', 'release_verified', 'context_sha256',
                              'artifact_sha256', 'archive_sha256', 'cache_manifest_sha256', 'producer'},
            'Unexpected restore receipt fields')
    require(restored['schema'] == 1 and restored['status'] == 'partial_prefix_restored'
            and restored['build_complete'] is False and restored['release_verified'] is False,
            'Restore receipt grants an invalid completion')
    require(restored['context_sha256'] == value_digest(context)
            and restored['artifact_sha256'] == digest(restore_dir / 'artifact.json')
            and restored['archive_sha256'] == artifact['files']['build.tar.gz']
            and restored['cache_manifest_sha256'] == value_digest(artifact['cache_files']),
            'Restore receipt binding differs')
    provenance = restored['producer']
    require(set(provenance) == {'repository', 'run_id', 'run_attempt', 'commit', 'prefix_job', 'artifact_id'}
            and provenance['repository'] == context['repository']
            and provenance['run_id'] == context['run_id'] and provenance['run_attempt'] == context['run_attempt']
            and provenance['commit'] == context['commit'], 'Restored producer identity differs')
    for field in ('prefix_job', 'artifact_id'):
        require(type(provenance[field]) is int and provenance[field] > 0, 'Invalid producer identifier')
    require(cache_manifest(project, prefix_modules(context)) == artifact['cache_files'],
            'Restored cache files differ before suffix build')
    return restored


def check_restore_output(project, output):
    require(not output.exists() and not output.is_symlink(), 'Restore output must be a fresh directory')
    require(output.resolve().is_relative_to((project / '.verification').resolve()),
            'Restore metadata must stay in project .verification')
    require(not (project / '.verification').is_symlink(), 'Unsafe verification directory')


def restore_bundle(project, bundle, context, output, producer):
    """Materialize a validated bundle; caller separately authenticates provenance.

    The production CLI obtains producer from the same-run GitHub API. Offline
    tests may supply clearly labelled fixture provenance, never a CI claim.
    """
    check_restore_output(project, output)
    builder, actual_context = current_context(project, context['cut'])
    require(actual_context == context, 'Bundle consumer context differs')
    manifest, receipt, ledger_text = check_bundle(builder, bundle, context)
    lake = project / '.lake'
    require(lake.is_dir() and not lake.is_symlink(), 'Unsafe dependency directory')
    target = lake / 'build'
    require(not target.is_symlink() and (not target.exists() or target.is_dir()), 'Unsafe cache destination')
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='.prefix-restore-', dir=lake) as stage:
        unpack_cache(bundle / 'build.tar.gz', Path(stage), prefix_modules(context), manifest['cache_files'])
        require(current_context(project, context['cut'])[1] == context, 'Source changed during prefix restoration')
        backup = Path(stage) / 'previous-build'
        metadata_stage = Path(stage) / 'metadata'; metadata_stage.mkdir()
        for name in ('stage.json', 'build.jsonl', 'plan.json', 'artifact.json'):
            shutil.copyfile(bundle / name, metadata_stage / name)
        restored = {'schema': 1, 'status': 'partial_prefix_restored', 'build_complete': False,
                    'release_verified': False, 'context_sha256': value_digest(context),
                    'artifact_sha256': digest(bundle / 'artifact.json'),
                    'archive_sha256': manifest['files']['build.tar.gz'],
                    'cache_manifest_sha256': value_digest(manifest['cache_files']),
                    'producer': producer}
        write_json(metadata_stage / 'restored.json', restored)
        moved_old, installed = False, False
        try:
            if target.exists():
                target.rename(backup)
                moved_old = True
            (Path(stage) / '.lake/build').rename(target)
            installed = True
            validate_restored(project, receipt, ledger_text, context, metadata_stage)
            require(current_context(project, context['cut'])[1] == context, 'Source changed after restoration')
            metadata_stage.rename(output)
        except BaseException:
            if installed and target.exists():
                shutil.rmtree(target)
            if moved_old and backup.exists():
                backup.rename(target)
            raise
    return restored


def restore(project, cut, output):
    _, context = current_context(project, cut)
    check_restore_output(project, output)
    run = api(f"/actions/runs/{context['run_id']}")
    jobs = api(f"/actions/runs/{context['run_id']}/attempts/{context['run_attempt']}/jobs?per_page=100")
    listing = api(f"/actions/runs/{context['run_id']}/artifacts?per_page=100")
    artifact, job = validate_producer(run, jobs, listing, context)
    with tempfile.TemporaryDirectory(prefix='same-run-prefix-') as temp:
        download = Path(temp) / 'artifact.zip'
        bundle = Path(temp) / 'bundle'; bundle.mkdir()
        download_artifact(artifact, download)
        unpack_zip(download, bundle)
        producer = {'repository': context['repository'], 'run_id': context['run_id'],
                    'run_attempt': context['run_attempt'], 'commit': context['commit'],
                    'prefix_job': job, 'artifact_id': artifact['id']}
        restore_bundle(project, bundle, context, output, producer)
    print('Restored only the exact same-run prefix. The suffix, roots and all release gates remain required.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='action', required=True)
    for name in ('pack', 'restore'):
        command = sub.add_parser(name)
        command.add_argument('--project', type=Path, default=Path(__file__).resolve().parents[1])
        command.add_argument('--cut', type=int, required=True)
        command.add_argument('--output', type=Path, required=True)
        if name == 'pack':
            for option in ('receipt', 'ledger', 'plan'):
                command.add_argument('--' + option, type=Path, required=True)
    args = parser.parse_args()
    project = args.project.resolve()
    if args.action == 'pack':
        pack(project, args.receipt.resolve(), args.ledger.resolve(), args.plan.resolve(), args.output.absolute(), args.cut)
    else:
        restore(project, args.cut, args.output.absolute())


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, tarfile.TarError, zipfile.BadZipFile, subprocess.CalledProcessError) as error:
        print('Same-run prefix artifact rejected: ' + str(error), file=sys.stderr)
        raise SystemExit(1)
