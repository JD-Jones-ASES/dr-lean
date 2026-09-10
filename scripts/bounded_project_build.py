#!/usr/bin/env python3
"""Build the actual DR/Test import closure with at most two project targets.

This bounds overlap between project modules, not Mathlib dependency jobs or
asynchronous declarations inside one Lean module. It changes no proof checks.
The final explicit +DR/+Test targets check both complete root modules.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import re
import subprocess
import tempfile
import time

ROOTS = ('DR', 'Test')
PROJECT_MODULE_ROOTS = (*ROOTS, 'Solution')
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")


def lean_imports(text):
    """Read Lean's import header, failing closed on unsupported import names."""
    text = text.removeprefix('\ufeff')
    pos = 0

    def skip(at):
        while at < len(text):
            if text[at].isspace():
                at += 1
            elif text.startswith('--', at):
                end = text.find('\n', at + 2)
                at = len(text) if end < 0 else end + 1
            elif text.startswith('/-', at):
                depth = 1
                at += 2
                while depth:
                    if at >= len(text):
                        raise ValueError('Unterminated block comment in Lean import header')
                    if text.startswith('/-', at):
                        depth += 1
                        at += 2
                    elif text.startswith('-/', at):
                        depth -= 1
                        at += 2
                    else:
                        at += 1
            else:
                break
        return at

    def keyword(word, at):
        at = skip(at)
        end = at + len(word)
        if text.startswith(word, at) and (end == len(text) or
                not (text[end].isalnum() or text[end] in "_'.«»")):
            return skip(end)
        return None

    pos = skip(pos)
    after = keyword('module', pos)
    if after is not None:
        pos = after
    after = keyword('prelude', pos)
    if after is not None:
        pos = after
    imports = []
    while True:
        at = pos
        after = keyword('public', at)
        if after is not None:
            at = after
        after = keyword('meta', at)
        if after is not None:
            at = after
        after = keyword('import', at)
        if after is None:
            return tuple(dict.fromkeys(imports))
        at = after
        after = keyword('all', at)
        if after is not None:
            at = after
        match = NAME.match(text, at)
        if match is None:
            raise ValueError('Unsupported or missing Lean import name')
        end = match.end()
        if end < len(text) and not text[end].isspace() and not (
                text.startswith('--', end) or text.startswith('/-', end)):
            raise ValueError('Unsupported Lean import name or separator')
        imports.append(match.group())
        pos = skip(end)


def is_project_module(name):
    return name.split('.')[0] in PROJECT_MODULE_ROOTS


def source_path(root, name):
    if not NAME.fullmatch(name) or not is_project_module(name):
        raise ValueError(f'Unsupported project module: {name}')
    path = root.joinpath(*name.split('.')).with_suffix('.lean')
    if not path.is_file():
        raise ValueError(f'Missing project import: {name} ({path})')
    if not path.resolve().is_relative_to(root.resolve()):
        raise ValueError(f'Project import escapes source root: {name}')
    return path


@dataclass
class BuildPlan:
    root: Path
    modules: dict
    order: tuple
    batches: tuple
    excluded: tuple
    tracked: tuple | None = None

    def report(self):
        return {'scope': 'exact DR.lean/Test.lean project import closure',
                'roots': list(ROOTS), 'project_module_count': len(self.order),
                'batch_count': len(self.batches), 'batches': self.batches,
                'modules': [self.modules[name] for name in self.order],
                'excluded_project_modules': self.excluded,
                'tracked_project_modules': self.tracked,
                'tracked_coverage_checked': self.tracked is not None}


def make_plan(root, batch_size=2):
    if type(batch_size) is not int or not 1 <= batch_size <= 2:
        raise ValueError('Project batch size must be 1 or 2')
    root = Path(root).resolve()
    modules, order, active = {}, [], []

    def visit(name):
        if name in active:
            raise ValueError('Cyclic project imports: ' + ' -> '.join(active[active.index(name):] + [name]))
        if name in modules:
            return
        path = source_path(root, name)
        data = path.read_bytes()
        imports = lean_imports(data.decode('utf-8'))
        dependencies = tuple(value for value in imports if is_project_module(value))
        active.append(name)
        for dependency in dependencies:
            visit(dependency)
        active.pop()
        modules[name] = {'name': name, 'path': path.relative_to(root).as_posix(),
                         'sha256': hashlib.sha256(data).hexdigest(),
                         'project_imports': dependencies,
                         'external_imports': tuple(value for value in imports if not is_project_module(value))}
        order.append(name)

    for name in ROOTS:
        visit(name)
    all_local = set(ROOTS)
    if (root / 'Solution.lean').is_file():
        all_local.add('Solution')
    for prefix in ROOTS:
        for path in (root / prefix).rglob('*.lean'):
            all_local.add('.'.join(path.relative_to(root).with_suffix('').parts))
    batches = tuple(tuple(order[start:start + batch_size]) for start in range(0, len(order), batch_size))
    return BuildPlan(root, modules, tuple(order), batches, tuple(sorted(all_local - modules.keys())))


def verify_sources(plan):
    for name, info in plan.modules.items():
        actual = hashlib.sha256(source_path(plan.root, name).read_bytes()).hexdigest()
        if actual != info['sha256']:
            raise ValueError(f'Project source changed during bounded build: {name}')


def validate_tracked_coverage(plan, paths):
    """CI mode: the closure must equal the tracked project Lean source set."""
    tracked = set()
    for value in paths:
        path = Path(value)
        if path.suffix != '.lean':
            continue
        # Challenge contains only independently compared statement holes.
        # It is compiled separately without the proof warning-as-error rule.
        if value == 'Challenge.lean':
            continue
        if path.is_absolute() or '..' in path.parts:
            raise ValueError(f'Unsafe tracked project source path: {value}')
        name = '.'.join(path.with_suffix('').parts)
        if not NAME.fullmatch(name) or not is_project_module(name):
            raise ValueError(f'Unsupported tracked project module: {value}')
        tracked.add(name)
    omitted = tracked - plan.modules.keys()
    untracked = plan.modules.keys() - tracked
    if omitted or untracked:
        raise ValueError('Tracked project coverage mismatch: ' + json.dumps({
            'omitted_tracked_modules': sorted(omitted),
            'untracked_imported_modules': sorted(untracked)}))
    plan.tracked = tuple(sorted(tracked))


def check_tracked_coverage(plan, runner=subprocess.run):
    result = runner(['git', 'ls-files', '-z', '--', 'DR.lean', 'Test.lean', 'Solution.lean', 'DR', 'Test'],
                    cwd=plan.root, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if result.returncode:
        raise ValueError('Could not read tracked project source coverage: ' + result.stderr)
    validate_tracked_coverage(plan, [path for path in result.stdout.split('\0') if path])


def run_plan(plan, lake='lake', log=None, runner=subprocess.run):
    """Every argument is a separate argv entry; a failed batch stops the run."""
    verify_sources(plan)
    records = []
    targets = [(batch, 'module_batch') for batch in plan.batches]
    # Both roots are already built; this last check retains the complete roots.
    targets.append((ROOTS, 'root_check'))
    for batch, phase in targets:
        command = [str(lake), '--wfail', 'build', *('+' + name for name in batch)]
        print(json.dumps({'status': 'checking', 'phase': phase, 'modules': batch}), flush=True)
        stamp = time.monotonic()
        result = runner(command, cwd=plan.root, text=True, stdout=subprocess.PIPE,
                        stderr=subprocess.STDOUT)
        record = {'status': 'passed' if result.returncode == 0 else 'failed',
                  'phase': phase, 'modules': batch, 'argv': command,
                  'seconds': round(time.monotonic() - stamp, 3), 'exit_code': result.returncode,
                  'output': result.stdout}
        records.append(record)
        if log is not None:
            log.write(json.dumps(record) + '\n')
            log.flush()
        print(json.dumps({key: value for key, value in record.items() if key != 'output'}), flush=True)
        if result.returncode:
            print(result.stdout, flush=True)
            raise subprocess.CalledProcessError(result.returncode, command, output=result.stdout)
    verify_sources(plan)
    print(json.dumps({'status': 'complete', 'project_modules': len(plan.order),
                      'root_check': list(ROOTS)}), flush=True)
    return records


def subprocess_exit_status(returncode):
    """Use the shell's 128+signal convention for a child killed by a signal."""
    return returncode if returncode >= 0 else 128 - returncode


def canonical_bytes(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode('utf-8')


def sha256_bytes(value):
    return hashlib.sha256(value).hexdigest()


def strict_json(value):
    def unique(pairs):
        result = {}
        for key, item in pairs:
            if key in result:
                raise ValueError('Duplicate receipt JSON key: ' + key)
            result[key] = item
        return result
    return json.loads(value, object_pairs_hook=unique)


def stage_require(value, message):
    if not value:
        raise ValueError(message)


def _git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args], text=True).strip()


def stage_context(plan, cut):
    """Bind both stages to the same entire source tree, plan and CI execution."""
    stage_require(type(cut) is int and 0 < cut < len(plan.batches),
                  'Stage cut must be strictly inside the complete batch plan')
    check_tracked_coverage(plan)
    verify_sources(plan)
    stage_require(not plan.excluded, 'Staged CI excludes local project modules')
    root = plan.root
    commit = _git(root, 'rev-parse', 'HEAD')
    stage_require(re.fullmatch('[0-9a-f]{40}', commit) is not None
                  and os.environ.get('GITHUB_SHA') == commit, 'Stage source commit differs from CI')
    stage_require(not _git(root, 'status', '--porcelain=v1', '--untracked-files=all'),
                  'Staged build requires a clean complete source tree')
    repository = os.environ.get('GITHUB_REPOSITORY')
    stage_require(repository == 'JD-Jones-ASES/dr-lean', 'Wrong staged-build repository')
    ids = [os.environ.get(key, '') for key in ('GITHUB_RUN_ID', 'GITHUB_RUN_ATTEMPT')]
    stage_require(all(re.fullmatch('[1-9][0-9]*', value) for value in ids),
                  'Missing or invalid workflow run/attempt identity')
    inputs = {}
    for relative in ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml',
                     'scripts/bounded_project_build.py', 'scripts/stage_build_artifact.py'):
        path = root / relative
        stage_require(path.is_file() and not path.is_symlink()
                      and path.resolve().is_relative_to(root), 'Missing/unsafe staged input: ' + relative)
        _git(root, 'ls-files', '--error-unmatch', '--', relative)
        inputs[relative] = sha256_bytes(path.read_bytes())
    manifest = strict_json((root / 'lake-manifest.json').read_text())
    dependencies = {}
    for item in manifest['packages']:
        name = item['name']
        stage_require(isinstance(name, str) and re.fullmatch('[A-Za-z0-9_-]+', name)
                      and name not in dependencies, 'Invalid dependency name')
        stage_require(item['type'] == 'git' and re.fullmatch('[0-9a-f]{40}', item['rev']),
                      'Staged dependency is not an exact Git pin')
        directory = root / '.lake/packages' / name
        stage_require(directory.is_dir() and not directory.is_symlink()
                      and directory.resolve().is_relative_to(root), 'Unsafe/missing dependency')
        stage_require(_git(directory, 'rev-parse', 'HEAD') == item['rev'], 'Dependency revision changed: ' + name)
        stage_require(not _git(directory, 'status', '--porcelain=v1', '--untracked-files=all'),
                      'Dependency source is dirty: ' + name)
        dependencies[name] = {'revision': item['rev'], 'url': item['url']}
    report = strict_json(json.dumps(plan.report()))
    workflow = '.github/workflows/development.yml'
    path = root / workflow
    stage_require(path.is_file() and not path.is_symlink()
                  and path.resolve().is_relative_to(root), 'Missing/unsafe staged workflow')
    _git(root, 'ls-files', '--error-unmatch', '--', workflow)
    return {'schema': 1, 'repository': repository, 'run_id': int(ids[0]),
            'run_attempt': int(ids[1]), 'commit': commit,
            'git_tree': _git(root, 'rev-parse', 'HEAD^{tree}'),
            'workflow': workflow, 'workflow_sha256': sha256_bytes(path.read_bytes()),
            'toolchain': (root / 'lean-toolchain').read_text().strip(),
            'platform': {'system': platform.system(), 'machine': platform.machine()},
            'inputs': inputs, 'dependencies': dependencies, 'plan': report,
            'plan_sha256': sha256_bytes(canonical_bytes(report)), 'cut': cut}


def validate_stage_ledger(ledger_text, context, complete=False):
    """Validate the exact ordered prefix or whole plan, with no skipped batch."""
    report = context['plan']
    batches = report['batches']
    stage_require(report['tracked_coverage_checked'] is True
                  and report['roots'] == list(ROOTS), 'Stage plan lacks complete root coverage')
    names = [name for batch in batches for name in batch]
    stage_require(report['batch_count'] == len(batches)
                  and report['project_module_count'] == len(names) == len(set(names))
                  and names == [m['name'] for m in report['modules']]
                  and set(names) == set(report['tracked_project_modules']),
                  'Stage plan has missing, duplicate or reordered modules')
    stage_require(context['plan_sha256'] == sha256_bytes(canonical_bytes(report)),
                  'Stage plan digest mismatch')
    cut = context['cut']
    stage_require(type(cut) is int and 0 < cut < len(batches), 'Invalid stage cut')
    stop = len(batches) if complete else cut
    expected = [(i, batches[i], 'module_batch') for i in range(stop)]
    if complete:
        expected.append((None, list(ROOTS), 'root_check'))
    records = [strict_json(line) for line in ledger_text.splitlines() if line.strip()]
    stage_require(len(records) == len(expected), 'Stage ledger is partial or has extra batches')
    keys = {'status', 'phase', 'modules', 'argv', 'seconds', 'exit_code', 'output', 'batch_index'}
    for record, (index, batch, phase) in zip(records, expected):
        stage_require(set(record) == keys and record['status'] == 'passed'
                      and type(record['exit_code']) is int and record['exit_code'] == 0
                      and (record['batch_index'] is None if index is None else
                           type(record['batch_index']) is int and record['batch_index'] == index)
                      and record['phase'] == phase
                      and record['modules'] == batch and 1 <= len(batch) <= 2
                      and record['argv'] == ['lake', '--wfail', 'build', *('+' + n for n in batch)]
                      and isinstance(record['output'], str)
                      and type(record['seconds']) in (int, float)
                      and math.isfinite(record['seconds']) and record['seconds'] >= 0,
                      'Stage ledger contains a failed, altered or reordered command')
    return records


def validate_prefix_receipt(receipt, ledger_text, context):
    keys = {'schema', 'status', 'stage', 'interval', 'covered_batches', 'context',
            'context_sha256', 'ledger_sha256', 'previous_receipt_sha256',
            'root_check', 'build_complete', 'release_verified'}
    stage_require(set(receipt) == keys and type(receipt['schema']) is int and receipt['schema'] == 1
                  and canonical_bytes(receipt['context']) == canonical_bytes(context)
                  and receipt['context_sha256'] == sha256_bytes(canonical_bytes(context)),
                  'Prefix receipt source/run/plan binding differs')
    stage_require(receipt['status'] == 'partial_stage_passed' and receipt['stage'] == 'prefix'
                  and receipt['interval'] == [0, context['cut']]
                  and all(type(value) is int for value in receipt['interval'])
                  and type(receipt['covered_batches']) is int
                  and receipt['covered_batches'] == context['cut']
                  and receipt['previous_receipt_sha256'] is None
                  and receipt['root_check'] is False and receipt['build_complete'] is False
                  and receipt['release_verified'] is False,
                  'Receipt is not the exact successful partial prefix')
    stage_require(receipt['ledger_sha256'] == sha256_bytes(ledger_text.encode('utf-8')),
                  'Prefix ledger digest differs')
    return validate_stage_ledger(ledger_text, context)


def run_stage(plan, stage, cut, context, log, runner=subprocess.run,
              prior_receipt=None, prior_ledger=None, context_reader=stage_context):
    """A prefix never checks final roots or emits a complete proof-build claim."""
    stage_require(stage in ('prefix', 'final'), 'Unknown bounded build stage')
    stage_require(context == context_reader(plan, cut), 'Stage context changed before build')
    chunks, records = [], []
    if stage == 'prefix':
        stage_require(prior_receipt is None and prior_ledger is None, 'Prefix cannot inherit another prefix')
        start, stop = 0, cut
    else:
        stage_require(prior_receipt is not None and prior_ledger is not None,
                      'Final stage requires its exact restored prefix')
        records = validate_prefix_receipt(prior_receipt, prior_ledger, context)
        chunks.append(prior_ledger)
        log.write(prior_ledger)
        log.flush()
        start, stop = cut, len(plan.batches)
    targets = [(i, plan.batches[i], 'module_batch') for i in range(start, stop)]
    if stage == 'final':
        targets.append((None, ROOTS, 'root_check'))
    for index, batch, phase in targets:
        argv = ['lake', '--wfail', 'build', *('+' + name for name in batch)]
        print(json.dumps({'status': 'checking', 'stage': stage, 'batch_index': index,
                          'phase': phase, 'modules': batch}), flush=True)
        stamp = time.monotonic()
        result = runner(argv, cwd=plan.root, text=True, stdout=subprocess.PIPE,
                        stderr=subprocess.STDOUT)
        record = {'status': 'passed' if result.returncode == 0 else 'failed',
                  'phase': phase, 'modules': list(batch), 'argv': argv,
                  'seconds': round(time.monotonic() - stamp, 3), 'exit_code': result.returncode,
                  'output': result.stdout, 'batch_index': index}
        records.append(record)
        line = json.dumps(record) + '\n'
        chunks.append(line)
        log.write(line)
        log.flush()
        print(json.dumps({k:v for k,v in record.items() if k != 'output'}), flush=True)
        if result.returncode:
            print(result.stdout, flush=True)
            raise subprocess.CalledProcessError(result.returncode, argv, output=result.stdout)
    stage_require(context == context_reader(plan, cut), 'Stage context changed during build')
    ledger_text = ''.join(chunks)
    validate_stage_ledger(ledger_text, context, complete=(stage == 'final'))
    complete = stage == 'final'
    receipt = {'schema': 1, 'status': 'complete_build' if complete else 'partial_stage_passed',
               'stage': stage, 'interval': [start, stop], 'covered_batches': stop,
               'context': context, 'context_sha256': sha256_bytes(canonical_bytes(context)),
               'ledger_sha256': sha256_bytes(ledger_text.encode('utf-8')),
               'previous_receipt_sha256': sha256_bytes(canonical_bytes(prior_receipt)) if complete else None,
               'root_check': complete, 'build_complete': complete, 'release_verified': False}
    print(json.dumps({'status': receipt['status'], 'stage': stage,
                      'covered_batches': stop, 'total_batches': len(plan.batches),
                      'build_complete': complete, 'release_verified': False}), flush=True)
    return records, receipt


def invalidate_stage_receipt(path):
    path = Path(path)
    stage_require(not path.is_symlink(), 'Unsafe stage receipt path')
    path.parent.mkdir(parents=True, exist_ok=True)
    path.unlink(missing_ok=True)


def write_stage_receipt(path, value):
    with tempfile.NamedTemporaryFile(mode='w', dir=path.parent,
                                    prefix='.stage-receipt-', delete=False) as data:
        temporary = Path(data.name)
        data.write(json.dumps(value, indent=2) + '\n')
    try:
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


def run_stage_cli(args, plan):
    stage_require(args.cut is not None and args.stage_receipt is not None
                  and args.log is not None and args.report is not None,
                  'Staged build requires cut, stage receipt, log and full plan report')
    stage_require(args.lake == 'lake', 'CI stages use the pinned lake command from PATH')
    context = stage_context(plan, args.cut)
    prior_receipt, prior_ledger = None, None
    if args.stage == 'final':
        stage_require(args.prior_stage_dir is not None, 'Final stage has no restored artifact')
        directory = args.prior_stage_dir.resolve()
        stage_require(args.log.resolve() != directory / 'build.jsonl'
                      and args.stage_receipt.resolve() != directory / 'stage.json',
                      'Final output must not overwrite its prefix evidence')
        prior_receipt = strict_json((directory / 'stage.json').read_text())
        prior_ledger = (directory / 'build.jsonl').read_text()
        # Imported only for final CLI; the artifact helper imports this module's
        # pure protocol functions without invoking the CLI.
        from stage_build_artifact import validate_restored
        validate_restored(plan.root, prior_receipt, prior_ledger, context, directory)
    else:
        stage_require(args.prior_stage_dir is None, 'Prefix cannot restore a prior stage')
    args.log.parent.mkdir(parents=True, exist_ok=True)
    with args.log.open('w') as log:
        _, receipt = run_stage(plan, args.stage, args.cut, context, log,
                              prior_receipt=prior_receipt, prior_ledger=prior_ledger)
    stage_require(receipt['ledger_sha256'] == sha256_bytes(args.log.read_bytes()),
                  'Written stage ledger changed before receipt publication')
    write_stage_receipt(args.stage_receipt, receipt)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root-dir', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--batch-size', type=int, default=2)
    parser.add_argument('--lake', default='lake')
    parser.add_argument('--dry-run', action='store_true')
    parser.add_argument('--require-no-excluded', action='store_true',
                        help='reject every local project Lean file outside the root import closure')
    parser.add_argument('--check-tracked-coverage', action='store_true',
                        help='CI: require exact equality with git-tracked DR/Test Lean sources')
    parser.add_argument('--report', type=Path)
    parser.add_argument('--log', type=Path)
    parser.add_argument('--stage', choices=('prefix', 'final'))
    parser.add_argument('--cut', type=int)
    parser.add_argument('--stage-receipt', type=Path)
    parser.add_argument('--prior-stage-dir', type=Path)
    args = parser.parse_args()
    prior = args.prior_stage_dir.resolve() if args.prior_stage_dir is not None else None
    if args.stage_receipt is not None:
        stage_require(prior is None or not args.stage_receipt.resolve().is_relative_to(prior),
                      'Stage outputs must not overwrite restored prefix evidence')
        invalidate_stage_receipt(args.stage_receipt)
    if prior is not None:
        for path in (args.log, args.report):
            stage_require(path is None or not path.resolve().is_relative_to(prior),
                          'Stage outputs must not overwrite restored prefix evidence')
    if args.stage is None and any(value is not None for value in
                                  (args.cut, args.stage_receipt, args.prior_stage_dir)):
        raise ValueError('Stage options require an explicit stage')
    plan = make_plan(args.root_dir, args.batch_size)
    if args.require_no_excluded and plan.excluded:
        raise ValueError('Local project sources excluded from the root closure: ' + ', '.join(plan.excluded))
    if args.check_tracked_coverage:
        check_tracked_coverage(plan)
    report = json.dumps(plan.report(), indent=2) + '\n'
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(report)
    if args.dry_run:
        stage_require(args.stage is None, 'Use the complete un-staged dry run for planning')
        if args.report:
            print(json.dumps({'status': 'dry_run', 'project_modules': len(plan.order),
                              'batches': len(plan.batches), 'excluded_local_modules': len(plan.excluded),
                              'tracked_coverage_checked': plan.tracked is not None,
                              'report': str(args.report)}))
        else:
            print(report, end='')
        return
    if args.stage is not None:
        run_stage_cli(args, plan)
        return
    if args.log:
        args.log.parent.mkdir(parents=True, exist_ok=True)
        with args.log.open('w') as log:
            run_plan(plan, args.lake, log)
    else:
        run_plan(plan, args.lake)


if __name__ == '__main__':
    try:
        main()
    except subprocess.CalledProcessError as error:
        raise SystemExit(subprocess_exit_status(error.returncode))
