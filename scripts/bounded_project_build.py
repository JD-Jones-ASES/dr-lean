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
from pathlib import Path
import re
import subprocess
import time

ROOTS = ('DR', 'Test')
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
    return name.split('.')[0] in ROOTS


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
    result = runner(['git', 'ls-files', '-z', '--', 'DR.lean', 'Test.lean', 'DR', 'Test'],
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
    args = parser.parse_args()
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
        if args.report:
            print(json.dumps({'status': 'dry_run', 'project_modules': len(plan.order),
                              'batches': len(plan.batches), 'excluded_local_modules': len(plan.excluded),
                              'tracked_coverage_checked': plan.tracked is not None,
                              'report': str(args.report)}))
        else:
            print(report, end='')
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
