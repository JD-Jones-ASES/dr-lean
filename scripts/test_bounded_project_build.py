#!/usr/bin/env python3
"""Graph, coverage and subprocess controls for the bounded CI build helper."""
from __future__ import annotations

import argparse
from contextlib import redirect_stdout
import io
from pathlib import Path
import subprocess
import tempfile
import unittest

from bounded_project_build import (ROOTS, check_tracked_coverage, lean_imports,
                                   make_plan, run_plan, subprocess_exit_status,
                                   validate_tracked_coverage)


def write(root, module, contents):
    path = root.joinpath(*module.split('.')).with_suffix('.lean')
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(contents)


def fixture(root, unused=True):
    write(root, 'DR', 'import DR.Top\n')
    write(root, 'Test', 'import Test.Cases\n')
    write(root, 'DR.Base', 'namespace BoundedSmoke\ntheorem base : (1 : Nat) + 1 = 2 := by decide\nend BoundedSmoke\n')
    write(root, 'DR.Left', 'import DR.Base\n')
    write(root, 'DR.Right', 'import DR.Base\n')
    write(root, 'DR.Top', 'import DR.Left\nimport DR.Right\n')
    write(root, 'Test.Cases', 'import DR.Top\nexample : (1 : Nat) + 1 = 2 := BoundedSmoke.base\n')
    if unused:
        write(root, 'DR.Unused', 'example : True := True.intro\n')


class BoundedBuildTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='dr-build-graph-')
        self.root = Path(self.temp.name)
        fixture(self.root)

    def tearDown(self):
        self.temp.cleanup()

    def test_header_nested_comments_flags_and_body_strings(self):
        source = '''/- import DR.Ghost /- import DR.Other -/ -/
module
prelude
public meta import all DR.Base -- trailing import DR.Ghost
import
  Mathlib.Data.Nat.Basic
import DR.Base
def text := "import DR.NotAnImport"
/- import DR.AlsoNotAnImport -/
'''
        self.assertEqual(lean_imports(source), ('DR.Base', 'Mathlib.Data.Nat.Basic'))
        self.assertEqual(lean_imports('module\npublic section\n'), ())

    def test_unsupported_or_broken_header_rejects(self):
        for source in ('import DR.\n', 'import «DR.Base»\n', 'import\n', '/- unfinished'):
            with self.subTest(source=source), self.assertRaises(ValueError):
                lean_imports(source)

    def test_exact_closure_shared_dependency_and_dependency_first_order(self):
        plan = make_plan(self.root)
        self.assertEqual(set(plan.order), {'DR', 'Test', 'DR.Base', 'DR.Left',
                                         'DR.Right', 'DR.Top', 'Test.Cases'})
        self.assertEqual(len(plan.order), len(set(plan.order)))
        self.assertEqual(plan.excluded, ('DR.Unused',))
        flattened = tuple(name for batch in plan.batches for name in batch)
        self.assertEqual(flattened, plan.order)
        positions = {name: index for index, name in enumerate(plan.order)}
        for name, info in plan.modules.items():
            for dependency in info['project_imports']:
                self.assertLess(positions[dependency], positions[name])
        self.assertTrue(all(1 <= len(batch) <= 2 for batch in plan.batches))

    def test_missing_import_rejects(self):
        write(self.root, 'DR.Left', 'import DR.Missing\n')
        with self.assertRaisesRegex(ValueError, 'Missing project import: DR.Missing'):
            make_plan(self.root)

    def test_cycles_and_self_cycles_reject(self):
        write(self.root, 'DR.Base', 'import DR.Top\n')
        with self.assertRaisesRegex(ValueError, 'Cyclic project imports'):
            make_plan(self.root)
        write(self.root, 'DR.Base', 'import DR.Base\n')
        with self.assertRaisesRegex(ValueError, 'DR.Base -> DR.Base'):
            make_plan(self.root)

    def test_external_import_is_reported_not_traversed(self):
        write(self.root, 'DR.Base', 'import Mathlib.DoesNotExist\n')
        plan = make_plan(self.root)
        self.assertEqual(plan.modules['DR.Base']['external_imports'], ('Mathlib.DoesNotExist',))
        self.assertNotIn('Mathlib.DoesNotExist', plan.modules)

    def test_invalid_batch_sizes_reject(self):
        for size in (0, 3, 100, True, 1.0):
            with self.subTest(size=size), self.assertRaises(ValueError):
                make_plan(self.root, size)

    def test_tracked_extra_missing_and_exact_coverage(self):
        plan = make_plan(self.root)
        paths = [info['path'] for info in plan.modules.values()]
        for mutated in (paths + ['DR/Unused.lean'], paths[:-1]):
            with self.subTest(paths=mutated), self.assertRaisesRegex(ValueError, 'coverage mismatch'):
                validate_tracked_coverage(plan, mutated)
        validate_tracked_coverage(plan, paths)
        self.assertEqual(set(plan.tracked), set(plan.order))
        self.assertTrue(plan.report()['tracked_coverage_checked'])

    def test_git_coverage_uses_exact_safe_argv(self):
        plan = make_plan(self.root)

        def git(command, **kwargs):
            self.assertEqual(command, ['git', 'ls-files', '-z', '--', 'DR.lean', 'Test.lean', 'DR', 'Test'])
            return subprocess.CompletedProcess(command, 0,
                '\0'.join(info['path'] for info in plan.modules.values()) + '\0', '')

        check_tracked_coverage(plan, git)
        self.assertEqual(set(plan.tracked), set(plan.order))

    def test_safe_module_targets_bounded_batches_and_complete_root_check(self):
        plan = make_plan(self.root)
        calls = []
        executable = '/path with spaces/lake;literal'

        def runner(command, **kwargs):
            calls.append(command)
            self.assertEqual(kwargs['cwd'], self.root.resolve())
            self.assertNotIn('shell', kwargs)
            return subprocess.CompletedProcess(command, 0, 'checked\n')

        with redirect_stdout(io.StringIO()):
            records = run_plan(plan, executable, runner=runner)
        self.assertEqual(len(calls), len(plan.batches) + 1)
        self.assertTrue(all(command[:3] == [executable, '--wfail', 'build'] for command in calls))
        self.assertTrue(all(1 <= len(command[3:]) <= 2 for command in calls))
        self.assertEqual(calls[-1][3:], ['+DR', '+Test'])
        requested = [value[1:] for command in calls[:-1] for value in command[3:]]
        self.assertEqual(tuple(requested), plan.order)
        self.assertEqual(records[-1]['phase'], 'root_check')

    def test_nonzero_batch_fails_fast_and_preserves_exit_code(self):
        calls = []
        log = io.StringIO()

        def runner(command, **kwargs):
            calls.append(command)
            return subprocess.CompletedProcess(command, 143, 'stopped\n')

        with redirect_stdout(io.StringIO()), self.assertRaises(subprocess.CalledProcessError) as caught:
            run_plan(make_plan(self.root), log=log, runner=runner)
        self.assertEqual(caught.exception.returncode, 143)
        self.assertEqual(len(calls), 1)
        self.assertIn('"status": "failed"', log.getvalue())
        self.assertNotIn('root_check', log.getvalue())

    def test_child_signal_uses_standard_shell_status(self):
        self.assertEqual(subprocess_exit_status(-15), 143)
        self.assertEqual(subprocess_exit_status(-9), 137)
        self.assertEqual(subprocess_exit_status(143), 143)
        self.assertEqual(subprocess_exit_status(1), 1)

    def test_changed_sources_do_not_report_completion(self):
        plan = make_plan(self.root)

        def runner(command, **kwargs):
            write(self.root, 'DR.Base', 'example : True := True.intro\n')
            return subprocess.CompletedProcess(command, 0, '')

        output = io.StringIO()
        with redirect_stdout(output), self.assertRaisesRegex(ValueError, 'source changed'):
            run_plan(plan, runner=runner)
        self.assertNotIn('"status": "complete"', output.getvalue())


def lean_smoke(lake):
    """An actual small Lean project checks the +module CLI and final roots."""
    toolchain = Path(__file__).resolve().parents[1] / 'lean-toolchain'
    with tempfile.TemporaryDirectory(prefix='dr-bounded-lean-smoke-') as directory:
        root = Path(directory)
        fixture(root, unused=False)
        (root / 'lean-toolchain').write_text(toolchain.read_text())
        (root / 'lakefile.toml').write_text('name = "boundedBuildSmoke"\n'
            '[[lean_lib]]\nname = "DR"\n[[lean_lib]]\nname = "Test"\n')
        records = run_plan(make_plan(root), lake)
        if records[-1]['phase'] != 'root_check' or any(record['exit_code'] for record in records):
            raise ArithmeticError('Actual Lean smoke did not check both roots')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--smoke', action='store_true')
    parser.add_argument('--lake', default='lake')
    args = parser.parse_args()
    result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(BoundedBuildTests))
    if not result.wasSuccessful():
        raise SystemExit(1)
    if args.smoke:
        lean_smoke(args.lake)
