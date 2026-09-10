#!/usr/bin/env python3
"""Tiny real Lean handoff in two disposable checkouts; no project cache or API.

Only provenance acquisition is mocked. Actual prefix/suffix CLI, Git binding,
bundle pack/restore, cache hashes, final roots and a fresh axiom audit run.
"""
from contextlib import redirect_stdout
import argparse
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from unittest.mock import patch


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lake-bin', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.unlink(missing_ok=True)
    scripts = Path(__file__).resolve().parent
    log = []
    def run(argv, cwd, env=None):
        result = subprocess.run(argv, cwd=cwd, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log.append({'argv': [str(x) for x in argv], 'output': result.stdout,
                    'exit_code': result.returncode})
        if result.returncode:
            raise RuntimeError('Fixture command failed: ' + repr(argv) + '\n' + result.stdout)
        return result.stdout.strip()
    with tempfile.TemporaryDirectory(prefix='dr-staged-lean-handoff-') as temporary:
        root = Path(temporary)
        producer = root / 'producer'; producer.mkdir()
        source = {
            '.gitignore': '.lake/\n.verification/\n__pycache__/\n',
            'lean-toolchain': 'leanprover/lean4:v4.33.0\n',
            'lakefile.toml': 'name = "stagedBuildSmoke"\nversion = "0.1.0"\n'
                '[[lean_lib]]\nname = "DR"\n[[lean_lib]]\nname = "Test"\n'
                '[[lean_lib]]\nname = "Solution"\n',
            'lake-manifest.json': json.dumps({'version':'1.2.0','packagesDir':'.lake/packages',
                'packages':[],'name':'stagedBuildSmoke','lakeDir':'.lake','fixedToolchain':False})+'\n',
            '.github/workflows/development.yml': 'name: offline staged Lean fixture\n',
            'DR/Base.lean': 'namespace DittertRybin\n'
                'theorem two : (1 : Nat) + 1 = 2 := rfl\nend DittertRybin\n',
            'DR.lean': 'import DR.Base\n',
            'Solution.lean': 'import DR\nnamespace DittertRybinRelease\n'
                'theorem two : (1 : Nat) + 1 = 2 := DittertRybin.two\nend DittertRybinRelease\n',
            'Test/Axioms.lean': 'import DR\nimport Solution\nimport Lean.Util.CollectAxioms\nimport Lean.Elab.Command\n'
                'open Lean Elab Command in\nrun_cmd do\n'
                '  let env ← getEnv\n  let mut count : Nat := 0\n'
                '  for (name, _) in env.constants.toList do\n'
                '    if name.toString.startsWith "DittertRybin." ||\n'
                '        name.toString.startsWith "DittertRybinRelease." then\n'
                '      count := count + 1\n'
                '      for ax in ← collectAxioms name do\n'
                '        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do\n'
                '          logError m!"Unexpected axiom: {name} -> {ax}"\n'
                '  if count == 0 then logError "Empty audit"\n'
                '  logInfo m!"Audited {count} project declarations."\n',
            'Test.lean': 'import Test.Axioms\nexample : (1 : Nat) + 1 = 2 := DittertRybinRelease.two\n',
        }
        for name, contents in source.items():
            path = producer / name; path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(contents)
        for name in ('bounded_project_build.py', 'stage_build_artifact.py'):
            destination = producer / 'scripts' / name; destination.parent.mkdir(exist_ok=True)
            shutil.copy2(scripts / name, destination)
        run(['git','init','-q'], producer)
        run(['git','config','user.name','Staged Lean Fixture'], producer)
        run(['git','config','user.email','stage@example.invalid'], producer)
        run(['git','add','.'], producer)
        run(['git','commit','-qm','tiny actual staged Lean fixture'], producer)
        commit = run(['git','rev-parse','HEAD'], producer)
        environment = {**os.environ, 'PATH':str(args.lake_bin.resolve().parent)+os.pathsep+os.environ['PATH'],
            'GITHUB_SHA':commit,'GITHUB_REPOSITORY':'JD-Jones-ASES/dr-lean',
            'GITHUB_RUN_ID':'750011','GITHUB_RUN_ATTEMPT':'1'}
        command = [sys.executable, 'scripts/bounded_project_build.py', '--check-tracked-coverage',
            '--batch-size','2','--cut','1','--report','.verification/plan.json',
            '--log','.verification/build.jsonl']
        run([*command,'--stage','prefix','--stage-receipt','.verification/prefix.json'], producer, environment)
        prefix = json.loads((producer/'.verification/prefix.json').read_text())
        if prefix['status'] != 'partial_stage_passed' or prefix['build_complete']:
            raise ArithmeticError('Fixture prefix falsely claims completion')
        bundle = root / 'prefix-bundle'
        run([sys.executable,'scripts/stage_build_artifact.py','pack','--project','.',
            '--cut','1','--receipt','.verification/prefix.json','--ledger','.verification/build.jsonl',
            '--plan','.verification/plan.json','--output',str(bundle)], producer, environment)
        consumer = root / 'consumer'
        run(['git','clone','--quiet','--no-local','--no-hardlinks',str(producer),str(consumer)], root)
        (consumer/'.lake').mkdir()
        spec = importlib.util.spec_from_file_location('smoke_stage_artifact',consumer/'scripts/stage_build_artifact.py')
        artifact = importlib.util.module_from_spec(spec); sys.modules[spec.name] = artifact
        spec.loader.exec_module(artifact)
        restored = consumer / '.verification/restored-prefix'
        provenance = {'repository':environment['GITHUB_REPOSITORY'],'run_id':750011,'run_attempt':1,
                      'commit':commit,'prefix_job':1,'artifact_id':1}
        with patch.dict(os.environ,environment,clear=True), redirect_stdout(io.StringIO()):
            artifact.restore_bundle(consumer,bundle,prefix['context'],restored,provenance)
        names = [name for batch in prefix['context']['plan']['batches'][:1] for name in batch]
        before = {}
        for name in names:
            path = consumer/'.lake/build/lib/lean'/Path(name.replace('.','/')+'.olean')
            before[name] = (path.stat().st_mtime_ns, hashlib.sha256(path.read_bytes()).hexdigest())
        run([*command,'--stage','final','--prior-stage-dir','.verification/restored-prefix',
             '--stage-receipt','.verification/complete.json'], consumer, environment)
        final = json.loads((consumer/'.verification/complete.json').read_text())
        after = {}
        for name in names:
            path = consumer/'.lake/build/lib/lean'/Path(name.replace('.','/')+'.olean')
            after[name] = (path.stat().st_mtime_ns, hashlib.sha256(path.read_bytes()).hexdigest())
        if before != after:
            raise ArithmeticError('Real suffix rebuilt or changed the restored prefix cache')
        if final['status'] != 'complete_build' or not final['build_complete'] or final['release_verified']:
            raise ArithmeticError('Fixture final receipt has wrong coverage/release status')
        audit = run(['lake','env','lean','Test/Axioms.lean'], consumer, environment)
        if 'Audited 2 project declarations.' not in audit:
            raise ArithmeticError('Fresh actual fixture axiom audit did not cover both declarations')
        if run(['git','status','--porcelain=v1','--untracked-files=all'],consumer):
            raise ArithmeticError('Fixture source tree changed')
        result = {'status':'passed','scope':'tiny actual Lean handoff with mocked provenance only',
                  'platform':prefix['context']['platform'],'toolchain':prefix['context']['toolchain'],
                  'fixture_commit':commit,'modules':final['context']['plan']['project_module_count'],
                  'batches':final['context']['plan']['batch_count'],'cut':1,
                  'tested_helpers':{name:hashlib.sha256((producer/'scripts'/name).read_bytes()).hexdigest()
                      for name in ('bounded_project_build.py','stage_build_artifact.py')},
                  'prefix_cache_reused':True,'fresh_axiom_audit':True,
                  'real_github_api':False,'real_project_cache_touched':False,
                  'independent_kernel_replay':False,'commands':log}
        args.output.write_text(json.dumps(result,indent=2)+'\n')
        print('Tiny actual Lean handoff passed: two fresh checkouts, prefix reused, full roots and fresh audit.')


if __name__ == '__main__':
    main()
