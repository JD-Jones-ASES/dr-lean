#!/usr/bin/env python3
"""Check the complete public release sources and optional Lean mutation controls.

Only the Python standard library is required. Defaults target the project
containing this scripts/ file; --project and --source-dir support staged files.
This checks source alignment and ordinary Lean bridges, not independent kernel
replay. Metadata is read and fingerprinted; official YAML schema/profile and
protected-Challenge provenance validation remain separate release gates.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import re
import shutil
import subprocess
import sys

sys.dont_write_bytecode = True
NAMESPACE = 'DittertRybinRelease.'

EXPECTED_SIGNATURES = {'DittertRybinRelease.dittert_unique_maximum': '{n : ℕ} (hn : 0 < n) : ∀ A : Matrix (Fin n) (Fin '
                                               'n) ℝ, (∀ i j, 0 ≤ A i j) → (∑ i, ∑ j, A i j) = (n '
                                               ': ℝ) → (∏ i, ∑ j, A i j) + (∏ j, ∑ i, A i j) - '
                                               'A.permanent ≤ 2 - (n.factorial : ℝ)/(n : ℝ)^n ∧ '
                                               '((∏ i, ∑ j, A i j) + (∏ j, ∑ i, A i j) - '
                                               'A.permanent = 2 - (n.factorial : ℝ)/(n : ℝ)^n ↔ A '
                                               '= fun _ _ => (n : ℝ)⁻¹)',
 'DittertRybinRelease.uniform_maximum_order_two': '{m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) : '
                                                  'UniformMaximizer m n 2',
 'DittertRybinRelease.uniform_maximum_order_three': '{m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) : '
                                                    'UniformMaximizer m n 3',
 'DittertRybinRelease.uniform_maximum_four_rows': '{n : ℕ} (hn : 4 ≤ n) : UniformMaximizer 4 n 4 ∧ '
                                                  'UniformMaximizer n 4 4',
 'DittertRybinRelease.uniform_maximum_five_by_five_order_four': ': UniformMaximizer 5 5 4',
 'DittertRybinRelease.uniform_maximum_twenty_by_twenty_order_four': ': UniformMaximizer 20 20 4',
 'DittertRybinRelease.uniform_maximum_large_boards': '{m n k : ℕ} (hk : 4 ≤ k) (hm : '
                                                     '128*(k-2)*(k.choose 2*((k.choose '
                                                     '2)^2).choose 2 + 1)^2 ≤ m) (hn : '
                                                     '128*(k-2)*(k.choose 2*((k.choose '
                                                     '2)^2).choose 2 + 1)^2 ≤ n) : '
                                                     'UniformMaximizer m n k',
 'DittertRybinRelease.uniform_maximum_large_boards_power': '{m n k : ℕ} (hk : 4 ≤ k) (hm : k^21 ≤ '
                                                           'm) (hn : k^21 ≤ n) : UniformMaximizer '
                                                           'm n k',
 'DittertRybinRelease.uniform_maximum_large_endpoints': '{m n : ℕ} (hm : 10^18 ≤ m) (hmn : m ≤ n) '
                                                        ': UniformMaximizer m n m ∧ '
                                                        'UniformMaximizer n m m',
 'DittertRybinRelease.uniform_maximum_quadratic_endpoint_strip': '{m n : ℕ} (hm : 96 ≤ m) (hn : '
                                                                 '10000*m^2 ≤ n) : '
                                                                 'UniformMaximizer m n m ∧ '
                                                                 'UniformMaximizer n m m',
 'DittertRybinRelease.uniform_maximum_quartic_endpoint_strip': '{m n : ℕ} (hm : 16 ≤ m) (hn : '
                                                               '20000*m^4 ≤ n) : UniformMaximizer '
                                                               'm n m ∧ UniformMaximizer n m m',
 'DittertRybinRelease.uniform_maximum_combined_endpoint_strip': '{m n : ℕ} (hm : 5 ≤ m) (hn : '
                                                                '100000000000*m^2 ≤ n) : '
                                                                'UniformMaximizer m n m ∧ '
                                                                'UniformMaximizer n m m',
 'DittertRybinRelease.uniform_maximum_consecutive_endpoint': '{m : ℕ} (hm : 19 ≤ m) : '
                                                             'UniformMaximizer m (m+1) m ∧ '
                                                             'UniformMaximizer (m+1) m m',
 'DittertRybinRelease.uniform_maximum_short_endpoint': '{m n : ℕ} (hm : 117 ≤ m) (hmn : m ≤ n) (hn '
                                                       ': n ≤ 2*m) : UniformMaximizer m n m ∧ '
                                                       'UniformMaximizer n m m',
 'DittertRybinRelease.uniform_maximum_square_near_endpoint': '{n : ℕ} (hn : 21 ≤ n) : '
                                                             'UniformMaximizer n n (n-1)',
 'DittertRybinRelease.uniform_maximum_arithmetic_endpoint': '{m n : ℕ} (hm : 128 ≤ m) (hmn : m ≤ '
                                                            'n) (hcut : 22*(n : ℝ)*Real.log (m : '
                                                            'ℝ) ≤ (m : ℝ)*((m : ℝ)-1)) : '
                                                            'UniformMaximizer m n m ∧ '
                                                            'UniformMaximizer n m m',
 'DittertRybinRelease.uniform_maximum_double_endpoint': '{m : ℕ} (hm : 80 ≤ m) : UniformMaximizer '
                                                        'm (2*m) m ∧ UniformMaximizer (2*m) m m',
 'DittertRybinRelease.uniform_maximum_lll_endpoint': '{m n : ℕ} (hm : 128 ≤ m) (hmn : m ≤ n) '
                                                     '(hlower : 4096*m^3 ≤ n^2) (hupper : 20*n ≤ '
                                                     'm*(m-1)) : UniformMaximizer m n m ∧ '
                                                     'UniformMaximizer n m m',
 'DittertRybinRelease.uniform_maximum_small_side': '{m n k : ℕ} (hsmall : min m n ≤ 4) (hk : 2 ≤ '
                                                   'k) (hkmn : k ≤ min m n) : UniformMaximizer m n '
                                                   'k',
 'DittertRybinRelease.uniform_maximum_five_by_five': '{k : ℕ} (hk : 2 ≤ k) (hk5 : k ≤ 5) : '
                                                     'UniformMaximizer 5 5 k'}

EXPECTED_DEFINITIONS = '/-- The entire probability simplex of real m-by-n matrices, allowing zero cells. -/\ndef IsProbability {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℝ) : Prop :=\n  (∀ i j, 0 ≤ P i j) ∧ (∑ i, ∑ j, P i j) = 1\n\n/-- The probability that k independent draws have distinct rows or distinct columns.\nThe finite sum ranges over all ordered samples, including repeated cells. -/\nnoncomputable def separationProbability {m n : ℕ}\n    (P : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) : ℝ := by\n  classical\n  exact ∑ s : Fin k → Fin m × Fin n,\n    if Function.Injective (fun t => (s t).1) ∨ Function.Injective (fun t => (s t).2)\n    then ∏ t, P (s t).1 (s t).2 else 0\n\n/-- Uniform success a+b-ab, using falling factorials a=(m)_k/m^k and b=(n)_k/n^k. -/\nnoncomputable def uniformSeparationValue (m n k : ℕ) : ℝ :=\n  let a := (m.descFactorial k : ℝ) / (m : ℝ)^k\n  let b := (n.descFactorial k : ℝ) / (n : ℝ)^k\n  a + b - a*b\n\n/-- The sharp inequality and its unique equality case for every probability matrix.\nNo positive-entry, balance, or support condition is imposed. -/\ndef UniformMaximizer (m n k : ℕ) : Prop :=\n  ∀ P : Matrix (Fin m) (Fin n) ℝ, IsProbability P →\n    separationProbability P k ≤ uniformSeparationValue m n k ∧\n    (separationProbability P k = uniformSeparationValue m n k ↔\n      P = fun _ _ => ((m : ℝ)*n)⁻¹)'

def need(condition, message):
    if not condition:
        raise ValueError(message)


def signatures(source):
    return {NAMESPACE+m.group(1): re.sub(r'\s+', ' ', m.group(2)).strip()
            for m in re.finditer(r'(?m)^theorem (\w+)\b(.*?) := by', source, re.S)}


def checked_file(path, project):
    need(not path.is_symlink(), f'Symlink is not a release source: {path}')
    path.resolve().relative_to(project)
    need(path.is_file(), f'Missing regular release source: {path}')
    data = path.read_bytes()
    need(data and b'\x00' not in data, f'Empty or NUL-containing source: {path}')
    return data.decode('utf-8')


def check_sources(challenge, solution, config, inventory, guard, lean_imports):
    expected = [NAMESPACE+x['declaration'].split('.')[-1] for x in inventory]
    need(expected == list(EXPECTED_SIGNATURES), 'Release inventory differs from reviewed twenty targets')
    need(config['challenge_module'] == 'Challenge' and config['solution_module'] == 'Solution',
         'Public module names changed')
    need(config['theorem_names'] == expected, 'Complete ordered target selection changed')
    ccode = guard.code_without_comments_or_strings(challenge)
    scode = guard.code_without_comments_or_strings(solution)
    c, s = signatures(ccode), signatures(scode)
    need(list(c) == expected and list(s) == expected, 'Both files must contain all twenty targets in order')
    need(c == s == EXPECTED_SIGNATURES, 'A public theorem signature differs from the reviewed release scope')
    cdefs = ccode[ccode.index('def IsProbability'):ccode.index('theorem dittert_unique_maximum')]
    sdefs = scode[scode.index('def IsProbability'):scode.index('private theorem probability_eq')]
    expected_defs = guard.code_without_comments_or_strings(EXPECTED_DEFINITIONS)
    normalize = lambda text: re.sub(r'\s+', ' ', text).strip()
    need(normalize(cdefs) == normalize(sdefs) == normalize(expected_defs),
         'An active fixed public definition differs from its reviewed meaning')
    need(not guard.violations(solution), 'Forbidden proof token in Solution')
    need('Challenge' not in lean_imports(solution), 'Solution imports Challenge')
    imports = lean_imports(challenge)
    need(imports and all(x.startswith('Mathlib.') for x in imports), 'Challenge is not Mathlib-only')
    need(config.get('definition_names', []) == [], 'Unspecified-definition holes are not part of this release')
    need(config['permitted_axioms'] == ['propext','Quot.sound','Classical.choice'], 'Permitted axioms changed')
    need(config.get('enable_nanoda') is True, 'Direct replay must request NanoDa')
    need(set(config) <= {'challenge_module','solution_module','theorem_names',
                         'definition_names','permitted_axioms','enable_nanoda'}, 'Unknown Comparator config key')
    need(len(challenge.splitlines()) <= 300 and len(challenge.encode()) <= 32768,
         'Challenge exceeds recommended statement size')
    return cdefs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument('--source-dir', type=Path, help='Alternative staged public-source directory inside project')
    parser.add_argument('--metadata', default='formalization.yaml', help='Metadata filename inside source directory')
    parser.add_argument('--lake', default=shutil.which('lake') or 'lake')
    parser.add_argument('--lean-controls', action='store_true')
    parser.add_argument('--control-timeout', type=int, default=120)
    args = parser.parse_args()
    checker_bytes = Path(__file__).read_bytes()
    project = args.project.resolve()
    source_dir = project if args.source_dir is None else (project/args.source_dir).resolve()
    source_dir.relative_to(project)
    output = project/'.verification'/'release-checks'
    output.mkdir(parents=True,exist_ok=True)
    files = {'Challenge.lean':source_dir/'Challenge.lean', 'Solution.lean':source_dir/'Solution.lean',
             'comparator.json':source_dir/'comparator.json', 'metadata':source_dir/args.metadata,
             'release-targets.json':project/'release-targets.json',
             'source_guard':project/'scripts'/'check-source.py',
             'import_parser':project/'scripts'/'bounded_project_build.py'}
    sources = {key:checked_file(path,project) for key,path in files.items()}
    challenge,solution = sources['Challenge.lean'],sources['Solution.lean']
    config=json.loads(sources['comparator.json'])
    inventory=json.loads(sources['release-targets.json'])['required_targets']
    spec=importlib.util.spec_from_file_location('dr_source_guard',project/'scripts'/'check-source.py')
    guard=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(guard)
    header_spec=importlib.util.spec_from_file_location('dr_release_import_parser',files['import_parser'])
    header=importlib.util.module_from_spec(header_spec)
    sys.modules[header_spec.name]=header
    header_spec.loader.exec_module(header)
    defs=check_sources(challenge,solution,config,inventory,guard,header.lean_imports)
    checks=['all twenty declarations match the reviewed inventory, configuration and exact signatures',
            'four fixed public definitions match their reviewed meanings in both environments',
            'Solution has no Challenge import or forbidden proof token',
            'Mathlib-only Challenge is below recommended size',
            'direct config requests NanoDa and only standard axioms',
            'metadata exists as an in-project regular UTF-8 source; schema/profile check remains separate']
    for name,bad_challenge,bad_solution,bad_config in [
        ('dropped target',challenge,solution,dict(config,theorem_names=config['theorem_names'][:-1])),
        ('missing final proof',challenge,re.sub(r'/-- Square near-endpoint.*?\n\n','',solution,count=1,flags=re.S),config),
        ('proof placeholder',challenge,solution.replace('  exact DittertRybin.dittert_unique_maximum hn','  sorry',1),config),
        ('Challenge dependency',challenge,'import Challenge\n'+solution,config),
        ('newline Challenge dependency',challenge,'import\nChallenge\n'+solution,config),
        ('newline project statement dependency','import\nDR.Semimatching\n'+challenge,solution,config),
        ('commented proof declarations',challenge,
            solution[:solution.index('/-- Dittert’s')]+'/-\n'+
            solution[solution.index('/-- Dittert’s'):solution.index('end DittertRybinRelease')]+
            '\n-/\nend DittertRybinRelease\n',config),
        ('joint scope change',challenge.replace('(hn : 21 ≤ n)','(hn : 22 ≤ n)'),
                               solution.replace('(hn : 21 ≤ n)','(hn : 22 ≤ n)'),config)]:
        try:
            check_sources(bad_challenge,bad_solution,bad_config,inventory,guard,header.lean_imports)
        except ValueError:
            checks.append('rejected '+name)
        else:
            raise ValueError('Source mutation was accepted: '+name)
    controls=[]
    if args.lean_controls:
        bridges=solution[solution.index('private theorem probability_eq'):solution.index('/-- Dittert’s')]
        base=('import DR.Semimatching\nopen scoped BigOperators\nnamespace DittertRybinRelease\n\n'
              +defs+'\n\n'+bridges+'\nend DittertRybinRelease\n')
        mutations=[('Base',None,None),
            ('AndEvent','Function.Injective (fun t => (s t).1) ∨ Function.Injective (fun t => (s t).2)',
                        'Function.Injective (fun t => (s t).1) ∧ Function.Injective (fun t => (s t).2)'),
            ('PositiveDomain','(∀ i j, 0 ≤ P i j)','(∀ i j, 0 < P i j)'),
            ('WrongValue','a + b - a*b','a + b'),
            ('OneWayEquality','uniformSeparationValue m n k ↔','uniformSeparationValue m n k →')]
        for name,before,after in mutations:
            code=base if before is None else base.replace(before,after,1)
            need(before is None or code!=base,'Mutation not applied: '+name)
            path=output/(name+'.lean')
            path.write_text(code)
            result=subprocess.run([args.lake,'env','lean','-DwarningAsError=true',str(path)],
                                  cwd=project,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,
                                  timeout=args.control_timeout)
            (output/(name+'.log')).write_text(result.stdout)
            if before is None:
                need(result.returncode==0,'Unmodified actual semantic bridges failed')
            else:
                need(result.returncode>0 and 'error:' in result.stdout,'Semantic mutation was not rejected: '+name)
            controls.append({'name':name,'expected':'pass' if before is None else 'type/proof rejection',
                             'exit_code':result.returncode,'source_sha256':hashlib.sha256(code.encode()).hexdigest()})
        checks.append('actual Lean bridges pass and reject four mathematical mutations')
    for key,path in files.items():
        need(path.read_bytes() == sources[key].encode('utf-8'), f'Release input changed during checks: {key}')
    need(Path(__file__).read_bytes() == checker_bytes, 'Release checker changed during execution')
    receipt={'scope':'public source checks and optional ordinary Lean controls; no independent verifier replay',
             'checks':checks,'count':len(checks),'lean_controls':controls,'pending_targets':[],
             'all_target_wrappers_checked':True,'complete_release':False,
             'metadata_schema_profile_validated':False,
             'sha256':{key:hashlib.sha256(value.encode('utf-8')).hexdigest() for key,value in sources.items()},
             'checker_sha256':hashlib.sha256(checker_bytes).hexdigest()}
    receipt_name='controls-receipt.json' if args.lean_controls else 'source-receipt.json'
    (output/receipt_name).write_text(json.dumps(receipt,indent=2)+'\n')
    print(f'Passed {len(checks)} release checks; {len(controls)} Lean controls; all twenty proof wrappers are present.')


if __name__ == '__main__':
    main()
