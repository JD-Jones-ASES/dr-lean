#!/usr/bin/env python3
"""Check bounded coverage shards only after their individual cases have passed.

The case replay log controls scheduling, not mathematical validity: every shard
still imports each literal Lean certificate and is checked by lake --wfail.
"""
import argparse
import json
import subprocess
import time
from pathlib import Path
from generate_finite_k3_envelope import BASE, EXPECTED, SHARDS, load_cases, render_dispatch


def completed_cases(contents):
    """Read a contiguous canonical prefix; ignore only an unfinished last write."""
    lines = contents.splitlines(keepends=True)
    if lines and not lines[-1].endswith('\n'):
        lines.pop()
    completed = []
    for line in lines:
        record = json.loads(line)
        if record.get('status') != 'passed':
            raise ArithmeticError('A case batch did not pass')
        if type(record.get('offset')) is not int or record['offset'] != len(completed):
            raise ArithmeticError('Missing, duplicate or reordered case batch')
        raw = record.get('cases')
        if not isinstance(raw, list) or not raw or any(
            not isinstance(pair, list) or len(pair) != 2 or
            any(type(value) is not int for value in pair) for pair in raw
        ):
            raise ArithmeticError('Malformed case batch')
        batch = tuple(map(tuple, raw))
        if batch != EXPECTED[len(completed):len(completed) + len(batch)]:
            raise ArithmeticError('Case batch differs from canonical coverage')
        completed.extend(batch)
    return tuple(completed)


def ready_shards(completed):
    passed = set(completed)
    return tuple((m, lo, hi) for m, lo, hi in SHARDS
                 if all((m, n) in passed for n in range(lo, hi + 1)))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--replay-log', type=Path,
                        default=BASE / '.verification/finite-k3-envelope-replay.jsonl')
    parser.add_argument('--log', type=Path,
                        default=BASE / '.verification/finite-k3-dispatch-replay.jsonl')
    parser.add_argument('--lake', default='lake')
    parser.add_argument('--follow', action='store_true')
    parser.add_argument('--poll-seconds', type=float, default=15)
    args = parser.parse_args()
    if not 1 <= args.poll_seconds <= 60:
        raise ArithmeticError('Poll interval must be between 1 and 60 seconds')
    if args.log.resolve() == args.replay_log.resolve():
        raise ArithmeticError('Case and dispatch logs must differ')
    load_cases()
    args.log.parent.mkdir(parents=True, exist_ok=True)
    built = set()
    previous_count = -1
    with args.log.open('w') as out:
        while True:
            completed = completed_cases(args.replay_log.read_text())
            if len(completed) < previous_count:
                raise ArithmeticError('Case replay log was truncated during dispatch')
            previous_count = len(completed)
            for m, lo, hi in ready_shards(completed):
                if (m, lo, hi) in built:
                    continue
                module = f'DR.Certificates.FiniteK3Dispatch.M{m}N{lo}To{hi}'
                path = BASE / f'DR/Certificates/FiniteK3Dispatch/M{m}N{lo}To{hi}.lean'
                expected = render_dispatch(m, lo, hi)
                if path.exists() and path.read_text() != expected:
                    raise ArithmeticError(f'Changed generated dispatch shard: {path}')
                if not path.exists():
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text(expected)
                print(json.dumps({'status': 'checking', 'module': module}), flush=True)
                stamp = time.monotonic()
                result = subprocess.run([args.lake, '--wfail', 'build', module], cwd=BASE,
                                        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                record = {'status': 'passed' if result.returncode == 0 else 'failed',
                          'module': module, 'm': m, 'lower': lo, 'upper': hi,
                          'seconds': round(time.monotonic() - stamp, 3), 'output': result.stdout}
                out.write(json.dumps(record) + '\n')
                out.flush()
                print(json.dumps({key: value for key, value in record.items() if key != 'output'}),
                      flush=True)
                if result.returncode:
                    print(result.stdout, flush=True)
                    raise SystemExit(result.returncode)
                built.add((m, lo, hi))
            if len(built) == len(SHARDS):
                print(json.dumps({'status': 'complete', 'shards': len(built),
                                  'cases': len(completed)}), flush=True)
                return
            if not args.follow:
                print(json.dumps({'status': 'ready_prefix_complete', 'shards': len(built),
                                  'cases': len(completed)}), flush=True)
                return
            time.sleep(args.poll_seconds)


if __name__ == '__main__':
    main()
