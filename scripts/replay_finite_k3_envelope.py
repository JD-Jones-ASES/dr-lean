#!/usr/bin/env python3
"""Replay bounded groups of exact Lean cases, failing on the first bad batch."""
import argparse
import json
import subprocess
import time
from pathlib import Path
from generate_finite_k3_envelope import BASE,EXPECTED,load_cases

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--all',action='store_true')
    parser.add_argument('--case',nargs=2,type=int,action='append',default=[])
    parser.add_argument('--batch-size',type=int,default=2)
    parser.add_argument('--lake',default='lake')
    parser.add_argument('--log',type=Path,default=BASE/'.verification/finite-k3-envelope-replay.jsonl')
    args=parser.parse_args()
    load_cases()
    if args.all and args.case:raise ArithmeticError('Select all cases or an explicit list')
    shapes=EXPECTED if args.all else tuple(map(tuple,args.case))
    if not shapes or len(shapes)!=len(set(shapes))or any(x not in EXPECTED for x in shapes):
        raise ArithmeticError('Empty, duplicate or out-of-envelope replay selection')
    if not 1<=args.batch_size<=16:raise ArithmeticError('Batch size must be between1 and16')
    for m,n in shapes:
        if not (BASE/f'DR/Certificates/FiniteK3Cases/M{m}N{n}.lean').exists():
            raise ArithmeticError(f'Missing generated case {(m,n)}')
    args.log.parent.mkdir(parents=True,exist_ok=True)
    started=time.monotonic()
    with args.log.open('w')as out:
        for offset in range(0,len(shapes),args.batch_size):
            batch=shapes[offset:offset+args.batch_size]
            print(json.dumps({'status':'checking','offset':offset,'total':len(shapes),'cases':batch}),flush=True)
            stamp=time.monotonic()
            result=subprocess.run([args.lake,'--wfail','build',*(f'DR.Certificates.FiniteK3Cases.M{m}N{n}'for m,n in batch)],
                cwd=BASE,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
            record={'status':'passed'if result.returncode==0 else'failed','offset':offset,
                'cases':batch,'seconds':round(time.monotonic()-stamp,3),'output':result.stdout}
            out.write(json.dumps(record)+'\n');out.flush()
            print(json.dumps({k:v for k,v in record.items()if k!='output'}),flush=True)
            if result.returncode:
                print(result.stdout,flush=True)
                raise SystemExit(result.returncode)
        print(json.dumps({'status':'complete','cases':len(shapes),'seconds':round(time.monotonic()-started,3)}),flush=True)

if __name__=='__main__':main()
