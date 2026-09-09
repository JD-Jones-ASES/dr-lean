#!/usr/bin/env python3
"""Split all 224 exact square-order-four role/coefficient gates into serial modules.

This changes proof scheduling only. All 448 statements, kernel reductions and
the two universal dispatch theorems are retained with their original names.
"""
from pathlib import Path
import argparse

ROOT=Path(__file__).resolve().parent.parent
PREFIX='DR.Square.OrderFourSexticChecks'
COUNT=224
SIZE=16


def render():
    outputs={}
    names=[]
    header='\nnamespace DittertRybin\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 128000000\nset_option Elab.async false\n\n'
    for start in range(0,COUNT,SIZE):
        end=min(COUNT,start+SIZE)
        name=f'{PREFIX}.Rows{start:03d}To{end-1:03d}'
        names.append(name)
        body='import DR.Square.OrderFourPolynomialSexticRoles\n'+header
        for i in range(start,end):
            body+=f'theorem orderFourSexticEntryKey_{i} : orderFourSexticEntryKeyValid {i} := by decide +kernel\n\n'
            body+=f'theorem orderFourSexticTableCoefficient_{i} : orderFourSexticTableCoefficient {i} =\n    orderFourSexticExpectedCoefficient {i} := by decide +kernel\n\n'
        outputs[Path(*name.split('.')).with_suffix('.lean')]=body+'end DittertRybin\n'
    body=''.join(f'import {name}\n' for name in names)+header
    body+='theorem orderFourSexticEntryKey (s : Fin 224) : orderFourSexticEntryKeyValid s := by\n  fin_cases s\n'
    body+=''.join(f'  · exact orderFourSexticEntryKey_{i}\n' for i in range(COUNT))
    body+='\ntheorem orderFourSexticTableCoefficient_eq_expected (s : Fin 224) :\n    orderFourSexticTableCoefficient s = orderFourSexticExpectedCoefficient s := by\n  fin_cases s\n'
    body+=''.join(f'  · exact orderFourSexticTableCoefficient_{i}\n' for i in range(COUNT))
    outputs[Path('DR/Square/OrderFourPolynomialSexticRolesCheck.lean')]=body+'\nend DittertRybin\n'
    return outputs


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    outputs=render()
    for rel,text in outputs.items():
        path=ROOT/rel
        if args.check:
            if not path.is_file() or path.read_text()!=text:raise SystemExit('Generated proof differs: '+str(rel))
        else:
            path.parent.mkdir(parents=True,exist_ok=True)
            path.write_text(text)
    print(f'PASS: {len(outputs)-1} serialized chunks, {2*COUNT} literal gates, two complete dispatchers')

if __name__=='__main__':main()
