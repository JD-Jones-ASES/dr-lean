#!/usr/bin/env python3
"""Combine the exact finite K3 dispatch intervals without changing coverage."""
import argparse
from pathlib import Path
from generate_finite_k3_envelope import RANGES, SHARDS

ROOT=Path(__file__).resolve().parents[1]


def render():
    outputs={}
    for m,lower,upper in RANGES:
        pieces=[(lo,hi) for mm,lo,hi in SHARDS if mm==m]
        if [n for lo,hi in pieces for n in range(lo,hi+1)]!=list(range(lower,upper+1)):
            raise ArithmeticError('Dispatch does not cover the exact finite strip')
        lines=[f'import DR.Certificates.FiniteK3Dispatch.M{m}N{lo}To{hi}' for lo,hi in pieces]
        lines += ['import DR.Certificates.FiniteK3EnvelopeSoundness','',
            '/-! Generated exact finite-strip assembly; every referenced certificate is required. -/',
            'namespace DittertRybin','',
            f'theorem uniformMaximizer_orderThree_finite_{m} {{n : ℕ}}',
            f'    (hlo : {lower} ≤ n) (hhi : n ≤ {upper}) : UniformMaximizer {m} n 3 := by']
        for lo,hi in pieces[:-1]:
            lines += [f'  by_cases h{hi} : n ≤ {hi}',
                f'  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C{m}N{lo}To{hi}.exists_valid n (by omega) h{hi}',
                '    exact hv.uniformMaximizer (by omega)']
        lo,hi=pieces[-1]
        lines += [f'  obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C{m}N{lo}To{hi}.exists_valid n (by omega) hhi',
            '  exact hv.uniformMaximizer (by omega)','','end DittertRybin','']
        outputs[ROOT/f'DR/Rectangular/OrderThreeFinite{m}.lean']='\n'.join(lines)
    return outputs


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    for path,text in render().items():
        if args.check:
            if not path.is_file() or path.read_text()!=text:
                raise SystemExit(f'Finite strip differs: {path.relative_to(ROOT)}')
        else:
            path.write_text(text)
    print('Checked six exact finite strips' if args.check else 'Generated six exact finite strips')


if __name__=='__main__':
    main()
