"""Make a Lean file with literal records and independently constructed expected keys."""
import argparse
import sys
from pathlib import Path
from metadata import expected, verify


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('ledger',type=Path)
    p.add_argument('--nmin',type=int,required=True)
    p.add_argument('--nmax',type=int,required=True)
    p.add_argument('--kmin',type=int,required=True)
    p.add_argument('--kmax',type=int,required=True)
    a=p.parse_args()
    bounds=a.nmin,a.nmax,a.kmin,a.kmax
    with a.ledger.open('rb') as f:
        verify(f,*bounds)
    stats=dict(pairs=0,witnessed_pairs=0,highest_entrance=0)
    keys=[f'  ({k}, {n}, {rank})' for n,k,rank in expected(*bounds,stats)]
    rows=[]
    for line in a.ledger.read_text().splitlines():
        n,k,rank,x,xb,y,yb=map(int,line.split(','))
        rows.append(f'  ⟨{n}, {k}, {rank}, ⟨{x}, {xb}⟩, ⟨{y}, {yb}⟩⟩')
    sys.stdout.write((Path(__file__).parent/'WitnessLedger.lean').read_text())
    print('\nopen WitnessLedger\nset_option maxRecDepth 4000\nset_option maxHeartbeats 0')
    print('def expectedKeys : List (ℕ × ℕ × ℕ) := [\n'+',\n'.join(keys)+'\n]')
    print('def checkedRows : List Gap := [\n'+',\n'.join(rows)+'\n]')
    print('theorem checkedShard : check expectedKeys checkedRows = true := by decide')
    print('#print axioms checkedShard')
