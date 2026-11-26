"""Exact test for the concavity of u_k=(k+1)(a_{k+1}/a_k)^(1/d)."""
import gzip, json, subprocess, sys
from pathlib import Path
from flint import fmpz

repo=sys.argv[1] if len(sys.argv)>1 else str(Path(__file__).resolve().parents[3])
rev='b99147c5388ff82369904849769d23e071b5cc62'
prefix='topics/balanced-arrays/'
rows={}
for name in ('results/corank-one.jsonl.gz','results/source_range.jsonl','results/degree_reduction.jsonl','results/column-extension-corank-two.jsonl.gz','results/column-extension-cap-two.jsonl.gz','results/column-extension-screen.jsonl.gz','results/column-extension-seven.jsonl.gz','results/linear_tail_ranges.jsonl','finite-residual/records.jsonl.gz'):
    data=subprocess.check_output(['git','-C',repo,'show',rev+':'+prefix+name])
    if name.endswith('.gz'): data=gzip.decompress(data)
    for rec in map(json.loads,data.splitlines()):
        for field,off in [('coefficients',0),('left',0),('right',1)]:
            if field in rec:
                k=rec['n'],rec['r'],rec['d']+off
                a=list(map(int,rec[field]))
                if k in rows: assert a==rows[k]
                rows[k]=a
fail=[];good=undec=0
for (n,r,d),a in sorted(rows.items()):
    if r==d:continue
    # Enclose u_k within one 256-bit dyadic ulp.
    scale=2**256
    u=[int(fmpz((y*((k+1)*scale)**d)//x).root(d)) for k,(x,y) in enumerate(zip(a,a[1:]))]
    for k in range(1,len(u)-1):
        margin=2*u[k]-u[k-1]-u[k+1]
        if margin>2:good+=1
        elif margin < -2:fail.append((n,r,d,k,margin))
        else:undec+=1
print(len(rows),'vectors,',good,'strict concave,',len(fail),'strict violations,',undec,'unresolved')
print('first failures',fail[:18])

assert (len(rows), good, len(fail), undec)==(1659,14570,0,0)
