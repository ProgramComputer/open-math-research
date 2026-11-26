"""Exact binomial-basis coefficient tests for straight Toeplitz minors."""
import argparse
from collections import defaultdict
from functools import lru_cache
import gzip
import io
import json
from math import comb
from pathlib import Path
from flint import fmpz_mat

def partitions(n, hi=None):
    if not n:
        yield ()
        return
    for j in range(min(n,hi or n),0,-1):
        for rest in partitions(n-j,j): yield (j,)+rest

def support_counts(d,r,k):
    """Count arrays on s labeled rows of which every row is nonempty."""
    if not k: return [1]
    @lru_cache(None)
    def moves(h):
        dest=list(h)
        out={}
        def visit(j,left,w,used):
            if j==k:
                if used:out[tuple(dest)]=w
                return
            for b in range(min(h[j],left)+1):
                dest[j]-=b;dest[j+1]+=b
                visit(j+1,left-b,w*comb(h[j],b),used+b)
                dest[j]+=b;dest[j+1]-=b
        visit(0,r,1,0)
        return out
    source={(d,)+(0,)*k:1}
    full=(0,)*k+(d,)
    result=[0]
    for s in range(1,d*k+1):
        after=defaultdict(int)
        for h,a in source.items():
            for z,m in moves(h).items(): after[z]+=m*a
        source=after
        result.append(source.get(full,0))
    return result

def check(d,r,weight,output):
    bound=d*weight
    coeff=[support_counts(d,r,k) for k in range(weight+1)]
    values=[[sum(comb(n,s)*v for s,v in enumerate(c) if s<=n) for c in coeff] for n in range(bound+1)]
    ncases=bad=0;badpart=None
    for ell in range(1,weight+1):
        for lam in partitions(ell):
            order=len(lam)
            indices=[[s-i+j for j in range(order)] for i,s in enumerate(lam)]
            vals=[int(fmpz_mat([[values[n][idx] if idx>=0 else 0 for idx in row] for row in indices]).det()) for n in range(d*ell+1)]
            bc=[]
            while vals:
                bc.append(vals[0])
                vals=[t-s for s,t in zip(vals,vals[1:])]
            neg=[j for j,c in enumerate(bc) if c<0]
            row=dict(d=d,r=r,partition=lam,binomial_coefficients=bc,negative_indices=neg)
            output.write(json.dumps(row,separators=(',',':'))+'\n')
            ncases+=1
            if neg:
                bad+=1
                if badpart is None:badpart=(lam,neg[0],bc[neg[0]])
    return ncases,bad,badpart

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("d", type=int)
    parser.add_argument("r", type=int)
    parser.add_argument("weight", type=int)
    parser.add_argument("--write", action="store_true", help="regenerate the archive")
    args = parser.parse_args()
    archive = Path(__file__).with_name(
        f"binomial-schur-{args.d}-{args.r}-{args.weight}.jsonl.gz"
    )
    output = io.StringIO()
    count, bad, first = check(args.d, args.r, args.weight, output)
    if args.write:
        with gzip.open(archive, "wt", encoding="utf-8") as target:
            target.write(output.getvalue())
    else:
        with gzip.open(archive, "rt", encoding="utf-8") as source:
            if source.read() != output.getvalue():
                raise SystemExit(f"Archive differs: {archive.name}")
    print(f"{count} partition polynomials, {bad} with negative binomial coefficients")
    if first is not None:
        print(f"First failure: {first}")
        raise SystemExit(1)


if __name__ == "__main__":
    main()
