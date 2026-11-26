"""Lower-width and hybrid coefficient variant of the front certificate."""
from argparse import ArgumentParser
from math import comb, isqrt
from time import perf_counter

from flint import arb, fmpz_poly

from check import eulerian, ratio, sample, universal, update


def next_rows(k, limit, cycle, width):
    t=fmpz_poly([0,1])
    one=fmpz_poly([1])
    rows={k:cycle[k-1]}
    for n in range(k,limit):
        old=rows[n]
        result=(one+(n-1)*t)*old+t*(one-t)*old.derivative()
        m=n+1-k
        if m>=k:
            result+=comb(n,k-1)*t*cycle[k-1].mul_low(rows[m],width-1)
        rows[n+1]=result.truncate(width)
    return rows


def majorants(coeff,n,h,y):
    central=coeff[h-1]
    inv=1/y
    rest=coeff[h+1]*y*y/central
    if h>1:
        rest+=coeff[h-2]*inv/central
    if h>2:
        q=ratio(n,h-2,-1)*inv
        if not q<1:
            raise ArithmeticError((n,h,"left geometric ratio"))
        rest+=universal(n,h-2)*inv*inv/(central*(1-q))
    if h+2<n-1:
        q=ratio(n,h+3,1)*y
        if not q<1:
            raise ArithmeticError((n,h,"right geometric ratio"))
        rest+=universal(n,h+3)*y*y*y/(central*(1-q))
    return rest,coeff[h]*y/central


def check_pair(n,old,new):
    H=isqrt(49*n)//20
    for h in range(1,H+1):
        u=old[h-1]/old[h]
        v=new[h-1]/new[h]
        if not v<u:
            return h,"scale order"
        left=(u+v)/2
        right=u+(u-v)/2
        el,ml=majorants(old,n,h,left)
        er,mr=majorants(old,n,h,right)
        enl,mnl=majorants(new,n+1,h,left)
        enr,mnr=majorants(new,n+1,h,right)
        if not el+ml<1:
            return h,"old left"
        if not 1+er<mr:
            return h,"old right"
        if not 1+enl<mnl:
            return h,"new left"
        if not 1+enr<mnr:
            return h,"new right"
    if not right<sample(n,H):
        return H,"phase join"
    return None


def run(lo,hi,k0,k1):
    width=isqrt(49*hi)//20+2
    max_n=hi+1
    cyc=eulerian(max_n-1,width)
    rows={n:cyc[n-1] for n in range(max_n//2+1,max_n+1)}
    num=fail=ranks=0
    started=perf_counter()
    # Direct insertions use one polynomial convolution per row and are faster
    # when the cutoff admits many repetitions of the same cycle length.
    switch=2*isqrt(hi)
    first=min(max_n//2,max(switch,min(k1,hi//4))) if switch>=hi//4 else max_n//2
    for k in range(first,k0-1,-1):
        if k>switch:
            update(rows,cyc,max_n,k,width)
        elif k<=min(k1,hi//4):
            rows=next_rows(k,max_n,cyc,width)
        if k>min(k1,hi//4):
            continue
        start=max(lo,4*k)
        old=[arb(c) for c in rows[start]]
        for n in range(start,hi+1):
            new=[arb(c) for c in rows[n+1]]
            err=check_pair(n,old,new)
            old=new
            num+=1
            ranks+=isqrt(49*n)//20
            if err:
                fail+=1
                if fail<=40:
                    print("FAIL",n,k,err,flush=True)
        if k%max(1,hi//100)==0:
            print(f"Through k={k}: {num} pairs, {fail} failures, {perf_counter()-started:.2f}s",flush=True)
    print(f"TOTAL {num} pairs, {ranks} ranks, failures={fail}, {perf_counter()-started:.2f}s",flush=True)
    if fail:
        raise SystemExit(1)


if __name__=="__main__":
    parser=ArgumentParser(description=__doc__)
    parser.add_argument("lo",type=int)
    parser.add_argument("hi",type=int)
    parser.add_argument("--k0",type=int,default=4)
    parser.add_argument("--k1",type=int,default=100000)
    cfg=parser.parse_args()
    if not 250 <= cfg.lo <= cfg.hi or not 4 <= cfg.k0 <= cfg.k1:
        parser.error("require 250 <= lo <= hi and 4 <= k0 <= k1")
    run(cfg.lo,cfg.hi,cfg.k0,cfg.k1)
