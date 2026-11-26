"""Independent dominant-monomial exterior certificates for actual consecutive rows."""
from argparse import ArgumentParser
from functools import lru_cache
from math import comb, factorial, isqrt
from time import perf_counter

from flint import arb, ctx, fmpz_poly

ctx.prec = 100
T = fmpz_poly([0, 1])


def eulerian(max_n, width):
    rows = [None, fmpz_poly([1])]
    for n in range(2,max_n+1):
        prev = rows[-1]
        rows.append(fmpz_poly([
            (j+1)*prev[j]+(n-j)*prev[j-1] for j in range(min(n,width))
        ]))
    return rows


def update(rows, cyc, max_n, k, width):
    powers = [fmpz_poly([1])]
    factors = [1]
    fac = factorial(k)
    for h in range(1,max_n//k+1):
        powers.append(powers[-1].mul_low(cyc[k-1],width))
        factors.append(factorial(h*k)//(fac**h*factorial(h)))
    for n in range(max_n,k-1,-1):
        result = rows.get(n,fmpz_poly())
        if n%k==0:
            h = n//k
            result += factors[h]*powers[h].left_shift(h-1)
        for h in range(1,(n-k-1)//k+1):
            result += comb(n,h*k)*factors[h]*powers[h].mul_low(rows[n-h*k],width).left_shift(h)
        rows[n] = result.truncate(width)


@lru_cache(maxsize=200_000)
def sample(n,h):
    pi = arb.pi()
    return (-pi*(pi*(6*h+5)/(6*n)).cot()).exp()


@lru_cache(maxsize=200_000)
def universal(n,p):
    return arb(p)**n


@lru_cache(maxsize=200_000)
def ratio(n,p,step):
    return (arb(p+step)/p)**n


def majorants(coeffs,n,h,y):
    # Normalize all terms by the modulus of the exact monomial at index h.
    # The index p refers to E = t Q, so its coefficient is coeffs[p-1].
    low,high=max(1,h-3),h+4
    left=arb(0)
    right=arb(0)
    c=arb(coeffs[h-1])
    inv=1/y
    if low>1:
        q=ratio(n,low-1,-1)*inv
        if not q < 1:
            raise ArithmeticError((n,h,"left geometric ratio"))
        left=universal(n,low-1)*inv**(h-low+1)/(c*(1-q))
    if high<n-1:
        q=ratio(n,high+1,1)*y
        if not q < 1:
            raise ArithmeticError((n,h,"right geometric ratio"))
        right=universal(n,high+1)*y**(high+1-h)/(c*(1-q))
    power=arb(1)
    for p in range(h-1,low-1,-1):
        power*=inv
        left+=arb(coeffs[p-1])*power/c
    power=y
    for p in range(h+2,min(high,n-1)+1):
        power*=y
        right+=arb(coeffs[p-1])*power/c
    return left+right,arb(coeffs[h])*y/c


def check_pair(n,k,old,new):
    H=isqrt(49*n)//20
    for h in range(1,H+1):
        u=arb(old[h-1])/arb(old[h])
        v=arb(new[h-1])/arb(new[h])
        if not v < u:
            return h,"scale order"
        left=(u+v)/2
        right=u+(u-v)/2
        old_left,old_left_main = majorants(old,n,h,left)
        if not old_left+old_left_main<1:
            return h,"old left"
        old_right,old_right_main = majorants(old,n,h,right)
        if not 1+old_right<old_right_main:
            return h,"old right"
        next_left,next_left_main = majorants(new,n+1,h,left)
        if not 1+next_left<next_left_main:
            return h,"next left"
        next_right,next_right_main = majorants(new,n+1,h,right)
        if not 1+next_right<next_right_main:
            return h,"next right"
        if h==H and not right<sample(n,h):
            return h,"phase join"
    return None


def run(lo,hi,k0,k1):
    width=isqrt(49*hi)//20+4
    max_n=hi+1
    cyc=eulerian(max_n-1,width)
    rows={n:cyc[n-1] for n in range(max_n//2+1,max_n+1)}
    num=fail=rank_total=0
    started=perf_counter()
    for k in range(max_n//2,k0-1,-1):
        update(rows,cyc,max_n,k,width)
        if k>min(k1,hi//4):
            continue
        for n in range(max(lo,4*k),hi+1):
            err=check_pair(n,k,rows[n],rows[n+1])
            num+=1
            rank_total+=isqrt(49*n)//20
            if err:
                fail+=1
                if fail<=40:
                    print("FAIL",n,k,err,flush=True)
        if k%max(1,hi//100)==0:
            print(f"Through k={k}: {num} pairs, {fail} failures, {perf_counter()-started:.2f}s",flush=True)
    print(f"TOTAL {num} pairs, {rank_total} ranks, failures={fail}, {perf_counter()-started:.2f}s",flush=True)
    if fail:
        raise SystemExit(1)


if __name__=="__main__":
    args=ArgumentParser(description=__doc__)
    args.add_argument("lo",type=int)
    args.add_argument("hi",type=int)
    args.add_argument("--k0",type=int,default=4)
    args.add_argument("--k1",type=int,default=100000)
    cfg=args.parse_args()
    run(cfg.lo,cfg.hi,cfg.k0,cfg.k1)
