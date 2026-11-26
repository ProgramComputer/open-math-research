"""Independent positive coefficient recurrence and exterior-disk replay."""
from functools import lru_cache
from math import comb,isqrt
from flint import arb, ctx, fmpz_poly
ctx.prec=112

@lru_cache(None)
def eulerian(j,size):
    # A(j,r) = sum (-1)^i binom(j+1,i) (r+1-i)^j by extracting t^(r+1)
    # from (1-t)^(j+1) sum_{a>=1} a^j t^a.
    return fmpz_poly([sum((-1)**i*comb(j+1,i)*(r+1-i)**j for i in range(r+1))
                      for r in range(min(j,size))])

@lru_cache(None)
def entrance(n,H):
    return (-arb.pi()*(arb.pi()*(6*H+5)/(6*n)).cot()).exp()

@lru_cache(maxsize=100000)
def universal(n,p):
    return arb(p)**n

def remainder(y,n,h,row):
    c=row[h-1]
    lo=max(h-2,1); hi=h+3
    value=arb(0)
    for p in range(lo,hi+1):
        if p not in (h,h+1):
            value+=row[p-1]*y**(p-h)/c
    p=lo-1
    if p:
        ratio=universal(n,p-1)/(universal(n,p)*y)
        assert ratio<1
        value+=universal(n,p)*y**(p-h)/(c*(1-ratio))
    p=hi+1
    ratio=universal(n,p+1)*y/universal(n,p)
    assert ratio<1
    return value+universal(n,p)*y**(p-h)/(c*(1-ratio))

def pair(n,old,new):
    H=isqrt(49*n)//20
    for h in range(1,H+1):
        u=old[h-1]/old[h];v=new[h-1]/new[h]
        assert 0<v and v<u
        inner=u-(u-v)*2/5; outer=u+(u-v)*2/5
        for y,old_sign in [(inner,1),(outer,-1)]:
            assert old_sign*(1-y/u)>remainder(y,n,h,old)
            assert y/v-1>remainder(y,n+1,h,new)
    assert outer<entrance(n,H)
    return H

def main():
    hi=1000;size=isqrt(49*hi)//20+3
    tested=ranks=0
    for k in range(4,hi//4+1):
        cycle=eulerian(k-1,size)
        ring=[None]*k
        old=cycle;ring[0]=old
        for n in range(k,hi+1):
            m=n+1-k
            lag=fmpz_poly()
            if m>=k:lag=cycle.mul_low(ring[m%k],size-1)*comb(n,k-1)
            new=fmpz_poly([(j+1)*old[j]+((n-j)*old[j-1]+lag[j-1] if j else 0)
                           for j in range(size)])
            if n>=max(251,4*k):
                tested+=1
                ranks+=pair(n,[arb(c) for c in old],[arb(c) for c in new])
            ring[(n+1)%k]=new
            old=new
    assert (tested,ranks)==(114750,991894)
    print(tested,'old/new pairs,',ranks,'one-sided exterior ranks, all dominance and phase joins pass')
if __name__=='__main__':
    if not __debug__:raise SystemExit('Run without -O.')
    main()
