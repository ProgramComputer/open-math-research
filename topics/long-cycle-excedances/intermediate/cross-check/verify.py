"""Independent finite signs by separating the old and new zeros using point values."""
from argparse import ArgumentParser
from functools import cache
from math import comb, isqrt
from time import monotonic

from flint import arb, arb_poly, ctx, fmpz_poly

ctx.prec = 160
WIDTH = 60
X = fmpz_poly([0, 1])
ONE = fmpz_poly([1])

@cache
def single_cycle(length):
    m = length - 1
    return fmpz_poly([sum((-1)**j * comb(m+1, j) * (i+1-j)**m
                          for j in range(i+1))
                      for i in range(min(m, WIDTH))])

def reduced_rows(k, limit):
    """Insertion of the largest label, with the cycle of exact length k as the correction."""
    a = single_cycle(k)
    ring = [None]*k
    ring[0] = a
    cur = a
    for n in range(k, limit+1):
        diff = cur.derivative()
        nxt = cur + X*(diff + (n-1)*cur - X*diff)
        m = n+1-k
        if m >= k:
            nxt += X * (comb(n,k-1)*a.mul_low(ring[m%k], WIDTH-1))
        nxt = nxt.truncate(WIDTH)
        yield n,cur,nxt
        ring[(n+1)%k] = nxt
        cur = nxt

def signed_polynomial(row):
    return arb_poly([row[i] if i%2 == 0 else -row[i] for i in range(min(row.length(),WIDTH))])

@cache
def phase(n,j):
    th = arb.pi()*j/n
    return th.sin(), (-arb.pi() / th.tan()).exp()

@cache
def horizontal(n,j,A,k):
    # Check BOTH entrance inequalities with outward rounding.
    s = phase(n,j)[0]
    return k*s >= A and 5*n*s*s >= 6

@cache
def tail(n,Bn,j):
    B = phase(Bn,j)[1].upper()
    ratio = B * (arb(WIDTH+2)/(WIDTH+1))**n
    assert ratio < 1
    return (arb(WIDTH+1)**n*B**WIDTH / (1-ratio)).upper()

def signs(poly, y, direction, remainder):
    return direction*poly(y) > remainder

def pair(n,k,f,g):
    h = isqrt(49*n)//20
    a = 7 if 2*n <= 15*k else 5 if n<=10*k or k<=100 else 6
    first = h+1
    gap = first
    while not horizontal(n,gap,a,k):
        assert 2*(gap+1) <= n
        left = phase(n,gap)[1].upper()
        right = phase(n,gap+1)[1].lower()
        e = tail(n,n,gap+1)
        e1 = tail(n+1,n,gap+1)
        d = (-1)**(gap-1)
        assert left < right and signs(f,left,d,e) and signs(f,right,-d,e),(n,k,gap,'old angular endpoints')
        # Both signs of g at *point* endpoints suffice: adjacent brackets then
        # force different new roots in the intervening complementary gaps.
        for step in range(72):
            if signs(g,left,-d,e1) and signs(g,right,-d,e1):
                break
            for numerator,denominator in [(1,2),(3,8),(5,8)]:
                cut = ((left*(denominator-numerator)+right*numerator)/denominator).mid()
                if signs(f,cut,d,e):
                    left = cut
                    break
                if signs(f,cut,-d,e):
                    right = cut
                    break
            else:
                raise ArithmeticError((n,k,gap,'old split'))
        else:
            raise ArithmeticError((n,k,gap,'separating points'))
        gap += 1
    return gap-first,gap

def main(lo,hi,start,end):
    pairs = gaps = witnessed = highest = 0
    begin = monotonic()
    for k in range(start,end+1):
        bottom,top = max(4*k,lo),min(20*k-1,hi)
        if bottom>top:
            continue
        partial = counted = 0
        running = None
        for n,old,new in reduced_rows(k,top):
            if n<bottom: continue
            if running is None: running = signed_polynomial(old)
            after = signed_polynomial(new)
            count,entrance = pair(n,k,running,after)
            running = after
            partial += count
            counted += 1
            witnessed += int(count>0)
            highest = max(highest,entrance)
        pairs += counted
        gaps += partial
        print(k, counted, partial,flush=True)
    print('TOTAL',pairs,gaps,witnessed,highest,round(monotonic()-begin,2),flush=True)
    if (lo,hi,start,end)==(251,1000,7,250):
        assert (pairs,gaps,highest)==(93902,541199,33)

if __name__=='__main__':
    ap = ArgumentParser()
    ap.add_argument('--nmin',type=int,default=251)
    ap.add_argument('--nmax',type=int,default=1000)
    ap.add_argument('--kmin',type=int,default=7)
    ap.add_argument('--kmax',type=int,default=250)
    args = ap.parse_args()
    if not __debug__: raise SystemExit('Use Python with assertions enabled.')
    main(args.nmin,args.nmax,args.kmin,args.kmax)
