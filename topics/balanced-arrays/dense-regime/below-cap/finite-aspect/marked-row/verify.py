"""Exact interval certificates for the marked-row comparison. Python standard library."""
from fractions import Fraction as Q
from functools import lru_cache
from math import ceil, factorial
from pathlib import Path
import json
import sys

N, D, R = 10**6, 250000, 127000
UNIT = 2**84
GRID = 10**14
DEPTH = 5
FIRST, GATE_END, LAST = 504159, 505610, 505661
FILE = Path(__file__).with_name("quota-blocks.json")


@lru_cache(maxsize=512)
def saturation(z):
    """Bracket the top truncated binomial atom via weights relative to the cap."""
    a = z.denominator-z.numerator
    b = z.numerator
    assert a>0 and b>0
    lo = hi = total_lo = total_hi = UNIT
    for j in range(R,0,-1):
        num, den = j*a,(D-j+1)*b
        lo = lo*num//den
        hi = (hi*num+den-1)//den
        total_lo += lo
        total_hi += hi
        if num<=den and hi<=4096:
            total_hi += (j-1)*hi
            break
    return Q(UNIT,total_hi), Q(UNIT,total_lo)


def alpha(n,k):
    return Q((D-R)*n,D*(n-k))


@lru_cache(maxsize=2048)
def lower(n,k):
    loss = Q(0)
    for j in reversed(range(DEPTH)):
        p = Q(k-j,n-j)
        z = p/(1-(1-p)*loss)
        loss = Q(int(GRID*alpha(n-j,k-j)*saturation(z)[0]),GRID)
    return loss


def upper(n,k,z):
    p = Q(k,n)
    top = saturation(z)[1]
    assert D*(z-p)>=z*(D-R)*top, (k,z)
    return alpha(n,k)*top


def width_ok(lo,hi):
    assert 0<=lo<=hi<1
    return 4*D*(hi-lo)<1-hi


def exp_bounds(x):
    """Taylor polynomial and geometric remainder for small positive rationals."""
    deg = 34
    total = sum(x**i/factorial(i) for i in range(deg+1))
    return total, total+x**(deg+1)/factorial(deg+1)/(1-x/(deg+2))


def seven_term(k,lo,hi):
    from runpy import run_path
    power=run_path(str(Path(__file__).resolve().parent.parent/'verify.py'))['rounded_power']
    center=Q(k*(k+1),(N-k)*(N-k+1))
    ratios={0:Q(1)}
    for j in range(1,4):
        ratios[j]=ratios[j-1]*Q(N-k-j+1,k+j)
        ratios[-j]=ratios[1-j]*Q(k-j+1,N-k+j)
    def upper_term(j):
        return power(ratios[j]**2*center**j,D//2)[1]
    even=power(ratios[-2]*ratios[2]*(1-hi)/(1-lo),D//2)[0]
    return 1-2*upper_term(1)+2*even-upper_term(-3)-upper_term(3)


def full_check(blocks):
    half=Q(1,2)
    # At a>=1/2 the scalar degree-three lower bound increases.
    assert exp_bounds(3*half)[0]>4
    ideal=1-2/exp_bounds(half)[0]+2/exp_bounds(Q(17,8))[1]-2/exp_bounds(9*half)[0]
    mass=2/exp_bounds(half)[0]+2/exp_bounds(4*half)[0]+2/exp_bounds(9*half)[0]
    assert ideal>Q(3,1000) and mass<Q(151,100)
    assert ideal>mass*(exp_bounds(Q(1,1000))[1]-1)
    # The unrestricted curvature-log error per coordinate at distance <=2.
    t=N//8
    assert 1/Q(2*(t-2)**2)+Q(2,t*(t-2))<Q(162,N*N)
    assert Q(729,N)<Q(1,1000)
    # A single endpoint controls every interior quota through FIRST-1.
    k=FIRST+1
    head=upper(N,k,Q(k+1,N))
    assert width_ok(0,head)
    start=FIRST
    for a,b,z_numerator in blocks:
        assert start==a<=b<=LAST
        high=upper(N,b+2,Q(z_numerator,GRID))
        low=lower(N,a-2)
        if b<=GATE_END:
            assert width_ok(low,high),(a,b)
        else:
            assert a==b and seven_term(a,low,high)>0,(a,b)
        start=b+1
    assert start==LAST+1
    # The earlier independently checked row-switching test covers the last 95.
    replay=Path(__file__).resolve().parent.parent/'upper-edge'/'verify.py'
    from runpy import run_path
    x,gain=run_path(str(replay))['curvature'](N,D,R,N*R//D-95)
    assert x<1 and D*gain/(N-(N*R//D-95)+gain)>Q(11,5)
    assert exp_bounds(Q(11,5))[0]>9
    print(len(blocks),"additional exact quota blocks cover",FIRST,"through",LAST)
    print(LAST+95,"simple negative roots of",N*R//D,";",N*R//D-(LAST+95),"remaining")


def make_blocks():
    # Float arithmetic proposes a tilt. upper() certifies each proposed tilt
    # exactly, and the replay reads only rational witnesses from the file.
    def approximate_mass(z):
        total = w = 1.0
        odds = (1-z)/z
        for j in range(R,0,-1):
            w*=j*odds/(D-j+1)
            total+=w
            if w<1e-16*total:
                break
        return 1/total

    @lru_cache(maxsize=None)
    def trial(k):
        p=k/N
        left,right=p,1.0
        for _ in range(48):
            mid=(left+right)/2
            if D*(mid-p)<(D-R)*mid*approximate_mass(mid):
                left=mid
            else:
                right=mid
        z=ceil(GRID*right)+2
        return z,upper(N,k,Q(z,GRID))

    blocks=[]
    def split(a,b):
        z,hi=trial(b+2)
        if width_ok(lower(N,a-2),hi):
            blocks.append([a,b,z])
        else:
            assert a<b, (a,b)
            mid=(a+b)//2
            split(a,mid)
            split(mid+1,b)
    split(FIRST,GATE_END)
    for k in range(GATE_END+1,LAST+1):
        z,_=trial(k+2)
        blocks.append([k,k,z])
    full_check(blocks)
    FILE.write_text(json.dumps(blocks,separators=(',',':'))+'\n')


if __name__=="__main__":
    if sys.argv[1:]==["--generate"]:
        make_blocks()
    else:
        assert not sys.argv[1:]
        full_check(json.loads(FILE.read_text()))
