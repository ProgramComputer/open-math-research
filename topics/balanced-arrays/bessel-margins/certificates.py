"""Prove simple, separated outer balanced-array roots using integer arithmetic."""
from fractions import Fraction as F
import json
from math import factorial


def upper_log(d):
    # log d < ceil(log2 d) log 2 and log 2 < 7/10.
    return F((d-1).bit_length()*7,10)


def averaged_penalty(n,d,e):
    coarse=F(9*e,d)
    if d<=58:return coarse
    m=F(e,n)
    z=F(d,d-58)
    q=1-m*(z-1)
    if q<=0:return coarse
    mgf=F(58*n,d*d)*(z*m/q**2+2*z*z*m*m/q**3)
    return min(coarse,mgf)


def bound(n,d,r,k):
    if not (1<=k<n*r//d and n>=1000 and n<=4*d<=4*n):
        return None
    if not (5*(k-1)>=n and 5*(k+1)<=4*n):return None
    e=n*r-d*k
    if e<d or 100*(e+d)>n*d: return None
    scalar=F(2*d*d*(n-1),(n+e+d-1)*(2*e+d))
    return scalar-144-(averaged_penalty(n,d,e-d)+averaged_penalty(n,d,e+d))-upper_log(d)-F(25,24)-F(50,n)


def terminal(n,d,r):
    degree=n*r//d
    k=degree-1; least=None
    while k>0:
        v=bound(n,d,r,k)
        if v is None or v<=F(11,5):break
        least=v if least is None else min(least,v)
        k-=1
    return dict(n=n,d=d,r=r,degree=degree,outer_simple_roots=degree-k-1,
                first_separating_quota=k+1 if least is not None else None,
                minimum_log_curvature_lower=str(least) if least is not None else None)


if __name__=='__main__':
    assert sum(F(11,5)**j/factorial(j) for j in range(9))>9
    assert sum(F(7,10)**j/factorial(j) for j in range(4))>2
    assert (1-F(1,10000))/F(501,1000)**2>F(199,50)
    assert F(1000,999)**5<F(101,100)
    assert 149-144-F(25,24)-2-F(1,100)>F(3,2)
    for n in (4000,10000,100000,1000000,10000000):
        d=3*n//10; r=d//2
        print(json.dumps(terminal(n,d,r)))
