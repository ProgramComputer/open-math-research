"""Independent nine-slab carrier check with direct powers of the binned polynomial."""
from fractions import Fraction as R
from math import ceil, factorial, isqrt
from pathlib import Path
import runpy

previous = runpy.run_path(str(Path(__file__).with_name("independent-check.py")))
G, U, P, SLABS, ODD = (previous[key] for key in ("G", "U", "P", "SLABS", "ODD"))
lattice, all_terms, e = (previous[key] for key in ("lattice", "all_terms", "e"))

def exp_upper(x, n=160):
    """Positive Maclaurin prefix plus a geometric bound on the remaining terms."""
    assert 0 <= x < n+2
    term = total = R(1)
    for j in range(1,n+1):
        term *= x/j
        total += term
    return total + term*x/(n+1)/(1-x/(n+2))


def verify_tail():
    weight = R(9,8)
    t = weight**4
    assert exp_upper(R(1)) < R(11,4)
    assert t+R(51,100)*t*(exp_upper(t)-1) < 7
    # Lower shape argument valid for every occupied primitive, every slab.
    c_min = (1-R(1,208))*U/(192*48)
    assert lattice(c_min)[2] < 4
    assert R(7)*4/(R(9,4)) < 14
    assert R(8,7)*exp_upper(R(14))*weight**-240 < R(1,10000)


def principal_star(c):
    # Distinguish +1. For the omitted signed poles, |a-1| >= 2.
    finite = sum((1+c*(a*a-1))**-96/abs(a-1) for a in ODD if a!=1)
    first_tail = (1+c*(P*P-1))**-95/(190*c)
    return finite + first_tail/(2*P)


def bound_unified(lo, X):
    K = 10000//X
    A0 = R(isqrt(192000)//X,4)
    assert K >= 208 and A0 >= R(9,4) and A0**2*X**2<=12000
    c = (1-R(1,K))*U/(192*X)
    eta = R(ceil(G*R(K,K-1)*principal_star(c)/A0),G)
    assert eta < R(81,100)
    carrier = R(12,11)/exp_upper(eta,48)
    coeff, multi = all_terms(240,K,X,A0)
    principal = R(1,10000)
    nonprincipal = regular = R(0)
    star = lattice((R(lo-1)-R(1,K))*U/(192*X))[2]
    singleton_jump = lattice(U/(192*X))[0]*star/(2*factorial(lo-1)*A0**2)
    multiple_jump = R(0)
    for b, q in enumerate(coeff):
        h = R(b,4)
        g = max(1,R(b,5)) if b else R(0)
        principal += 2*e(lo-h)*q
        mass, moment, _ = lattice(max(R(1,X),1-h/lo)*U/192)
        if g+1<=X and b<=5*X:
            nonprincipal += (R(4,7) if lo-h>=2 else 1)*moment*q
        if g+1<=X+R(1,K) and b<5*X:
            v = R(1) if lo-h<=2 else R(1,2*factorial(ceil(lo-h)-1))
            regular += v*mass*q/A0
            if h>lo-1:
                multiple_jump += A0*X*mass*multi[b]/U
    margin = carrier-principal-nonprincipal-regular-singleton_jump-multiple_jump
    assert margin > R(322338,10**6), (lo,X)
    return tuple(int(x*10**6) for x in
        (eta,carrier,principal,nonprincipal,regular,singleton_jump,multiple_jump,margin))


if __name__=='__main__':
    verify_tail()
    print('l  X   eta carrier principal nonprincipal regular atom-one atom-many margin (floors at 1e-6)')
    for lo,X in SLABS:
        print(lo,X,*bound_unified(lo,X),flush=True)
