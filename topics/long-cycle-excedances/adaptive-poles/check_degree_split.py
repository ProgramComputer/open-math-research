"""Exact degree-split scalar comparisons and short-cycle joins."""
from fractions import Fraction as F
from math import factorial

from check_full_powers import GRID, ceiling, scaled_up, star_bounds, test, verify_single_pole

LIMITS = (5,6,7,8,9,10,12,15,20,25,32,40,50,64,80,96,100,125)


def distinguished(lower):
    c=F(lower-1,320*lower)
    P=19
    K=lambda p:1+c*(p*p-1)
    assert 191*c*P**2>1-c
    first_tail=K(P)**(-95)/(190*c)
    first=F(sum(p*scaled_up(K(p)**(-96)) for p in range(1,P+1,2))*2,GRID)+first_tail
    zeroth=F(sum(scaled_up(K(p)**(-96)) for p in range(1,P+1,2))*2,GRID)+first_tail/P
    return zeroth,first

def exp_lower(x,terms=64):
    return sum(x**j/factorial(j) for j in range(terms+1))

def exp_upper(x,terms=32):
    return exp_lower(x,terms)+x**(terms+1)/factorial(terms+1)/(1-x/(terms+2))

def verify_block_constants():
    assert exp_upper(F(1))<3
    assert exp_upper(F(1,4))<F(129,100)
    assert exp_upper(F(154,100))<5
    assert F(229,100)*exp_upper(F(154,100))<11

    # Scalar joins with the separate short-cycle condition, where applicable.
    assert exp_lower(F(153,10))>4408334
    assert exp_lower(F(16))>7500000
    assert exp_lower(F(25))>250000**2
    assert F(89,100)*96>47+F(5,2)*F(153,10)
    assert F(89,100)*100>47+F(5,2)*16
    assert F(89,100)*125>47+F(5,2)*25

def allocation_test(lower,A,constants,short_constants):
    W,W1,U,*_=constants
    V,V1=short_constants
    denominator=F(1,lower*A)
    ys,yl=F(2,A)*U,F(5,A)*U
    if yl>=1:
        return False
    es,el=ys/(1-ys),yl/(1-yl)
    epsilon=1/exp_lower(F(lower-1,8))
    if not epsilon<1:
        raise ArithmeticError
    value=V*es+epsilon*W*el
    ds=V1*es+denominator*(6*(V*W+V1*U)+ys*V)*(1+es)
    dl=W1*el+denominator*(11*(W*W+W1*U)+yl*W)*(1+el)
    derivative=ds+epsilon*dl
    insertion=W*(V+value)*denominator
    return (value+F(1,50))**2 + (derivative+insertion+F(1,16)+F(1,100))**2 < 1

if __name__=="__main__":
    verify_single_pole()
    verify_block_constants()
    lo=4
    high=0
    print(" x interval    A    row cutoff     estimate")
    for X in LIMITS:
        constants=star_bounds(X)
        short=distinguished(lo)
        for A in range(10,2001):
            if test(lo,A,constants) or allocation_test(lo,A,constants,short):
                mode = "full powers" if test(lo,A,constants) else "degree split"
                break
        else:
            raise ArithmeticError((lo,X,"no certified threshold"))
        cutoff=max(10000,1000*X,ceiling(5*(X*A)**2,6))
        high=max(high,cutoff)
        print(f"{lo:3}..{X:<3} {A:4} {cutoff:13,}     {mode}")
        lo=X
    assert lo==125
    print(f"Uniform bounded-aspect row cutoff: {high:,}.")
