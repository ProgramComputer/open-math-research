"""Exact pole-star scalar envelopes on bounded aspect intervals."""
from fractions import Fraction as F
from math import isqrt

GRID = 1 << 80
LIMITS = (5,6,7,8,9,10,12,15,20,25,32,40,50,64,80,100,125)

def ceiling(a,b=1):
    return (a+b-1)//b

def scaled_up(f):
    return ceiling(f.numerator*GRID,f.denominator)

def star_bounds(cap):
    c=F(999,160000*cap)
    limit=2*isqrt(9*cap)+3
    ex=96
    assert (2*ex-1)*c*limit**2 > 1-c
    kernel=lambda p:1+c*(p*p-1)
    tail=kernel(limit)**(1-ex)/(2*c*(ex-1))
    w1_tail=scaled_up(tail)
    w_tail=ceiling(w1_tail,limit)
    p=tuple(range(-limit,limit+1,2))
    w={a:scaled_up(kernel(a)**(-ex)) for a in p}
    W=sum(w.values())+w_tail
    W1=sum(abs(a)*w[a] for a in p)+w1_tail
    U=max(sum(ceiling(w[b],abs(b-a)) for b in p if b!=a)
          for a in (*p,limit+2))
    U+=ceiling(w_tail,2)
    T=E=J=0
    for a in p:
        for b in p:
            if a==b:
                continue
            den=abs(a-b)
            pair=ceiling(w[a]*w[b],den)
            T+=pair
            E+=max(abs(a),abs(b))*pair
            J+=abs(b)*pair
    T+=w_tail*W
    weighted_tail=w1_tail*W+w_tail*W1
    E+=weighted_tail
    J+=weighted_tail
    return F(W,GRID),F(W1,GRID),F(U,GRID),F(T,GRID**2),F(E,GRID**2),F(J,GRID**2)

def test(lower,A,constants):
    W,W1,U,T,E,J=constants
    a=F(2,A)
    y=a*U
    if y>=1:
        return False
    tail1=y/(1-y)
    tail2=y*y/(2*(1-y))
    value=a*T+W*tail2
    denom=F(1,lower*A)
    derivative=a*(E+T*denom)+W1*tail2+a*(J+T*denom)*tail1
    insertion=W*(W+value)*denom
    return (value+F(1,50))**2 + (derivative+insertion+F(1,16)+F(1,100))**2 < 1

def verify_single_pole():
    beta=F(1,160)
    kernel=lambda a:1+beta*(a*a-1)
    assert (2*96-1)*beta*9**2>1-beta
    far=kernel(9)**(-95)/(2*beta*95)
    assert 2*sum(kernel(p)**(-96) for p in (3,5,7,9))+far/9<F(1,50)
    assert 2*sum(p*kernel(p)**(-96) for p in (3,5,7,9))+far<F(1,16)

if __name__=="__main__":
    verify_single_pole()
    lo=4
    high=0
    print(" x interval    A    row cutoff")
    for X in LIMITS:
        constants=star_bounds(X)
        for A in range(10,2001):
            if test(lo,A,constants):
                break
        else:
            raise ArithmeticError((lo,X,"no certified threshold"))
        cutoff=max(10000,1000*X,ceiling(5*(X*A)**2,6))
        high=max(high,cutoff)
        print(f"{lo:3}..{X:<3} {A:4} {cutoff:13,}")
        lo=X
    assert lo==125
    print(f"Uniform bounded-aspect row cutoff: {high:,}.")
