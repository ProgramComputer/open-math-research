"""Exact pole-star scalar envelopes on bounded aspect intervals."""
from fractions import Fraction as F
from math import isqrt, factorial

GRID = 1 << 80
LIMITS = (25,32,40,50,64,80,92,96,100)

def ceiling(a,b=1):
    return (a+b-1)//b

def scaled_up(f):
    return ceiling(f.numerator*GRID,f.denominator)

def star_bounds(cap):
    c=F(48951,3840000*cap)
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

def distinguished(lower):
    c=F(49*(lower-1),7680*lower)
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
    assert exp_lower(F(153,10))>4062720
    assert F(89,100)*96>47+F(5,2)*F(153,10)
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

def verify_single_pole():
    beta=F(1,160)
    kernel=lambda a:1+beta*(a*a-1)
    assert (2*96-1)*beta*9**2>1-beta
    far=kernel(9)**(-95)/(2*beta*95)
    assert 2*sum(kernel(p)**(-96) for p in (3,5,7,9))+far/9<F(1,50)
    assert 2*sum(p*kernel(p)**(-96) for p in (3,5,7,9))+far<F(1,16)

if __name__=="__main__":
    verify_single_pole()
    verify_block_constants()
    lo=20
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
        cutoff=max(10**6,1000*X,ceiling(20*(X*A)**2,49))
        high=max(high,cutoff)
        print(f"{lo:3}..{X:<3} {A:4} {cutoff:13,}     {mode}")
        lo=X
    assert lo==100
    print(f"Uniform bounded-aspect row cutoff: {high:,}.")
