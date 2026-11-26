"""Independent exact scalar replay for the x >= 44 Fourier comparison."""
from fractions import Fraction as Q
from functools import cache
from math import isqrt


def atan_bounds(x):
    terms = [(-1)**j*x**(2*j+1)/(2*j+1) for j in range(18)]
    lo = sum(terms)
    return lo, lo+x**37/37


pl, pu = atan_bounds(Q(1,5))
ql, qu = atan_bounds(Q(1,239))
P, R = 16*pl-4*qu, 16*pu-4*ql


@cache
def exp_unit(z):
    assert 0 <= z <= 1
    term = total = Q(1)
    for i in range(1,31):
        term *= z/i
        total += term
    return total,total+term*z/31*Q(32,31)


@cache
def exp(x):
    x = Q(x)
    if x < 0:
        low, high = exp(-x)
        return 1/high, 1/low
    n = x.numerator//x.denominator
    lo, hi = exp_unit(x-n)
    elo, ehi = exp_unit(Q(1))
    return lo*elo**n, hi*ehi**n


def log(x):
    if x > 2:
        a,b = log(x/2)
        c,d = log(Q(2))
        return a+c,b+d
    assert x >= 1
    z = (x-1)/(x+1)
    lo = 2*sum(z**(2*j+1)/(2*j+1) for j in range(100))
    return lo, lo + 2*z**201/(201*(1-z*z))


def sqrt_floor(x):
    scale = 10**12
    return Q(isqrt((x*scale**2).__floor__()),scale)


def outer_join():
    theta = Q(9,25)*R/100
    assert theta<Q(3,250)
    assert Q(7,20)*100-Q(1,6)>Q(17,50)*100
    assert (Q(17,50)*P*(1-theta*theta/6))**2>1
    assert (1-theta*theta/2)/Q(9,25)>2
    assert Q(48,100)+theta<P/6
    assert 1/(3*Q(9,25)**2)>log(Q(459,40))[1]
    assert 4*44>10**2


def positive_odd_tail(d, phase):
    # Direct first four values and integral from the last retained odd index.
    a = d-phase/4
    result = sum(j*exp(-d*(j*j-1)+phase*(j+1))[1] for j in (3,5,7,9))
    result += exp(-a*(9*9-1))[1]/(4*a)
    return result


def pole_tails():
    for d,p,target in [
        (Q(49,100),Q(42,100),Q(33,100)),
        (Q(44,100),Q(2,100),Q(11,100)),
        (Q(44,10),Q(2),Q(11,100)),
        (Q(11,10),Q(82,100),Q(11,100)),
    ]:
        assert positive_odd_tail(d,p)<target
    assert R*exp(Q(563,500))[1]*Q(21,20)/sqrt_floor(2*P*99)<Q(42,100)
    for k in range(10,100):
        H_bound = R*exp(Q(57,50))[1]*(1/(6*sqrt_floor(Q(k)))+1/sqrt_floor(2*P*(k-1)))
        assert H_bound < (2 if k<50 else Q(82,100))
    assert R*exp(Q(57,50))[1]/(exp(Q(25,4))[0]-1)<Q(2,100)


def contraction():
    elo,ehi = exp(1)
    for k,beta,U,M in [(100,4,Q(32,25),30),(50,4,Q(129,100),32),(10,8,Q(257,100),60)]:
        assert beta**2/P**2+Q(1,k)<U**2
        radial = ehi-1/ehi+Q(1,k-1)
        tail = 1/(elo*(1-Q(1,2*k)))
        assert Q(12,k)+(radial+1)*(2+Q(9,2)*U)+2*tail*(2+Q(9,4)*U)<M
    for k,beta,d,q,u,v,M in [
        (100,4,Q(31,100),Q(1004,1000),Q(5,4),Q(1,50),30),
        (50,4,Q(31,100),Q(1007,1000),Q(7,5),Q(9,200),32),
        (10,8,Q(78,1000),Q(1008,1000),Q(2),Q(1,8),60),
    ]:
        assert R**2/(2*beta**2)<d and 1+d/k<q
        assert 1-(1+log(u)[1])/u>v
        assert v>(d+q)/k
        x=(d+q)*u
        start = 2*q*u*exp(x)[1]+q*u*exp(d*u)[1]
        end = 2*q/(k*v-d-q)+q/(k*v-d)
        tail = (1+log(Q(k))[1])*exp(Q(-k,6))[1]+2/(1-d)
        assert start+end+2*tail<M


def denominator_and_moments():
    gap=Q(39,1000)
    assert 5*(1-(R/100)**2/24)*exp(-R/2)[0]>1 and 5>1+R
    assert 3*(1-(R/100)**2/24)*exp(-Q(24,100)*R)[0]>1 and 3>1+Q(48,100)*R
    assert Q(4,9)*gap*Q(48,100)*R<Q(3,100)
    assert 2*exp(Q(-1,5))[0]/R>Q(1,2)
    assert 1-exp(Q(-2,5))[1]>Q(3,200)
    assert (Q(2,100)+R/100)*(32+Q(1,100))<2
    for x,m0,m1 in [(48,16,74),(100,23,326)]:
        nu=Q(99,100*x)
        pole0=2+2/sqrt_floor(nu)
        if x==48:
            pole1=2+2*(sqrt_floor(Q(9,8))+Q(1,10**12))/sqrt_floor(nu)+Q(108,94)/nu
        else:
            pole1=2+2/sqrt_floor(nu)+3/nu
        assert pole0<m0 and pole1<m1
    assert 2/sqrt_floor(Q(99,100))+Q(1,5)<3
    assert Q(2,100)+2/(10*sqrt_floor(Q(99,100)))+Q(300,99)<4


def fourier_constants():
    a, gap = Q(48,25), Q(39,1000)
    assert a/2-a*a/400>Q(95,100)
    assert 2-a+2*gap<Q(16,100)
    assert gap*Q(507,100)**2>1
    assert 3*Q(507,100)*23<350 and 3*Q(507,100)*326<4959
    for x, B, D, amplitude, value, difference in [
        (48, 125000, 1860000, 4110, Q(2,100), Q(29,100)),
        (44, 61000, 313000, 696, Q(9,100), Q(44,100)),
    ]:
        mult=Q(amplitude,2*x*(x-1))*exp(30-Q(95,100)*x)[1]
        assert B*mult < value and D*mult < difference
        assert (1-(Q(33,100)+value)**2)>(Q(33,100)+difference)**2
    assert 122*10**5*exp(-59)[1]<Q(1,100)
    assert 1-(Q(1,3)+Q(1,100))**2>(Q(1,3)+Q(1,100))**2


def small_k():
    for k in range(4,100):
        if k < 10:
            eta, L, m = Q(218,1000), 119, 11
        elif k < 50:
            eta,L,m = Q(85,100),73,0
        else:
            eta,L,m = Q(89,100),45,0
        if k<10:
            assert eta*10000/k > L+m+Q(3,2)*log(Q(10000))[1]
        else:
            assert eta*10000/k > L+Q(5,2)*log(Q(10000))[1]
        assert eta/k > Q(5,2*10000)
    assert exp(13)[0]>130000 and exp(11)[0] > 34000


outer_join()
pole_tails()
contraction()
denominator_and_moments()
fourier_constants()
small_k()
print("Independent rational exponential and pi enclosures verified the outer join, Taylor contractions, denominator and pole bounds, Fourier endpoint arithmetic and small-threshold endpoints.")
