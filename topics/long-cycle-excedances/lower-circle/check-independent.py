"""Independent exact boundary checks for the lower common-circle heights."""
from fractions import Fraction as F
from functools import lru_cache
from math import factorial, isqrt


@lru_cache(None)
def exp(x, terms=75):
    lower=sum((x**j/factorial(j) for j in range(terms+1)),F(0))
    return lower,lower+x**(terms+1)/factorial(terms+1)/(1-x/(terms+2))


def atan(x, terms=12):
    a=sum((-1)**j*x**(2*j+1)/(2*j+1) for j in range(terms))
    b=a+(-1)**terms*x**(2*terms+1)/(2*terms+1)
    return min(a,b),max(a,b)


def log_near(x, terms=45):
    v=(x-1)/(x+1)
    low=2*sum(v**(2*j+1)/(2*j+1) for j in range(terms))
    return low,low+2*v**(2*terms+1)/((2*terms+1)*(1-v*v))


@lru_cache(None)
def log(x):
    z=F(x)
    factor=0
    while z>2:
        z/=2
        factor+=1
    low,high=log_near(z)
    low2,high2=log_near(F(2))
    return low+factor*low2,high+factor*high2


def sqrt_lower(x):
    scale=10**8
    return F(isqrt((x.numerator*scale*scale)//x.denominator),scale)


l1,h1=atan(F(1,5))
l2,h2=atan(F(1,239))
pi_low,pi_high=16*l1-4*h2,16*h1-4*l2
assert F(157,50)<pi_low<pi_high<F(22,7)

v=100
theta_hi=F(9,25)*pi_high/v
assert F(7,20)*v-F(1,6)>F(17,50)*v
assert theta_hi<F(3,250)
assert (F(17,50)*pi_low*(1-theta_hi**2/6))**2>1
assert (1-theta_hi**2/2)/F(9,25)>2
assert F(12,25)+theta_hi < pi_low/6
assert 1/(3*F(9,25)**2)>F(5,2)>log(F(459,40))[1]
for n in (32807,32808):
    lo,hi=log(n)
    value=F(89*n,40000)
    assert (value<47+F(5,2)*lo) if n==32807 else (value>47+F(5,2)*hi)
assert F(89,40000)>F(5,2*10000)

height=55_000
log_n=log(height)[1]
assert exp(F(11))[0]>34_000 and exp(F(13))[0]>130_000
for k in range(4,400):
    if k<=39:
        alpha,beta,eta,L=F(1,4),10,F(218,1000),119
    elif k<=80:
        alpha,beta,eta,L=F(2,5),9,F(358,1000),150
    elif k<=139:
        alpha,beta,eta,L=F(3,4),7,F(672,1000),238
    else:
        alpha,beta,eta=F(1),6,F(89,100)
    u=(1+alpha/k)**2-1
    assert (beta**2*k+pi_high**2)*u<8*pi_low**2
    assert 4*height>beta**2*k
    assert F(9,10)*alpha-(F(9,10)*alpha)**2/(2*k)>eta
    exp_gamma=exp(alpha+pi_high**2/(2*beta**2))[1]
    if k<=20:
        assert 100*k>4*(k-1)**2
        assert pi_high*exp_gamma/(exp(F(5,2))[0]-1)<F(2,5)
        assert (1-u/2)/2>F(46,100)
    else:
        gamma=pi_high*exp_gamma*(1/(beta*sqrt_lower(F(k)))+1/sqrt_lower(2*pi_low*(k-1)))
        assert gamma<F(12,25)
        assert (1-u/2)/2>F(49,100)
    if k<=139:
        assert 2*exp(alpha)[1]*(6+10*log(k)[1])<L
        assert 2*(40/alpha+pi_high**2)<340
        assert eta*height/k>L+11+F(3,2)*log_n
        assert eta/k>F(3,2*height)
    else:
        assert eta*height/k>58+F(5,2)*log_n
        assert eta/k>F(5,2*height)

# The high-k Taylor contraction, checked at its worst k=140.
U=F(48,25)
assert F(36)/pi_low**2+F(1,140)<U**2
assert 1/(exp(F(1))[0]*(1-F(1,280)))<F(38,100)
small=F(12,140)+(exp(F(1))[1]+1)*(2+F(9,2)*U)+F(19,25)*(2+F(9,4)*U)
assert small<45
assert pi_high**2/72<F(69,500)
assert F(69,500)/140<F(1,1000)
assert F(69,500)+F(1001,1000)<F(57,50)
early=2*F(1001,1000)*F(7,5)*exp(F(57,50)*F(7,5))[1]
early_principal=F(1001,1000)*F(7,5)*exp(F(69,500)*F(7,5))[1]
decay=1-F(5,7)*(1+log(F(7,5))[1])
assert decay>F(9,200) and decay-F(57,50)/140>F(1,30)
late=60*F(1001,1000)/140
assert log(2)[0]-F(1,2)>F(1,6)
original_tail=(1+log(140)[1])/exp(F(140,6))[0]
contracted_tail=original_tail+2/F(431,500)
assert early+early_principal+2*late+2*contracted_tail<45

# Independent direct nonprincipal sums through p=11, then a monotone integral.
for gamma,eta in ((F(2,5),F(46,100)),(F(12,25),F(49,100))):
    a=eta-gamma/4
    total=sum(F(p)/exp(eta*(p*p-1)-gamma*(p+1))[0] for p in (3,5,7,9,11))
    total+=1/(4*a*exp(a*(11*11-1))[0])
    assert total<F(21,50)
print("Independent phase floor and k=400 crossing passed.")
print("All 396 small thresholds k=4..399 passed the independent exact boundary replay.")
print("High-k Taylor contraction and both common-residue tail envelopes passed.")
