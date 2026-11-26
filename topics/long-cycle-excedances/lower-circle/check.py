"""Rational scalar checks for a lower-height common-circle criterion."""
from fractions import Fraction as Q


def exp_bounds(x):
    assert 0 <= x < 32
    term = lower = Q(1)
    for j in range(1, 51):
        term *= x / j
        lower += term
    return lower, lower + term * x / 51 / (1-x/52)


def lower_exp(x):
    return exp_bounds(Q(x))[0]


def upper_exp(x):
    return exp_bounds(Q(x))[1]


def log_bounds(x):
    """Factor powers of two to keep the atanh argument at most 1/3."""
    assert x >= 1
    power = 0
    while x >= 2:
        x /= 2
        power += 1

    def base(x):
        y = (x-1)/(x+1)
        lower = 2*sum((y**(2*j+1)/(2*j+1) for j in range(32)), Q())
        return lower, lower + 2*y**65/(65*(1-y*y))

    half = base(Q(2))
    rest = base(x)
    return tuple(power*a+b for a,b in zip(half,rest))


pi_lo, pi_hi = Q(157,50), Q(22,7)
height = 55_000
theta_cap = Q(3,250)
assert Q(9,25)*pi_hi/100 < theta_cap
assert Q(7,20)-Q(1,600) > Q(17,50)
assert Q(7,20)+Q(1,100) <= Q(9,25)
assert (Q(17,50)*pi_lo*(1-theta_cap**2/6))**2 > 1
assert (1-theta_cap**2/2)/Q(9,25) > 2
assert Q(12,25)+theta_cap < pi_lo/6
assert 1/(3*Q(9,25)**2) > Q(5,2)
assert lower_exp(Q(5,2)) > Q(459,40)

slabs = (
    # minimum, maximum, alpha, beta, attenuation, log(k_max) cap, amplitude exponent
    (4,39,Q(1,4),10,Q(218,1000),Q(4),119),
    (40,80,Q(2,5),9,Q(358,1000),Q(22,5),150),
    (81,139,Q(3,4),7,Q(672,1000),Q(5),238),
)
assert lower_exp(Q(11)) > max(34_000, height)
for lo,hi,alpha,beta,eta,log_cap,C in slabs:
    assert (beta**2*lo+pi_hi**2)*(2*alpha/lo+alpha**2/lo**2) < 8*pi_lo**2
    assert beta**2*hi < 4*10_000
    lower_radius = Q(9,10)*alpha
    assert eta < lower_radius-lower_radius**2/(2*lo)
    assert lower_exp(log_cap)>hi
    assert 2*upper_exp(alpha)*(6+10*log_cap)<C
    assert eta*height/hi > C+11+Q(3,2)*11
    assert eta*height/hi > Q(3,2)
    assert 2*(40/alpha+10)<=340

gamma_cases = (
    (21,10,Q(3,10),45,Q(56,5)),
    (40,9,Q(231,500),56,Q(31,2)),
    (81,7,Q(213,250),63,Q(22)),
    (140,6,Q(57,50),70,Q(59,2)),
)
alphas = (Q(1,4),Q(2,5),Q(3,4),Q(1))
for (k,beta,g,first,second), alpha in zip(gamma_cases, alphas):
    assert alpha+pi_hi**2/(2*beta**2)<g
    assert first**2<=beta**2*k
    assert second**2<2*pi_lo*(k-1)
    assert pi_hi*upper_exp(g)*(Q(1,first)+1/second)<Q(12,25)
    assert (1+alpha/k)**2-1<Q(1,25)
assert Q(1,4)+pi_hi**2/200<Q(3,10)
assert all(100*k>4*(k-1)**2 for k in range(4,21))
assert pi_hi*upper_exp(Q(3,10))/(lower_exp(Q(5,2))-1)<Q(2,5)
assert (1+Q(1,16))**2-1<Q(13,100)


def tail_bound(gamma, decay):
    first = 3/lower_exp(8*decay-4*gamma)
    a = decay-gamma/4
    return first + (5+1/(4*a))/lower_exp(24*a)


assert Q(1,2)-Q(13,100)/4>Q(46,100)
assert Q(1,2)-Q(1,25)/4==Q(49,100)
assert tail_bound(Q(2,5),Q(46,100))<Q(21,50)
assert tail_bound(Q(12,25),Q(49,100))<Q(21,50)

k, beta = 140, 6
assert (beta**2*k+pi_hi**2)*(Q(2,k)+Q(1,k*k))<8*pi_lo**2
assert beta**2*399<4*10_000
U=Q(48,25)
assert Q(36)/pi_lo**2+Q(1,k)<U**2
assert 1/(lower_exp(Q(1))*(1-Q(1,2*k)))<Q(38,100)
assert Q(12,k)+(upper_exp(Q(1))+1)*(2+Q(9,2)*U)+Q(76,100)*(2+Q(9,4)*U)<45
assert pi_hi**2/72<Q(69,500)
assert Q(69,500)/k<Q(1,1000)
assert Q(69,500)+Q(1001,1000)<Q(57,50)
assert 1-Q(69,500)==Q(431,500)
assert 2*Q(1001,1000)*Q(7,5)*upper_exp(Q(57,50)*Q(7,5))<14
assert Q(1001,1000)*Q(7,5)*upper_exp(Q(69,500)*Q(7,5))<2
assert 1-Q(5,7)*(1+log_bounds(Q(7,5))[1])>Q(9,200)
assert Q(9,200)-Q(57,50)/k>Q(1,30)
assert 60*Q(1001,1000)/k<Q(43,100)
assert lower_exp(Q(5))>k
assert log_bounds(Q(2))[0]-Q(1,2)>Q(1,6)
assert 6/lower_exp(Q(k,6))<Q(1,10)
assert 2/Q(431,500)<3
assert 14+2+2*Q(43,100)+2*Q(31,10)<45
assert 1+upper_exp(pi_hi)<25
assert Q(9,10)-Q(9,10)**2/(2*k)>Q(89,100)
assert lower_exp(Q(13))>130_000
assert Q(89,100)*height/399>58+Q(5,2)*11

# Locate the first old-row size at which the old k=400 radial criterion applies.
left,right=10_000,100_000
while right-left>1:
    mid=(left+right)//2
    lg_low,lg_high=log_bounds(Q(mid))
    lhs=Q(89,100)*mid/400
    if lhs>47+Q(5,2)*lg_high:
        right=mid
    else:
        assert lhs<=47+Q(5,2)*lg_low
        left=mid
assert Q(89,100)*left/400 < 47+Q(5,2)*log_bounds(Q(left))[0]
assert Q(89,100)*right/400 > 47+Q(5,2)*log_bounds(Q(right))[1]
assert Q(89,100)/400 > Q(5,2)/10_000
print("The common phase join is valid for n >= 10,000.")
print("The existing radial criterion for k=400 first passes at n =", right)
print("All four small-threshold slabs 4 <= k <= 399 pass for n >= 55,000.")
