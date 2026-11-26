"""Exact rational constants for the uniform signed-pole comparison."""
from fractions import Fraction as Q
from math import factorial


def exp_interval(x, terms=32):
    lower = sum((x**j / factorial(j) for j in range(terms+1)), Q())
    tail = x**(terms+1) / factorial(terms+1) / (1-x/(terms+2))
    return lower, lower+tail


assert exp_interval(Q(1, 2))[1] < Q(33,20)
assert exp_interval(Q(43,20))[1] < 9
assert exp_interval(Q(1, 2))[0] > Q(8,5)
assert exp_interval(Q(1))[0] > Q(8,3)
assert 9*27 < 16**2

# Pole masses and first moments from integral estimates.
assert Q(4) / Q(2,5) < 4**2
assert Q(4) / Q(2,5) < Q(7,2)**2
assert 2+Q(7,2)+3/Q(2,5) == 13
assert Q(4) / Q(4,5) < Q(5,2)**2
assert Q(4) / Q(4,5) < Q(9,4)**2
assert 6+Q(9,2)*Q(5,4) < 12
assert 13+Q(33,4)*3 < 38

# Small k sin^2(theta) slab, at the worst A=k sin(theta).
a = 2000
delta = Q(9, 2*a)
assert Q(81,2)/(1-delta) < 41
assert Q(99,7)+Q(41,a) < 16
assert 16/(1-Q(16,a)) < 17
scaled_derivative = Q(10)+Q(27,4*a)+Q(45,16*a)
assert scaled_derivative < 11
assert Q(11,7)*scaled_derivative < 16
assert Q(99)/(1-delta) < 100
assert (16+Q(100,a))/(1-Q(16,a)) < 17
assert Q(204,a) < Q(13,100)
assert Q(850,a) < Q(65,100)

# Wide slab, keeping V_2 <= 8 when summing the occupied orders.
eta = Q(8,a)
assert Q(11,6)+Q(10,8) < 4
assert 32*eta+Q(12*9,2)*eta**2/(1-3*eta) < Q(13,100)
assert 160*eta+Q(30*27,2)*eta**2/(1-3*eta) < Q(65,100)

# Old single-pole errors at n sin^2(theta) >= 6/5.
beta = Q(1,160)
def kernel(p):
    return 1+beta*(p*p-1)
poles = tuple(range(3,10,2))
exponent = 96
moment_tail = kernel(9)**(1-exponent)/(2*beta*(exponent-1))
assert (2*exponent-1)*beta*9**2 > 1-beta
assert 2*sum(kernel(p)**(-exponent) for p in poles)+moment_tail/9 < Q(1,50)
assert 2*sum(p*kernel(p)**(-exponent) for p in poles)+moment_tail < Q(1,16)

assert 1-(Q(13,100)+Q(1,50))**2 > Q(98,100)**2
assert Q(98,100)-Q(65,100)-Q(1,16) > Q(1,4)
assert 2+Q(9,4)+Q(13,100) < Q(22,5)
assert Q(4,a)*Q(22,5) < Q(1,100)
assert exp_interval(Q(7,3))[0] > 10
assert Q(10**9,400000) > 30*18*Q(7,3)+20
print("Uniform middle comparison passes at k sin(theta) >= 2000.")
print("Scaled derivative exceeds 1/4 and the insertion lag is below 1/100.")
print("The combined sufficient height is 10^18 for every k.")
