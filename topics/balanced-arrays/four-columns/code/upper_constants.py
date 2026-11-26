"""Exact rational comparisons in the effective upper endpoint proof."""
from fractions import Fraction as Q
from math import factorial

v = Q(7, 38)
n = 200
eta = Q(3, 32)

# Modulus estimates, relative power error and phase correction.
assert 1-v/2 > Q(9, 10)
assert (5*v/12+v*v/6)/Q(9, 10) < eta
assert (1+v/2)**2+(v/2+v*v/6)**2 < Q(121, 100)
assert 2*Q(7, 15)/Q(121, 100) > Q(3, 4)
assert 1-Q(21, 152)**2/2 > Q(99, 100)
assert Q(25, 8)-Q(21, 152) > Q(29, 10)

# Radial estimate and monotonic tails.
assert Q(100, 99)*Q(3, 2)*Q(7, 6)*Q(32, 29)**3+Q(1, 100) < Q(5, 2)
assert 12*n**2*Q(5, 6)**n < Q(1, 100)
assert Q(n+1, n)**2*Q(5, 6) < 1
assert 1-(1-eta)/6 == Q(163, 192)
assert 52*n**3*Q(163, 192)**(n-1) < Q(1, 100)
assert Q(n+1, n)**3*Q(163, 192) < 1

# Phase margins at integer and bracket sample points.
assert Q(1, 32)+(1+Q(1, 32))/4 < Q(99, 100)
assert Q(3, 4)*Q(29, 5) > 4
assert sum(Q(4)**j/factorial(j) for j in range(5)) > 32
assert sum(Q(45, 32)**j/factorial(j) for j in range(5)) > 4
assert Q(5, 8)-Q(5, 8)**3/6 > Q(9, 16)
assert Q(49, 570)>Q(1, 13)
assert 1+v/2<Q(11, 10)
assert Q(10, 143)/2 > Q(1, 30)

# Amplitude, integer upper join, and first bracket availability.
assert Q(11, 10)*(1+eta)<Q(5, 4)
assert Q(5, 2)*eta+Q(25, 8*n)==Q(1, 4)
assert Q(1, 4)+(1+Q(1, 4))/4==Q(9, 16)
assert 2*Q(9, 16)**2 < 1
assert Q(21, 152)<Q(9, 16)
assert Q(533, 30)>Q(6, 5)*Q(22, 7)
t = 1/v
assert Q(450)*(1+t)/t==Q(70)*(1+t)**2/t==Q(10125, 19)
assert 532<Q(10125, 19)<533
print("All exact rational constants check.")
