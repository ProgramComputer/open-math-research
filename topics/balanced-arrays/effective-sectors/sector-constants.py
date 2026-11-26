"""Rational comparisons used in the n >= 1024 high-rank proof."""
from fractions import Fraction as F
from math import factorial


def exp_lower(x, order):
    return sum(x**j / factorial(j) for j in range(order + 1))


n = 1024
assert exp_lower(F(n, n+2), 6) > F(27,10)
assert (1 / (F(23,100) + F(1,n)) + 1 / (F(77,100) + F(1,n))) / 4 > F(139,100)
assert exp_lower(F(139,100), 8) > 4
assert F(77,100) + F(2,n) < F(193,250)
assert F(23,100) - F(1,n) > F(228,1000)
b = F(193,250)
rate = (F(9,10) - b)**2 / (8*b*(1-b))
assert n*rate > 1 and exp_lower(n*rate, 40) > 100*n
assert F(2,n)/F(228,1000)**2 < F(38,1000)
assert 1 / (1-F(38,1000)) < F(104,100)
assert F(104,100)/F(99,100)**2 < F(107,100)
g = F(27,10)
assert F(61,100)**2*g > 1
assert 2*(1-F(61,100)/g**2)/F(107,100) > F(17,10)
assert g**3 > F(34,10)**2
assert g*(1+F(17,10)/g**2)**2 > 4
print("All explicit sector constants verified over the rationals.")

assert 2*exp_lower(F(64), 40) > 5*64**4
assert exp_lower(F(32), 45) > 254*64**5
print("Both numerical comparisons for the effective logarithmic sector passed.")
