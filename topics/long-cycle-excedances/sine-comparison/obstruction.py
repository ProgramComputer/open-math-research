"""Exact arithmetic for the single-row absolute Cauchy obstruction."""
from fractions import Fraction as F

n = 10031
k = 209
S = F(364,33125)
C = F(33123,33125)
assert n + 1 == 48*k
assert S*S + C*C == 1
assert n >= 10000 and 4 <= F(n,k) <= 48
assert n*S*S >= F(6,5) and F(9,4) <= k*S <= 10
assert 4*S*S < F(1,2000)
assert 4*(n+1)*S*S < 5
assert F(22,7)/S+2 < 300
assert 4*(n+301)*S*S < 6
assert F(1,4000) < F(1,2*3**6) < F(2000,3**5)
print('Cauchy and sine-weighted Cauchy obstructions passed exact arithmetic.')
