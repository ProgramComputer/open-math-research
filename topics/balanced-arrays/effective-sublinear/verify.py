"""Replay finite cumulant identities and endpoint arithmetic with exact integers."""
from fractions import Fraction as F
from itertools import combinations
from math import comb, factorial


def check_row(d, ell, y):
    p = F(ell, d)
    a = d*p*(1-p)/(d-1)
    gamma = a*(d-2*ell)/(d-2)
    xi = F(ell*(ell-1)*(d-ell)*(d-ell-1), d*(d-1)*(d-2)*(d-3))
    fourth, quadratic = a-6*xi, xi-a*a
    sums = [sum(row) for row in combinations(y, ell)]
    second, third, fourth_raw = (
        F(sum(z**power for z in sums), comb(d, ell)) for power in (2, 3, 4)
    )
    q2, q3, q4 = (sum(z**power for z in y) for power in (2, 3, 4))
    assert second == a*q2 and third == gamma*q3
    assert fourth_raw-3*second**2 == fourth*q4+3*quadratic*q2**2


rows = 0
for d in range(10, 13):
    # Both populations have sum zero. The asymmetric one also tests odd cumulants.
    for y in (tuple(2*j-d+1 for j in range(d)), tuple(range(d-1))+(-sum(range(d-1)),)):
        for ell in range(d+1):
            check_row(d, ell, y)
            rows += 1
for d in range(10, 151):
    for ell in range(d+1):
        p = F(ell, d)
        v = p*(1-p)
        a = d*v/(d-1)
        xi = F(ell*(ell-1)*(d-ell)*(d-ell-1), d*(d-1)*(d-2)*(d-3))
        assert abs(a*(d-2*ell)/(d-2)) <= a
        assert abs(a-6*xi) <= a
        assert abs(xi-a*a) <= 2*v/d
u = 10**6
# For u >= 10^6, log(u) <= u/100: ratio log(u)/u decreases and log(10)<3.
assert 6*3 < F(u,100)
assert F(1,100)+F(10,400) < F(4,100)
assert 36+F(8,100)*u < F(u,2)
assert 42+F(5,100)*u < F(u,4)
assert F(1,8)*u-F(4,100)*u > 6
assert F(u**2, 5**6*factorial(6)*40) > 1000
assert F(99,100)/F(3,5)**2 > 2
assert F(7,12) > F(1,2)
assert F(2,9)-F(1,50) > F(1,5)
assert F(15,8) < 2
assert F(422+10,u) < F(1,5)-F(18,100)
assert F(1,6)-F(1,8) > F(10,u)
print(f"{rows} exact subset laws, coefficient bounds through d=150, and cutoff checks passed.")
