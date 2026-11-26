"""Exact checks for the explicit scalar-curvature variation constants."""
from fractions import Fraction as F
from math import factorial


def exp_lower(x, degree=8):
    return sum(x**i / factorial(i) for i in range(degree + 1))


n = 10**200
# At the endpoint use log 10 < 7/3 and n^(1/6) > 10^33.
assert exp_lower(F(7, 3), 8) > 10
assert F(10**33, 10**18) > 4*200*F(7, 3)
assert F(4, 10)*10**33 > 22
assert F(1, 5)*10**8 > 1  # n^(1/24) exceeds 10^8.
assert F(295, 1000)*F(29, 100)/2 > F(4, 100)
assert F(1, 4800**2*200**2*10240) > 2*F(1, 10**18)
assert F(3, 4*4800**2) > 2*F(1, 10**18)
assert 2*10**9*F(1, 10**25)+4*10**11*F(1, 10**50)+F(50, n) < F(1, 10**6)
assert exp_lower(F(139, 100)) > 4
assert F(139, 100)+F(3, 10**6) < F(14, 10)
assert F(295, 1000)**2 > F(14, 10)*F(24, 100)**2
assert F(1, 100)*10**100 > 3*10**9
assert 2*10**9/F(23, 100)**3 < 2*10**11
assert 2*10**11*F(1, 10**100)+F(6, 10**6) < F(1, 10**5)
assert 1/(1-F(1, 10**5)) < F(1001, 1000)
assert F(295, 1000)*(1/(F(305, 1000)+1/F(n))
                    +1/(F(695, 1000)+1/F(n))) > F(139, 100)
g = F(32, 10)
assert exp_lower(F(59, 50)*n/(n+2)) > g
assert F(56, 100)**2*g > 1
assert 2*(1-F(56, 100)/g**2)/F(1001, 1000) > F(188, 100)
assert g**3 > F(376, 100)**2
assert g*(1+F(188, 100)/g**2)**2 > 4
assert (1-1/F(n)) / (F(84,100)+F(5,10**100))**2 > F(14,10)
print("All scalar-curvature and compensation constants passed.")
