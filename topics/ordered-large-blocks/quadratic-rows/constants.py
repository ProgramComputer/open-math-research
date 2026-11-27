from fractions import Fraction as Q
from independent import gap_counts, factorial

lo, hi = Q(693147, 10**6), Q(693148, 10**6)
mu, gamma = Q(7, 20), Q(1, 30)
z = Q(1, 3)
partial = 2 * sum(z**(2*k+1)/(2*k+1) for k in range(8))
assert lo < partial and partial + 2*z**17/(17*(1-z*z)) < hi
r = 8
assert (14*(r+3)*mu**(r+1) + 14*(r+2)*mu**(r+2)
        + 196*mu**r*(1+14*mu**(r+2)) + 196*mu**(r+1)*(1+14*mu**(r+1))) < Q(1,10)
for n in range(6):
    assert Q(gap_counts[0][n+1], (n+1)*gap_counts[0][n]) <= Q(3,2)
for r in range(8):
    assert Q(gap_counts[1][r+1], (r+1)*gap_counts[1][r]) > Q(3,2)
assert (1+14*mu**7)/(lo*(1-14*mu**6)) < Q(3,2)
assert 14*mu**17 < Q(1,100) and 196*mu**8 < lo
assert Q(9,10)/(4*Q(101,100)) > Q(1,5)
assert 5*Q(202,100)*hi**3 < 9
for r in range(8):
    low = 8*lo**(r+3)*Q(gap_counts[2][r], factorial[r])
    high = 8*hi**(r+3)*Q(gap_counts[2][r], factorial[r])
    next_low = 8*lo**(r+4)*Q(gap_counts[2][r+1], factorial[r+1])
    next_high = 8*hi**(r+4)*Q(gap_counts[2][r+1], factorial[r+1])
    assert high <= Q((r+4)**2,2)
    assert r+2 <= next_low-high and next_high-low <= r+4
assert 2200*(1+mu)*mu**8 < Q(19,20) < 3*lo/2
assert 3*hi/2 + Q(19,20) < 2
assert 2200*mu**8 < 1
assert Q(5,2)*8+7-3*hi*(8+1)/2-hi**2 > 1
m = j = 20
assert 196*mu**m < Q(1,20) and 1+lo-Q(1,20) > Q(7,5)
assert 196*(1+mu)*mu**m/(1-gamma/mu)+3*gamma**(m+1)/(1-gamma) < Q(1,100)
assert 14*(1+mu)/(1-14*mu**(2*j)) < 30
assert 30*mu**(2*j)*(2*j+198) < Q(1,100)
assert 14*mu**(2*j) < Q(1,100)
assert 6*gamma/(1-gamma)**2 < Q(1,4)
assert 15*mu**(2*j)*(j+4)**2 < Q(1,4)
assert Q(101,100)/Q(49,50) < Q(11,10) and Q(51,50)/2 < Q(21,40)
assert Q(3,8)*32-Q(451,40) > 0
assert Q(3,8)-Q(451,40*64) > Q(1,6)
assert Q(1,3)*Q(64,67)**2 > Q(1,4)
assert Q(2*64*(2*64+198),(64-1)**2) < 11
assert 16*hi**4 < 4 and 4*11**2*Q(30,29)/64**2 < Q(1,4)
print("Independent exact analytic-constant checks passed.")
