"""Exact scalar checks for the bounded-height, large-aspect exterior theorem."""
from fractions import Fraction as Q
from math import factorial

def exp_lo(t):
    return sum((t**j / factorial(j) for j in range(81)), Q(0))

pi_lo, pi_hi = Q(157,50), Q(22,7)
v0, v1 = Q(125,4), Q(100)
p_bound = Q(191,500)
assert v0*v0 < 1001
assert Q(7,20)+1/v0 <= p_bound
def exponent_base(v):
    return v*(Q(39,40)-Q(7,800)*v)**2/p_bound
assert min(exponent_base(v0),exponent_base(v1))>Q(13,5)
assert Q(39,40)-Q(7,800)*v1>0
# The derivative has at most one sign change, from positive to negative.
assert v0 < Q(39,40)/Q(21,800) < v1
fail_rate = Q(3,4)/exp_lo(Q(13,5))/(1-1/exp_lo(Q(13,10)))
assert fail_rate<Q(2,25)

word_boundary = 10_000/exp_lo(Q(31,1))
assert v0-1/v0 > 31
assert word_boundary < Q(1,1000)
assert Q(1,3)*(1-fail_rate)-word_boundary>Q(3,10)
assert 1/(exp_lo(Q(31,4))-1) + word_boundary < Q(1,10)
# e^(1/(12n)) is at most (1-1/(12n))^-1.
stirling_num = 1/(1-Q(1,12*1001))
assert (stirling_num/Q(3,40))**2 < 2*pi_lo*31*Q(19,20)
assert 1/(2*v0) <= Q(2,125)
assert Q(3,40)+Q(2,125)+word_boundary < Q(1,10)

ratio, q = Q(10,3), Q(1,900)
outer1, outer2 = Q(1,2), Q(3)
disk_lower, disk_upper = Q(19,20), Q(21,20)
assert exp_lo(1/p_bound**2)>1/q
def geom(radius_lower,radius_upper):
    s=q*ratio*max(radius_upper,1/radius_lower)
    return ratio*(1+radius_upper)*s/(1-s)
assert geom(disk_lower,disk_upper)<Q(1,20)
assert geom(outer1,outer1)<Q(1,2)
assert geom(outer2,outer2)<2

s = Q(1,250)
assert q*ratio*max(disk_upper,1/disk_lower)<s
old_weighted = ratio*(s/(1-s)**2+disk_upper*((1-s)**(-2)-1))
assert old_weighted < Q(1,20)
local_change = Q(1,3)*(1+disk_upper)*s/(1-s)
assert local_change < Q(3,1000)
assert Q(3,20)*v0-1 > 3
assert 1+p_bound/Q(3,20)*Q(5,4)<5
far_change = ratio*disk_upper*5*s**4*(4/(1-s)+s/(1-s)**2)
assert far_change < Q(1,1000)
assert Q(1,3)*(1+disk_upper)+old_weighted+local_change+far_change<disk_lower

assert disk_lower*Q(5,7)>Q(1,2)
assert disk_upper*Q(3,2)*Q(7,5)<3
assert disk_lower*2*Q(5,6)>Q(1,2)
assert disk_upper*2*Q(7,6)<3

angle_cap=Q(39,1000)
assert p_bound*pi_hi/v0<angle_cap
assert Q(7,20)-1/(6*v0)>Q(17,50)
assert (Q(17,50)*pi_lo*(1-angle_cap**2/6))**2>1
assert (Q(7,20)*pi_lo*(1-angle_cap**2/6))**2>Q(6,5)
assert (1-angle_cap**2/2)/p_bound>2
assert exp_lo(1/(3*p_bound**2)) > Q(7,2)
print("All scalar bounds pass for 1001 <= n < 10000, n/k >= 20.")
