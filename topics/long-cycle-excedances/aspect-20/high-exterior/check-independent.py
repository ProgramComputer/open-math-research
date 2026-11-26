"""Independent rational scalar and integer-endpoint replay."""
from fractions import Fraction as F
from math import factorial, isqrt


def atan(q):
    s=sum(((-1)**j*q**(2*j+1)/(2*j+1) for j in range(14)), F(0))
    return s,s+q**29/29


def e_lower(q):
    """Raise a unit-interval Taylor lower bound to an exact power."""
    assert q>=0
    b=max(1,q.__ceil__())
    unit=q/b
    s=sum((unit**j/factorial(j) for j in range(18)), F(0))
    return s**b


a,b=atan(F(1,5))
c,d=atan(F(1,239))
P,Q=16*a-4*d,16*b-4*c
V=F(158,5)
U=F(191,500)
assert V**2<1001 and F(7,20)+1/V<U
# The cubic v(a-bv)^2 grows up to a/(3b), then decreases on this range.
a,b=F(39,40),F(7,800)
assert a-b*100>0 and V<a/(3*b)<100
for v in (V,F(100)):
    assert v*(a-b*v)**2/(2*U)>F(13,10)
z=1/e_lower(F(13,10))
bad=F(3,4)*z*z/(1-z)
word=F(10000)/e_lower(V-1/V)
assert bad<F(2,25) and word<F(1,1000)
assert (1-bad)/3-word>F(3,10)
assert 1/(e_lower(V/4)-1)+word<F(1,10)
mode_den_sq=2*P*31*F(19,20)
mode_num=1/(1-F(1,12*1001))
assert mode_num**2 < F(3,40)**2*mode_den_sq
assert F(3,40)+1/(2*V)+word<F(1,10)

rho=F(10,3)
q=1/e_lower(1/U**2)
assert q<F(1,900)
for lo,hi,limit in [(F(19,20),F(21,20),F(1,20)),(F(1,2),F(1,2),F(1,2)),(F(3),F(3),F(2))]:
    t=q*rho*max(hi,1/lo)
    assert rho*(1+hi)*t/(1-t)<limit
s=q*rho*max(F(20,19),F(21,20))
assert s<F(1,250)
l=F(21,20)
old_weight=rho*(s/(1-s)**2+l*s*(2-s)/(1-s)**2)
change_mid=(1+l)*s/(3*(1-s))
tail_index_gap=F(1,2)-U
assert tail_index_gap*V>3 and 1+U/tail_index_gap<5
change_tail=rho*l*5*s**4*(4/(1-s)+s/(1-s)**2)
assert old_weight<F(1,20) and change_mid<F(3,1000) and change_tail<F(1,1000)
assert (1+l)/3+old_weight+change_mid+change_tail<F(19,20)

rel_low,rel_high=F(5,6),F(7,6)
for h in range(1,36):
    growth=F(h+1,h)
    a,b=(rel_low,rel_high) if h==1 else (rel_low/rel_high,rel_high/rel_low)
    assert F(19,20)*growth*a>F(1,2)
    assert F(21,20)*growth*b<3

assert e_lower(1/(3*U**2))>F(7,2)
# Independently check exact floors and phase criteria at every old row size.
for n in range(1001,10000):
    h=isqrt(49*n)//20
    assert h*h<=F(49*n,400)<(h+1)**2
    assert (h+1)**2<=U**2*n
    a,b=F(6*h+5,6),F(h+1)
    theta_cap=b*Q/n
    assert theta_cap<F(39,1000)
    factor=1-theta_cap**2/6
    assert (a*P*factor)**2>n
    assert (b*P*factor)**2>F(6,5)*n
    assert (1-theta_cap**2/2)**2*n > 4*a*a
print("Independent scalar bounds, signed-error budget, and all 8,999 integer phase endpoints passed.")
