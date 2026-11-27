"""Rational scalar comparisons for the bounded-aspect exterior proof."""
from fractions import Fraction as Q
from math import factorial

def exp_lo(x):
    return sum((x**j/factorial(j) for j in range(81)), Q(0))

v_min = Q(125,4)
v_max = Q(100)
C = Q(191,500)
pi_lo, pi_hi = Q(157,50), Q(22,7)
assert v_min**2 < 1000
assert Q(7,20)+1/v_min <= C
assert v_min/(32*C)>Q(51,20)
assert v_min-1/v_min>31
word_error=10000/exp_lo(Q(31))
assert word_error < Q(1,10**6)
lattice_ratio=1/exp_lo(Q(51,20))
assert lattice_ratio**2/(1-lattice_ratio)+word_error < Q(1,100)
assert lattice_ratio/(1-lattice_ratio)+word_error < Q(1,10)
lower_factor = Q(99,100)
a_weight=Q(8,3)
assert lower_factor/(1+a_weight*Q(2,21))<Q(9,10)

# Upper bound via the Poisson tail at two thirds of the target.
log_3_over_2_lower=2*(Q(1,5)+Q(1,375))
assert log_3_over_2_lower-Q(1,3)>Q(1,15)
assert v_min/2<exp_lo(Q(3))
assert Q(6)/exp_lo(v_min/5)<Q(2,100)
upper_coef=Q(38,25)
R=Q(128,25)
assert (1+a_weight*upper_coef)/lower_factor < R
assert R*Q(7,6)<6
assert R*2<11
q_total = Q(1,150)
assert 6/exp_lo(1/C**2)<q_total
assert 11/exp_lo(Q(1000,36))<q_total

# Appending one color label, normalized by either central coefficient.
stirling_numerator=1/(1-Q(1,12*1000))
point_mass=Q(47,100)
assert (stirling_numerator/point_mass)**2*Q(50,49)<2*pi_lo*Q(3,4)
assert Q(9,2)**2>20
coef_change=(point_mass*(Q(9,2)/v_min+a_weight*C/2)
           +Q(1,2)/v_min+a_weight*C/8
           +word_error*(1+a_weight*C*v_max/4))/lower_factor
assert coef_change < Q(46,100)
assert word_error*(1+a_weight*C*v_max/4)/lower_factor < Q(1,1000)

# Far indices and the Rouché circles.
assert Q(3,20)*v_min - 1>3
assert 1+C/Q(3,20)*Q(5,4)<5
assert (Q(1,5)+a_weight*C/(4*Q(3,20)))/lower_factor<3

def tail_linear(s):
    return 1/(1-s)**2-1

def far_linear(s):
    return s**4*(5/(1-s)+s/(1-s)**2)

def far_squared(s):
    return s**4*(25/(1-s)+10*s/(1-s)**2+s*(1+s)/(1-s)**3)

lo,hi = Q(17,20), Q(23,20)
disk_ratio=Q(1,125)
assert q_total*max(hi,1/lo)<disk_ratio
assert (R*tail_linear(disk_ratio)
       +hi*(R*disk_ratio/(1-disk_ratio)+3*far_linear(disk_ratio))) < Q(3,20)
assert R*Q(3,2)*tail_linear(2*q_total)<Q(1,2)
assert 4*R*tail_linear(3*q_total)<2

# For the old polynomial use the factors l and l+1.
s=disk_ratio
old_weighted=(R*2*s/(1-s)**3+
              hi*(R*tail_linear(s)+3*far_squared(s)))
assert old_weighted<Q(19,100)
local_change=Q(46,100)*(1+hi)*s/(1-s)
assert local_change<Q(8,1000)
far_change=15*hi*far_squared(s)
assert far_change<Q(1,1000)
assert Q(46,100)+hi/1000+old_weighted+local_change+far_change < lo
assert lo*Q(77,123)>Q(1,2)
assert hi*Q(3,2)*Q(123,77)<3
assert 2*lo*Q(77,100)>Q(1,2)
assert 2*hi*Q(123,100)<3

# Both phase joins.
assert C*pi_hi/v_min<Q(39,1000)
assert exp_lo(1/(3*C*C))>7
assert hi*6<7
assert Q(7,20)-1/(6*v_min)>Q(17,50)
assert (Q(17,50)*pi_lo*(1-Q(39,1000)**2/6))**2>1
assert (Q(7,20)*pi_lo*(1-Q(39,1000)**2/6))**2>Q(6,5)
assert (1-Q(39,1000)**2/2)/C>2
print("All bounded-aspect front checks pass for 1000 <= n < 10000 and 4 <= n/k <= 20.")
