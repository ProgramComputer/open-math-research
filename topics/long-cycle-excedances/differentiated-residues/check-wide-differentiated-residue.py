"""Exact constants for the x >= 50 differentiated common-residue theorem."""
from fractions import Fraction as Q
from math import factorial


def exp_bounds(x, terms=42):
    low = sum((x**j / factorial(j) for j in range(terms+1)), Q())
    high = low + x**(terms+1)/factorial(terms+1)/(1-x/(terms+2))
    return low, high


c = Q(13,25)+Q(1,49)
assert exp_bounds(c)[1] < Q(7,4)
assert exp_bounds(Q(7,4))[1] < Q(29,5)
ev, ee = Q(7,4), Q(29,5)
first_block = Q(251,500)
assert Q(1,2)+Q(1,4*225) < first_block
mom0 = ev+first_block*ev**2+ev*(ee-1-ev)/2
mom1 = ev+2*first_block*ev**2+ev*((1+ev)*ee-1-2*ev)/2
assert mom0<6 and mom1<15 and mom0*mom1<100
assert Q(17,32*factorial(16))<Q(1,10**12)

pi_upper, pi_lower = Q(22,7), Q(157,50)
assert 4*exp_bounds(pi_upper+4)[1]<6000
load = Q(147,125)
J = Q(15,49*225)+Q(10,15)/load+Q(6,225)/load
assert 6000*(pi_upper/2+4)*J<21000
assert Q(13,25)-Q(12,25)==Q(1,25)
assert Q(16,49)+Q(25,49)/Q(8,3)<Q(53,100)
assert Q(13,25)*(49-16)>17
assert Q(13,25)*(49-1)>24
assert exp_bounds(Q(3))[0]>20 and exp_bounds(Q(2))[0]>7
assert 20**5*7>20_000_000 and 20**8>25_000_000_000
assert exp_bounds(Q(1))[0]>Q(8,3)

beta = load/192
K = 1+beta*(7**2-1)
h = 96
assert (2*h-1)*beta*7**2 > 1-beta
pole_moment = 14*K**(-h)+K**(1-h)/(2*beta*(h-1))
assert pole_moment < Q(1,10**8)

near_val_short = Q(6000*6,10**12)
near_der_short = Q(6000*18+21000*6,10**12)
near_val_long = Q(6000*6,20_000_000)
near_der_long = (21000*6+6000*18*Q(53,100))/20_000_000
slow_val = Q(6000,10**8)
slow_der = Q(6000+21000,10**8)
fast_val = Q(6000)*Q(9,2)*7/25_000_000_000
fast_der = (Q(6000)*Q(33,4)*49+Q(21000)*Q(9,2)*7)/25_000_000_000
assert near_val_short+near_val_long+slow_val+fast_val < Q(1,500)
assert near_der_short+near_der_long+slow_der+fast_der < Q(1,100)

assert 1-Q(1,25*225)>Q(999,1000)**2
assert 5*pi_lower*Q(999,1000)>15
assert Q(12,25)+Q(1,49)<Q(51,100)
assert exp_bounds(Q(51,100))[1]<Q(5,3)
assert 2*pi_lower*224>37**2
assert pi_upper*Q(5,3)*(Q(1,225)+Q(1,37))<Q(17,100)
assert Q(1,3*49)+Q(17,100)/load<Q(16,100)
assert exp_bounds(Q(225,18))[0]>101
assert exp_bounds(Q(59,50))[1]<Q(10,3)
assert Q(9,10)/(pi_upper+Q(9,2)/Q(999,1000))>Q(23,200)

assert 4*load/(1+Q(8,25*225))>Q(23,5)
assert 12*load/(1+Q(24,25*225))>14
assert exp_bounds(Q(23,5)-Q(68,100))[0]>50
assert exp_bounds(Q(1298,100))[0]>100000
assert Q(1,50)+Q(1,100000)<Q(21,1000)
assert (3+Q(16,100))/50+(5+Q(16,100))/100000<Q(7,100)
assert Q(2,1000)/Q(23,100)+Q(21,1000)<Q(3,100)
assert 1-Q(3,100)**2>Q(99,100)**2
assert Q(99,100)-Q(16,100)-Q(7,100)-Q(1,100)/Q(23,100)>Q(71,100)
assert Q(1,50)-Q(1,50)**3/6>Q(1,75)
assert 1-Q(19,100)**2/2>Q(3,100)
assert Q(4,50)<Q(29,100)**2
assert (Q(2,50)+Q(29,100))/3==Q(11,100)
assert Q(11,100)*(1+Q(3,100))<Q(12,100)

height = 1_408_334
assert Q(6,5)*height > (3*96)**2
assert 24**2*96*25 < height
assert exp_bounds(Q(153,10))[0]>4_062_720
assert Q(89,100)*96>47+Q(5,2)*Q(153,10)
print("Wide differentiated-residue slab passes, with normalized derivative > 71/100 and lag < 12/100.")
print("The exterior and middle comparisons give all-threshold cutoff 1,408,334.")
