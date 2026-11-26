"""Exact margins for the x >= 25 differentiated slab and sub-million joins."""
from fractions import Fraction as Q
from math import factorial


def exp_bounds(x, terms=56):
    low = sum((x**j / factorial(j) for j in range(terms+1)), Q())
    high = low + x**(terms+1)/factorial(terms+1)/(1-x/(terms+2))
    return low, high


bound_c = Q(13,20)+Q(1,13)
ev, ee = Q(52,25), Q(81,10)
assert exp_bounds(bound_c)[1] < ev and exp_bounds(ev)[1] < ee
first_block = Q(501,1000)
assert Q(1,2)+Q(1,4*847)<first_block
moment0 = ev+first_block*ev**2+ev*(ee-1-ev)/2
moment1 = ev+2*first_block*ev**2+ev*((1+ev)*ee-1-2*ev)/2
assert moment0<10 and moment1<27 and moment0*moment1<16**2
assert Q(11,20*factorial(10))<Q(1,6_000_000)

pi_upper, pi_lower = Q(22,7), Q(157,50)
load = Q(144,125)
D = Q(10,11)
assert exp_bounds(pi_upper*D/2+D**2/(2*(1-D/2)))[1]<9
J = Q(27,24*847)+Q(16,29)/load+Q(10,847)/load
assert 29**2<847
assert 9*(pi_upper/2+D/(1-D/2))*J<16
assert Q(13,20)-Q(4,7)==Q(11,140)
assert Q(10,24)+Q(140,11*24)/Q(8,3)<Q(5,8)
assert Q(13,20)*(24-10)>9
assert exp_bounds(Q(3))[0]>20
assert exp_bounds(Q(1))[0]>Q(8,3)
assert exp_bounds(Q(13,20)*(24-1))[0]>2_000_000

beta = load/192
K = 1+beta*(5**2-1)
h = 96
assert (2*h-1)*beta*5**2 > 1-beta
assert 10*K**(-h)+K**(1-h)/(2*beta*(h-1))<Q(1,20000)
assert 24<5**2
near_val = Q(9*4,6_000_000)+Q(9*4,8000)
near_der = Q(9*8+16*4,6_000_000)+(16*4+9*8*Q(5,8))/8000
slow_val, slow_der = Q(9,20000), Q(9+16,20000)
fast_val = 9*Q(9,2)*5/2_000_000
fast_der = (9*Q(33,4)*24+16*Q(9,2)*5)/2_000_000
assert near_val+slow_val+fast_val<Q(6,1000)
assert near_der+slow_der+fast_der<Q(17,1000)

assert 1-Q(1,7*847)>Q(999,1000)**2
assert 7*pi_lower**2*Q(999,1000)**2>8**2
assert Q(4,7)+Q(1,13)<Q(65,100)
assert exp_bounds(Q(65,100))[1]<Q(193,100)
assert 2*pi_lower*846>72**2
assert pi_upper*Q(193,100)*(Q(1,232)+Q(1,72))<Q(12,100)
assert Q(1,11*24)+Q(12,100)/load<Q(11,100)
assert exp_bounds(Q(232,18))[0]>101
assert exp_bounds(Q(113,100))[1]<Q(31,10)
assert Q(110,31)/(pi_upper+Q(33,2)/Q(999,1000))>Q(17,100)
assert 4*load/(1+Q(8,7*847))>Q(23,5)
assert exp_bounds(Q(23,5)-Q(48,100))[0]>Q(1000,17)
assert Q(17,1000)*(3+Q(11,100))<Q(53,1000)
assert Q(6,1000)/Q(34,100)+Q(17,1000)<Q(35,1000)
assert 1-Q(35,1000)**2>Q(99,100)**2
assert Q(99,100)-Q(11,100)-Q(53,1000)-Q(17,1000)/Q(34,100)>Q(77,100)
assert ((Q(2,25)+Q(2,5))/11)*(1+Q(35,1000))<Q(5,100)
assert 7*847>76**2
assert Q(1,50)-Q(1,50)**3/6>Q(1,76)

# Phase entrance n >= 972,000 and its exterior ordering.
height = 972_000
assert height>100**2 and height>9**2/(Q(7,20)**2)
assert Q(1,100)*height > (Q(9,25)*pi_upper*100)**2/100
assert (Q(9,25)*pi_upper)**2 < height/10000
assert (Q(17,50)*pi_lower*(1-Q(1,60000)))**2>Q(11,10)
assert (1-Q(1,20000))/Q(9,25)>2
assert Q(1,2)-Q(10)/(6*(9+Q(5,6)))>Q(33,100)
assert Q(33,100)/Q(9,25)**2>Q(5,2)
assert exp_bounds(Q(5,2))[0]>Q(9,8)*Q(51,5)
assert Q(12,25)+Q(1,100)<pi_lower/6

# Adapt the small-threshold circle for 4 <= k < 400.
assert exp_bounds(Q(14))[0]>10**6 and exp_bounds(Q(6))[0]>400
assert exp_bounds(Q(1,5))[1]*66 < 82
assert Q(3,20)-Q(3,20)**2/8>Q(146,1000)
assert Q(146,1000)*height/400>164+10+Q(3,2)*14
assert exp_bounds(Q(10))[0]>18000
assert (400+pi_upper**2)*(Q(2,5*4)+Q(1,25*4**2))<8*pi_lower**2
assert Q(1,5)+pi_upper**2/200<Q(1,4)
assert exp_bounds(Q(1,4))[1]<Q(129,100)
assert 4*(20-1)**2<100*20 and 21>Q(9,2)**2 and 40*pi_lower>11**2
factor=pi_upper*Q(129,100)
assert factor*(Q(1,45)+Q(1,11))<Q(12,25)
assert factor/(exp_bounds(Q(5,2))[0]-1)<Q(12,25)
u = (1+Q(1,5*4))**2-1
assert Q(11,20)*(1-u/2)>Q(49,100)
assert 4*height>100*400

# Global joins to the known angular and radial regions.
assert Q(6,5)*height > (11*96)**2
assert 37**2*96*7 < height
assert exp_bounds(Q(153,10))[0]>1_408_334
assert Q(89,100)*96 > 47+Q(5,2)*Q(153,10)
print("Differentiated-residue slab passes: normalized derivative > 77/100, lag < 5/100.")
print("The radial and small-threshold phase joins extend to old size 972,000.")
print("The combined all-threshold cutoff is 972,000.")
