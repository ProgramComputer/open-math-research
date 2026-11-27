"""Spot-check the printed elementary bounds entering Zuo's cutoff-four sign test."""
from fractions import Fraction as Q
from math import factorial

def enclosure(x):
    assert 0 <= x < 162
    low = sum((x**j/factorial(j) for j in range(161)),Q(0))
    return low,low+x**161/factorial(161)/(1-x/162)

pi_upper=Q(22,7)
for shift,radius,ratio,budget in ((4,8,Q(7,10),34),(8,11,Q(9,10),6),(16,18,Q(24,25),1)):
    assert shift**2+pi_upper**2 < (radius*ratio)**2
    assert 170*enclosure(Q(budget))[1]*ratio**508 < Q(1,10**6)
assert pi_upper**2/8+pi_upper**3/12<5
assert Q(1,10**6) < Q(3,17*16)/enclosure(Q(5))[1]
assert Q(3,512)*(pi_upper**2+pi_upper**3/2+pi_upper**4/6)<Q(9,34)
assert 1+pi_upper**2/16**2 < Q(33,32)**2
assert Q(33,2)**6/enclosure(Q(16))[0]<Q(16,5)
assert Q(21,100)*Q(16,5)<Q(27,40)<Q(3,4)
assert Q(3,5)*Q(21,100)*Q(16,5)<Q(1,2)

n=512
assert Q(113,5)**2<n-1
assert n**8<enclosure(Q(339,5))[0]
assert n**2<enclosure(Q(113,5))[0]
assert (Q(16,1)**2)*(n-1)<9*n*n
assert 16*(n-1)<n*n
assert Q(6,n**5) < Q(1,4)
assert Q(6*n+1,n**4)<Q(1,8*n)
print('Cutoff-four printed elementary compact, middle and exterior sign budgets pass.')
