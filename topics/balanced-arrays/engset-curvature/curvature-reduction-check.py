from fractions import Fraction as F
from math import factorial
n=65536
s=F(7,9)
m=F(13,4)
x=F(59,50)*F(n,n+2)
assert sum(x**j/factorial(j) for j in range(18))>m
eta=2/(F(228,1000)**2*n)
assert 1/(1-eta)<F(1001,1000)
# 1.8027 < sqrt(13/4), hence this choice rounds the loss upward.
lower_sqrt=F(18027,10000)
assert lower_sqrt**2<m
b=(1-1/(s*lower_sqrt*m**2))/(F(1001,1000)*s*s)
assert b > 0 and s*s*m > 1
assert m > 1/s
a=s+1/s
assert (1+b/m**2)**2*m>a*a
assert a*a*m**3>16*b*b
print("The tilted sign margins at the lower curvature threshold are strictly positive.")
