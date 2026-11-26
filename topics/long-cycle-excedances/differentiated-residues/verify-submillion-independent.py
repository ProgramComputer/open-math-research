"""Independent rational checks for the 972,000 differentiated-residue cutoff."""
from fractions import Fraction as F
from math import factorial


def exponential(x, terms=80):
    lower=sum((x**j/factorial(j) for j in range(terms+1)),F(0))
    upper=lower+x**(terms+1)/factorial(terms+1)/(1-x/(terms+2))
    return lower,upper


def atan_bounds(x, terms=12):
    a=sum((-1)**j*x**(2*j+1)/(2*j+1) for j in range(terms))
    b=a+(-1)**terms*x**(2*terms+1)/(2*terms+1)
    return min(a,b),max(a,b)


l1,h1=atan_bounds(F(1,5))
l2,h2=atan_bounds(F(1,239))
pi_l,pi_h=16*l1-4*h2,16*h1-4*l2
assert F(157,50)<pi_l<pi_h<F(22,7)
# Direct finite summation of the exponential envelope on b_s, including its tail.
c=F(13,20)+F(1,13)
e=exponential(c)[1]
w0=e+(F(1,2)+F(1,4*847))*e**2
w1=e+2*(F(1,2)+F(1,4*847))*e**2
for j in range(2,20):
    f=e**(j+1)/(2*factorial(j))
    w0+=f
    w1+=(j+1)*f
tail0=e**21/(2*factorial(20))/(1-e/21)
tail1=21*e**21/(2*factorial(20))/(1-e*22/21**2)
assert w0+tail0<10 and w1+tail1<27
assert (w0+tail0)*(w1+tail1)<16**2
assert F(11,20*factorial(10))<F(1,6_000_000)

load=F(144,125)
q=F(10,11)
qnorm=exponential(pi_h*q/2+q*q/(2*(1-q/2)))[1]
assert qnorm<9
# sqrt(847)>29.1, a deliberately different lower enclosure.
assert F(291,10)**2<847
j=F(27,24*847)+F(160,291)/load+F(10,847)/load
qder=qnorm*(pi_h/2+q/(1-q/2))*j
assert qder<16

beta=load/192
def kernel(p):
    return (1+beta*(p*p-1))**-96
# Retain p=5,...,15, then a distinct pure-power integral tail from 15.
tail=beta**-96*F(15)**-190/190
moment=2*sum(p*kernel(p) for p in range(5,16,2))+tail
assert moment < F(1,20000)
# Separate nearby correction with the actual exponential majorants.
epsilon=1/exponential(F(13,20)*14)[0]
delta=1/exponential(F(13,20)*23)[0]
fraction_r=F(10,24)+F(140,11*24)/exponential(F(1))[0]
assert fraction_r< F(5,8)
value=qnorm*4*(F(1,6000000)+epsilon)+qnorm*moment+qnorm*F(9,2)*5*delta
derivative=(qnorm*8+qder*4)/6_000_000
derivative+=(qnorm*8*fraction_r+qder*4)*epsilon
derivative+=(qnorm+qder)*moment
derivative+=(qnorm*F(33,4)*24+qder*F(9,2)*5)*delta
assert value<F(6,1000) and derivative<F(17,1000)

assert 1-F(1,7*847)>F(999,1000)**2
assert 7*pi_l**2*F(999,1000)**2>64
assert F(4,7)+F(1,13)<F(65,100)
hprime=pi_h*exponential(F(65,100))[1]*(F(1,232)+F(1,72))
assert 2*pi_l*846>72**2 and hprime<F(12,100)
md=F(1,264)+hprime/load
assert md<F(11,100)
principal=(11/(pi_h+F(33,2)/F(999,1000)))/exponential(F(113,100))[1]
assert principal>F(17,100)
near=1/exponential(4*load/(1+F(8,7*847))-4*hprime)[0]
assert near<F(17,1000)
error=near+value/(2*principal)
derivative_error=md+near*(3+md)+derivative/(2*principal)
assert error<F(35,1000)
assert 1-error**2>(F(77,100)+derivative_error)**2
assert (F(2,25)+F(2,5))*(1+error)/11<F(5,100)

height=972000
v_lower=985  # floor(sqrt(972000)) is 985.
assert v_lower**2<height<(v_lower+1)**2
assert F(7,20)*v_lower-F(1,6)>F(17,50)*v_lower
assert F(1,100)*v_lower>1
theta_upper=F(9,25)*pi_h/v_lower
assert theta_upper<F(1,100)
assert (F(17,50)*pi_l*(1-theta_upper**2/6))**2>F(11,10)
assert (1-theta_upper**2/2)/F(9,25)>2
assert F(12,25)+theta_upper<pi_l/6
assert (1-F(1,7*4)/2)*F(11,20)>F(49,100)  # also follows from u<=.1025 below
u=(1+F(1,20))**2-1
assert (1-u/2)*F(11,20)>F(49,100)
assert F(3,20)-F(3,20)**2/(2*4)>F(146,1000)
assert F(146,1000)*height/400>164+10+F(3,2)*14
assert F(146,1000)/400>F(3,2*height)
assert (400+pi_h**2)*(F(1,10)+F(1,400))<8*pi_l**2
assert 4*height>100*400
assert F(6,5)*height>(11*96)**2
assert 37**2*96*7<height
assert F(89,100)*96>47+F(5,2)*F(153,10)
assert exponential(F(153,10))[0]>1408334
print("Exact independent medium-slab coefficient bounds:",float(value),float(derivative))
print("Exact independent scaled phase and derivative error bounds:",float(error),float(derivative_error))
print("Independent derivative, lag and 972,000 joins passed.")
