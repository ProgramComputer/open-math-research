"""Continuous gamma and residue bounds at old sizes 251 through 9999."""
from argparse import ArgumentParser
from fractions import Fraction
from math import factorial
from time import perf_counter

from flint import arb, ctx

ctx.prec = 96
P = Fraction(157,50)
Q = Fraction(22,7)


def ball(q):
    return arb(q.numerator)/q.denominator


def gamma_mesh(m, lo, hi):
    # At frequency a the gamma mass is maximized where a*s is closest
    # to the mode within [a*lo, a*hi]. The mode is exactly m.
    cutoff = max(1,(2*m+lo-1)//lo,(180+lo-1)//lo)
    finite = arb(0)
    fac = factorial(m)
    for a in range(1,cutoff):
        t = min(a*hi,max(m,a*lo))
        finite += arb(t**m)*arb(-t).exp()/fac
    # For a >= cutoff use the Poisson event at half the mean.
    decay=arb(-lo)/8
    return finite+(cutoff*decay).exp()/(1-decay.exp())


def phase_join():
    theta = Fraction(86,1000)
    assert Fraction(73,2700)*Q<theta
    assert Fraction(180,73)*(1-theta**2/2)>Fraction(12,5)
    assert Fraction(12,5)**2*251 > 38**2
    assert Q**2/(2*20*Fraction(12,5)**2)<Fraction(43,1000)
    assert 2*P*24>12**2
    fac = ball(Fraction(43,1000)).exp()*ball(Q)
    hi = fac*(arb(1)/38+arb(1)/12)
    assert hi<arb(37)/100
    assert 23<Fraction(5,8)*38
    # Poisson lower-tail Chernoff exponent at 5/8 of the mean.
    v=arb(5)/8
    assert 1-v+v*v.log()>arb(8)/100
    assert fac/((arb(8)*38/100).exp()-1)<arb(18)/100
    assert Fraction(37,100)+theta<P/6
    assert (Fraction(61,180)*P*(1-theta**2/6))**2>1


def check(min_aspect, step, cap):
    assert min_aspect >= 20
    assert Fraction(33,16)*(1+(5/P)**2)<8
    assert Q**2*9998<315**2
    assert 1+Fraction(33,16)*(1+(315/P)**2)<145**2
    max_bound=arb(0)
    boxes=0
    terms=0
    for k in range(4,9999//min_aspect+1):
        m=k-1
        shift=Fraction(6,k)+Fraction(9,k*k)
        for lo in range(5,315,step):
            hi=min(315,lo+step)
            support=shift*(1+(hi/P)**2)
            if support < 8:
                continue
            boxes+=1
            mesh=gamma_mesh(m,lo,hi)
            nlo=max(Fraction(251),Fraction(min_aspect*k),1+(lo/Q)**2)
            sum_bound=arb(0)
            S2lo=P**2/(P**2+hi**2)
            for p in range(3,145,2):
                if p*p-1>support:
                    break
                terms+=1
                u=(p*p-1)*S2lo
                radial=(1+ball(u)).log()*ball(-(nlo+1)/2)
                b=min((p*Q/lo)**2,(1+shift)*(1+(Q/lo)**2)-1)
                vertical=(1+ball(b)).log()*ball(Fraction(m,2))
                amplitude=ball(Q)*(p-1)*mesh*vertical.exp()
                sum_bound+=p*(radial+amplitude).exp()
            if not sum_bound<ball(cap):
                raise ArithmeticError((k,lo,hi,sum_bound,cap))
            if sum_bound.upper()>max_bound:
                max_bound=sum_bound.upper()
    print(f"Continuous residue envelope < {cap} for aspect >= {min_aspect}.")
    print(f"Checked {boxes} integer-height boxes and {terms} pole bounds. "
          f"Largest upper endpoint below {max_bound.upper()}.")
    print("Exterior phase join and n sin^2(theta*) > 1 also pass.")


if __name__=='__main__':
    cli=ArgumentParser(description=__doc__)
    cli.add_argument('--aspect',type=int,default=20)
    cli.add_argument('--step',type=int,default=4)
    cli.add_argument('--cap',type=Fraction,default=Fraction(1,10))
    args=cli.parse_args()
    phase_join()
    start=perf_counter()
    check(args.aspect,args.step,args.cap)
    print(f"Elapsed {perf_counter()-start:.3f}s.")
