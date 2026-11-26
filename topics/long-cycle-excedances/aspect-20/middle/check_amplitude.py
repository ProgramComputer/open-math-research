"""Validated on real height intervals using Arb; no floating-point decisions."""
import argparse
from flint import arb, ctx
from math import ceil
from fractions import Fraction

ctx.prec=100
pi=arb.pi()
one=arb(1)
alpha=arb(3)
beta=arb(27)/10

def upper(x,y):
    return x if x<y else y if y<x else x.upper()+abs(y-x).upper()

def lower(x,y):
    return x if x>y else y if y>x else x.lower()-abs(y-x).upper()

def upperbound_max(x,y):
    return x if x>y else y if y>x else x.upper()+abs(y-x).upper()

def height_bounds(u,v,J):
    r=(v*v+pi*pi).sqrt()
    rho=[r/(v*v+p*p*pi*pi).sqrt() for p in range(1,32,2)]
    vals=[q*q for q in rho]
    tail=r*r/(2*pi*pi*31)
    power=one
    c=[arb(0),r/(1+u.exp())]
    # For low heights the odd-pole estimate alone suffices.
    freq=ceil((2*J+20)/float(u)) if u>=2 else 0
    if freq:
        freq+=2
        assert freq*u>=2*J
        ratios=[a*r for a in range(1,freq+2)]
        poisson=[(-a*u).exp()/a for a in range(1,freq+2)]
        last=1/(1-(-u/2).exp())
        for a in range(len(ratios)):
            poisson[a]*=ratios[a]
    for j in range(2,J+1):
        lattice=2*(sum(vals)+tail*power)/j
        if freq:
            for a in range(len(ratios)):
                poisson[a]=poisson[a]*ratios[a]/j
            c.append(upper(lattice,sum(poisson[:-1])+poisson[-1]*last))
        else:c.append(lattice)
        vals=[w*q for w,q in zip(vals,rho)]
        power*=rho[-1]
    return c

def kblocks(x):
    last=9999//x
    groups=[]
    k=4
    while k<=last:
        stop=min(last,k+max(0,k//12-1))
        factors=[]; t=one; w=1+alpha/k
        for j in range(1,stop):t*=w;factors.append(t+1)
        groups.append((k,stop,factors,(1+beta/stop).log(),x*k*(1+beta/k).log()))
        k=stop+1
    return groups

def audit(x,step):
    groups=kblocks(x); last=groups[-1][1]
    worst=(-1e10,None)
    for i in range(0,315*step):
        u=arb(i)/step;v=arb(i+1)/step
        ru=(u*u+pi*pi).sqrt()
        rv=(v*v+pi*pi).sqrt()
        c=height_bounds(u,v,last-1)
        nmin=lower(arb(251),ru*ru/(pi*pi))
        for k,l,factors,lograd,aspect in groups:
            penalty=lower(nmin*lograd,aspect)
            amp=sum(a*b for a,b in zip(c[1:l],factors))
            # If no higher pole can approach the outer edge, use the outer radius itself.
            if 1+8*(pi/rv)**2 > (1+arb(4)/k)**2:
                # Distance from the p=1 pole is 3r/k; all higher poles are >r/k away.
                # For the logistic bound cap the physical gap at one half.
                penalty=lower(nmin*(1+alpha/l).log(),x*k*(1+alpha/k).log())
                pref=upperbound_max(4*rv*rv/pi,2*l*rv/pi)
            else:
                # Largest gap obtained by subdividing the legal interval at interior pole radii.
                # Number of subintervals <= 2 + (1+3/K)rv/(2pi).
                count=2+(1+alpha/k)*rv/(2*pi)
                pref=upperbound_max(4*rv*rv/pi,(arb(40)/3)*l*rv/pi*count)
            logerr=pref.log()+amp-penalty
            if not logerr < -(arb(100).log()):
                raise ArithmeticError((i,step,k,l,'circle/S',logerr))
            # Only for reporting; each certified test above is an Arb comparison.
            f=float(logerr.upper())
            if f>worst[0]:worst=f,(i,step,k,l)
    print('All circle errors below S/100, x >=',x,'k groups:',len(groups),'height intervals:',315*step,'largest exploratory log upper:',worst)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--x',type=int,default=25);p.add_argument('--step',type=int,default=2)
    a=p.parse_args();audit(a.x,a.step)
