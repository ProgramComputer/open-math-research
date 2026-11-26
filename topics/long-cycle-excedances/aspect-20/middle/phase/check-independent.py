"""Bound the nonprincipal residues using a separate geometric density tail."""
from flint import arb,ctx
from math import factorial
ctx.prec=110
pi=arb.pi()
one=arb(1)
maxval=arb(0)
count=0
for k in range(4,500):
    m=k-1
    fac=factorial(m)
    shift=(1+arb(3)/k)**2-1
    # Width two; the last interval reaches 315.
    for l in range(5,315,2):
        h=l+2
        h2=1+(h/pi)**2
        sup=shift*h2
        if sup<8: continue
        s2=1/h2
        N=max(arb(max(251,20*k)),1+(l/pi)**2)
        # The ratio of successive densities is <= exp(-l+m/a) for every s>=l.
        b=1+(2*m)//l
        val=arb(0)
        for i in range(1,b+1):
            w=min(i*h,max(m,i*l))
            term=arb(w)**m*(-arb(w)).exp()/fac
            val+=term if i<b else term/(1-(-arb(l)/2).exp())
        cost=arb(0)
        for p in range(3,145,2):
            if sup<p*p-1:break
            raised=min(1+(p*pi/l)**2,(1+shift)*(1+(pi/l)**2))
            phase=pi*(p-1)*(raised**m).sqrt()*val
            cost+=p*(phase-(N+1)/2*(1+(p*p-1)*s2).log()).exp()
        assert cost<arb(9)/100,(k,l,cost)
        count+=1
        maxval=max(maxval,cost.upper())
print(count,'active angular boxes of width at most 2; weighted error < 9/100')
