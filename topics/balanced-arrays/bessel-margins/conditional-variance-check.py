"""Compare the four-pattern formula against literal row-subset probabilities."""
from math import comb, factorial
from fractions import Fraction as F


def check(n,d,r):
    k=n*r//d; q=F(r,d); size=comb(d,r)
    a,b,c=(F(comb(d-2,i),size) for i in (r-2,r-1,r))
    values=range(max(0,2*k-n),k+1)
    weights=[]
    for l in values:
        z=n-2*k+l; s=k-l
        mult=factorial(n)//(factorial(z)*factorial(l)*factorial(s)**2)
        weights.append(mult*a**l*b**(2*s)*c**z)
    total=sum(weights); mu=sum(w*l for l,w in zip(values,weights))/total
    ideal=F(n*r*(r-1),d*(d-1))
    var=0
    for l,w in zip(values,weights):
        for count,j in ((n-2*k+l,0),(2*(k-l),1),(l,2)):
            p=F(r-j,d-2); var+=w/total*count*p*(1-p)
    delta=var-n*q*(1-q)*d*(d-3)/((d-1)*(d-2))
    assert delta==2*(ideal-mu)/(d-2)**2
    assert 0<delta<=F(2*(d-1),r*(d-r)*(d-2)**2)


count=0
for n in range(2,41):
    for d in range(4,23):
        for r in range(2,d-1):
            if not n*r%d:
                check(n,d,r); count+=1
print(count,'exact variance discrepancies in the predicted intervals')
