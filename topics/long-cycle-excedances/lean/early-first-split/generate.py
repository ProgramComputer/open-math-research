"""Generate candidate inputs to the supplying release's first-split checker."""
import gzip, json
from fractions import Fraction
from math import comb
from flint import ctx, fmpz_poly, fmpq_poly, fmpq

ctx.prec = 256
u = fmpz_poly([0,1])
euler = [fmpz_poly([1]), fmpz_poly([1])]
gamma = [None, fmpz_poly([1])]
for n in range(2, 109):
    row = gamma[n-1]
    gamma.append(fmpz_poly([(j+1)*row[j]+(2*(n-2*j)*row[j-1] if j else 0)
                            for j in range((n+1)//2)]))
    prev=euler[-1]
    euler.append((1+(n-1)*u)*prev + u*(1-u)*prev.derivative())

def expand(row,d):
    one=fmpz_poly([1,1])
    return sum((c*u**j*one**(d-2*j) for j,c in enumerate(row)), fmpz_poly([]))

def approx_roots(row):
    roots=[]
    for root,m in row.complex_roots():
        assert m==1 and root.imag.is_zero()
        man, exp=root.real.mid().man_exp()
        roots.append(Fraction(int(man))*Fraction(2)**int(exp))
    return sorted(roots)

def between(a,b):
    assert a<b
    shift=0
    while True:
        scale=1<<shift
        c=Fraction((a*scale).__floor__()+1,scale)
        if a<c<b: return c
        shift+=1

def sign_ok(poly,x,desired):
    assert x<0 or x==0
    numer=x.numerator
    shift=x.denominator.bit_length()-1
    assert 1<<shift==x.denominator
    value=0
    for j in reversed(range(len(poly))):
        upper=(desired<0) ^ bool(j%2)
        product=numer*value
        value=(poly[j]<<256)+(-((-product)>>shift) if upper else product>>shift)
    return desired*value>0

def dyadic(x):
    return [x.numerator, x.denominator.bit_length()-1]

def case(k):
    p=gamma[2*k-2]
    q=gamma[2*k-1] + (comb(2*k,k)//2)*u*gamma[k-1]**2
    assert expand(p,2*k-3)==euler[2*k-2]
    assert expand(q,2*k-2)==euler[2*k-1]+(comb(2*k,k)//2)*u*euler[k-1]**2
    old, new = approx_roots(p),approx_roots(q)
    d=k-2
    assert len(old)==d and len(new)==d+1
    outer=Fraction(new[0].__floor__()-1)
    qs=fmpq_poly(q); ps=fmpq_poly(p)
    def checked(g,rg,x,s):
        assert sign_ok(g,x,s)
        assert rg(fmpq(x.numerator,x.denominator))*s>0
    checked(q,qs,outer,(-1)**(d+1))
    checked(q,qs,Fraction(0),1)
    last=outer
    ws=[]
    for j,root in enumerate(old):
        left=between(new[j],root)
        right=between(root,new[j+1])
        s=(-1)**(d-j)
        assert last<left<right<0
        checked(p,ps,left,s);checked(p,ps,right,-s)
        checked(q,qs,left,s);checked(q,qs,right,s)
        ws.append([dyadic(left),dyadic(right)]);last=right
    return dict(k=k,p=list(map(int,p)),q=list(map(int,q)),outer=dyadic(outer),windows=ws)

if __name__=='__main__':
    import sys
    start,end=map(int,sys.argv[1:3])
    for k in range(start,end+1):
        print(json.dumps(case(k),separators=(',',':')),flush=True)
