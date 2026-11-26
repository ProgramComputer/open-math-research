"""Rational joint-vector replay at n >= 1000 and 4 <= n/k <= 15/2."""
from fractions import Fraction as F
from functools import cache
from math import factorial, isqrt

GRID = 1 << 60
P = 81
POLES = tuple(range(-P, P+1, 2))
U = F(6, 5)
H = F(4, 7)
LOW = F(547, 1000)
N = 1000


def ceil(x):
    return -(-x.numerator // x.denominator)


def up(x):
    return F(ceil(x*GRID), GRID)


@cache
def lattice(degree, exponent):
    """Bound rho_p^degree assuming degree*S^2 >= argument 'degree'."""
    c = degree / (2*exponent)
    assert (2*exponent-1)*c*P*P > 1-c
    terms = tuple(up((1+c*(p*p-1))**(-exponent)) for p in POLES)
    first = up((1+c*(P*P-1))**(1-exponent)/(2*c*(exponent-1)))
    return terms, up(first/P), first


@cache
def stars(degree,E):
    terms, mass, first = lattice(degree,E)
    s = d = F(0)
    for a in range(1,P+3,2):
        s = max(s, sum(w/abs(p-a) for p,w in zip(POLES,terms) if p!=a))
        d = max(d, sum(abs(p)*w/abs(p-a) for p,w in zip(POLES,terms) if p!=a))
    return up(s+mass/2), up(d+first/2)


@cache
def mass(degree,E):
    terms,tail,_=lattice(degree,E)
    return sum(terms)+tail


@cache
def weighted_tail(degree,E):
    terms,_,tail=lattice(degree/2,E//2)
    return sum(abs(p)*w for p,w in zip(POLES,terms) if abs(p)>1)+tail


def degrees(K,cap):
    yield 4,F(1),F(1)
    for i in range(5,cap+1):
        g=F(i-1,4)
        j=g.numerator//g.denominator
        if j==1:
            value=1/(g-F(1,K))-4/F(i)
            if i==8:
                value+=F(1,4*K)
        else:
            value=(F(1,4)+F(1,K))/(2*factorial(j))
        yield i,g,value


def envelopes(K,l,X,A,cap,E):
    L=[F(0)]*(cap+1)
    J=L.copy()
    for i,g,v in degrees(K,cap):
        s,t=stars((g-F(1,K))*U/X,E)
        L[i]=up(v*s/A)
        J[i]=up(v*(F(i,4)*t/(l*A)+s/(K*U)))
    q=[F(1)]
    for b in range(1,cap+1):
        q.append(up(sum((i*L[i]*q[b-i] for i in range(4,b+1)),F(0))/b))
    dq=[up(sum(J[i]*q[b-i] for i in range(4,b+1))) for b in range(cap+1)]
    return q,dq


def finite_cost(l,X,q,dq,exclude,omit_zero,E):
    value=res=F(0)
    for b in range(1 if omit_zero else 0,int(5*X)+1):
        g=max(F(1),F(b,5)) if b else F(0)
        if g+1>X:
            continue
        h=F(b,4)
        lo=max(F(1,X),1-h/l)*U
        lom=max(F(1,X),1-(h+1)/l)*U
        hi=1-g/X
        terms,_,first=lattice(lo,E)
        diag=sum(w*max(1,hi*abs(p)) for p,w in zip(POLES,terms))+first-exclude
        off=weighted_tail(lo,E)/isqrt(N)
        wn=H if l-h>=2 else 1
        wm=H if l-h-1>=2 else 1
        value+=wn*(q[b]*(diag+off)+dq[b]*(mass(lo,E)-exclude))
        res+=wm*q[b]*(mass(lom,E)-exclude)
    return value,res


def main():
    assert __debug__
    log2lo=2*sum(F(1,3)**(2*j+1)/(2*j+1) for j in range(8))
    log2hi=log2lo+F(1,7)*F(1,3)**17
    assert sum((H-F(1,100))**j/factorial(j) for j in range(30))>F(7,4)
    assert 1+log2hi+(1+H)/100<3*H
    assert F(1,2)+(log2lo-F(1,2))/4>LOW
    assert 1+log2lo+F(1,2)>4*LOW
    for i in range(16,30):
        l,X=F(i,4),F(i+1,4)
        K=ceil(N/X)
        E=(K-1)//2
        A=F(isqrt(int(10000*N*U))//X,100)
        assert K>=100 and 2*E<=K-1 and 4*(E//2)<=K
        assert A*A*X*X<=N*U
        q,dq=envelopes(K,l,X,A,int(5*X),E)
        v,z=finite_cost(l,X,q,dq,0,True,E)
        lag=mass(U/X,E)/(A*l)
        w,tail,first=lattice(U,E)
        val=sum(v for p,v in zip(POLES,w) if abs(p)>1)+tail
        der=sum(abs(p)*v for p,v in zip(POLES,w) if abs(p)>1)+first
        assert H*H*(val*val+der*der)<F(38,1000)**2
        baseline=2*LOW-F(38,1000)-v-lag*(H*mass((1-F(1,l))*U,E)+z)
        assert baseline>F(28,1000)
        print(l,X,int(baseline*10**6))

if __name__=='__main__':
    main()
