"""Independent rational replay of the nine paired-residue slabs."""
from fractions import Fraction as F
from functools import cache
from math import factorial, isqrt

GRID = 1 << 60
P = 81
POLES = tuple(range(-P, P+1, 2))
U = F(6, 5)
H = F(4, 7)
LOW = F(547, 1000)
N = 10000


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
def stars(degree):
    terms, mass, first = lattice(degree,92)
    s = d = F(0)
    for a in range(1,P+3,2):
        s = max(s, sum(w/abs(p-a) for p,w in zip(POLES,terms) if p!=a))
        d = max(d, sum(abs(p)*w/abs(p-a) for p,w in zip(POLES,terms) if p!=a))
    return up(s+mass/2), up(d+first/2)


@cache
def mass(degree):
    terms,tail,_=lattice(degree,92)
    return sum(terms)+tail


@cache
def weighted_tail(degree):
    terms,_,tail=lattice(degree/2,46)
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


def envelopes(K,l,X,A,cap):
    L=[F(0)]*(cap+1)
    J=L.copy()
    for i,g,v in degrees(K,cap):
        s,t=stars((g-F(1,K))*U/X)
        L[i]=up(v*s/A)
        J[i]=up(v*(F(i,4)*t/(l*A)+s/(K*U)))
    q=[F(1)]
    for b in range(1,cap+1):
        q.append(up(sum((i*L[i]*q[b-i] for i in range(4,b+1)),F(0))/b))
    dq=[up(sum(J[i]*q[b-i] for i in range(4,b+1))) for b in range(cap+1)]
    return q,dq


def finite_cost(l,X,q,dq,exclude,omit_zero):
    value=res=F(0)
    for b in range(1 if omit_zero else 0,5*X+1):
        g=max(F(1),F(b,5)) if b else F(0)
        if g+1>X:
            continue
        h=F(b,4)
        lo=max(F(1,X),1-h/l)*U
        lom=max(F(1,X),1-(h+1)/l)*U
        hi=1-g/X
        terms,_,first=lattice(lo,92)
        diag=sum(w*max(1,hi*abs(p)) for p,w in zip(POLES,terms))+first-exclude
        off=weighted_tail(lo)/isqrt(N)
        wn=H if l-h>=2 else 1
        wm=H if l-h-1>=2 else 1
        value+=wn*(q[b]*(diag+off)+dq[b]*(mass(lo)-exclude))
        res+=wm*q[b]*(mass(lom)-exclude)
    return value,res


def eps(r):
    if r<1:
        return H
    if r<2:
        return 1-LOW
    j=int(r)
    return min(H-(F(1,2) if j==2 else LOW),F(j+1,2*j*factorial(j)))


def exp_range(x):
    assert x>=0
    terms=[x**i/factorial(i) for i in range(81)]
    approx=sum(terms)
    return approx,approx+terms[-1]*x/81/(1-x/82)


def atan_range(x):
    approx=sum((-1)**j*x**(2*j+1)/(2*j+1) for j in range(16))
    return approx,approx+x**33/33


def constants():
    a,b=atan_range(F(1,5))
    c,d=atan_range(F(1,239))
    pi0,pi1=-up(-(16*a-4*d)),up(16*b-4*c)
    K=208
    C=F(9988,10000)
    assert C*C<1-F(10,K)**2
    s=pi0*K*C/10
    sq=F(isqrt(int(2*pi0*(K-1)*GRID**2)),GRID)
    rate=F(1,5)+F(4,5)*(-2*sum(F(1,9)**(2*j+1)/(2*j+1) for j in range(8))-F(1,8)*F(1,9)**17)
    assert rate>F(1,50)
    eta=up(pi1*exp_range(up(F(100,2*K)/C**2))[1]*(1/s+1/sq))
    assert eta<F(175,1000)
    e0=up(1/exp_range(F(K,40))[0]/(1-1/exp_range(-up(-s/50))[0]))
    assert e0<F(1,100)
    theta=F(49,1000)
    assert theta-theta**3/6>F(10,K)
    cos=1-(theta+eta)**2/2
    amp=F(1)
    for j in range(4):
        lower=max(F(9,4), F(4*j,5)*pi0*C)
        harmonic=sum(F(1,p) for p in range(1,j+1))
        amp=min(amp, 2*lower/pi1/exp_range(up(harmonic+eta+e0))[1])
    assert 50/(4*pi0*C)<4
    return eta,cos,amp


def infinite_tail(cap):
    u=F(9,8)
    t=u**4
    K=208
    # Telescoping guarantees these bounds binwise before a geometric factorial tail.
    block=1/(1-F(1,K))-F(1,2)+F(1,4*K)
    coarse=F(51,100)
    assert block<coarse and (1+F(4,K))/2<coarse
    e=exp_range(t)[1]
    m=t+coarse*t*(e-1)
    moment=t+coarse*t*((1+t)*e-1)
    s0,s1=stars((1-F(1,K))*U/48)
    a=F(9,4)
    L=m*s0/a
    L1=4*moment*s0/a
    J=moment*s1/(10*a)+m*s0/(K*U)
    return 2*H*u**(-cap-1)*exp_range(up(L))[1]*(1+L1/40+J)


def main():
    assert __debug__
    eta,cos,amp=constants()
    log2lo=2*sum(F(1,3)**(2*j+1)/(2*j+1) for j in range(8))
    log2hi=log2lo+F(1,7)*F(1,3)**17
    assert exp_range(H-F(1,100))[0]>F(7,4)
    assert 1+log2hi+(1+H)/100<3*H
    assert F(1,2)+(log2lo-F(1,2))/4>LOW
    assert 1+log2lo+F(1,2)>4*LOW
    w,_,first=lattice(U,92)
    offvalue=sum(v for p,v in zip(POLES,w) if abs(p)>1)+first/P
    offder=sum(abs(p)*v for p,v in zip(POLES,w) if abs(p)>1)+first
    assert offvalue<F(1,50) and offder<F(1,16)
    assert H*H*(offvalue**2+offder**2)<F(38,1000)**2
    cap=240
    tail=infinite_tail(cap)
    assert tail<F(1,10000)
    print('Amp lower',int(amp*10**6),'phase cosine lower',int(cos*10**6),'scaled tail upper',ceil(tail*10**9))
    for l,X in [(4,6),(6,10),(10,16),(16,22),(22,28),(28,34),(34,40),(40,44),(44,48)]:
        K=N//X
        assert K>=208 and K-1>=184 and K>=184
        q,dq=envelopes(K,l,X,F(10),5*X)
        v,z=finite_cost(l,X,q,dq,0,True)
        lag=mass(U/X)/(10*l)
        baseline=2*LOW-F(38,1000)-v-lag*(H*mass((1-F(1,l))*U)+z)
        assert baseline>0
        A=F(isqrt(int(16*N*U))//X,4)
        assert A*A*X*X<=N*U
        if A>=10:
            print(l,X,int(baseline*10**6),'automatic')
            continue
        q,dq=envelopes(K,l,X,A,cap)
        v,z=finite_cost(l,X,q,dq,2,False)
        old=new=tail
        for b,(x,y) in enumerate(zip(q,dq)):
            h=F(b,4)
            old+=2*eps(l-h)*(x*max(1,h/l-1)+y)
            new+=2*eps(l-1-h)*x
        lag=mass(U/X)/(A*l)
        result=cos-(1/(A*l)+eta/U)-lag-(v+old+lag*(z+new))/amp
        assert result>0
        print(l,X,int(baseline*10**6),int(result*10**6))


if __name__=='__main__':
    main()
