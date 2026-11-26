"""Rational enclosures for n>=10000, 4 <= n/k <= 48."""
import sys
from pathlib import Path
from functools import lru_cache
from math import factorial, isqrt
from fractions import Fraction as F

here = Path(__file__).resolve().parent
sys.path[:0] = [str(here.parent/'degree-blocks'), str(here)]
import verify_degree_blocks as prev

G=prev.G
B=4
U=F(6,5)
H=F(4,7)
P=63
T=240
up=prev.up
ceildiv=prev.ceildiv
poles=prev.POLES

@lru_cache(None)
def off_diagonal(c):
    # Envelope for rho_a^(r/2), exponent 48 (r >= k >= 208).
    assert 95*c*P**2>1-c
    w=sum(2*p*up((1+c*(p*p-1))**-48) for p in range(3,P+1,2))
    return F(w+up((1+c*(P*P-1))**-47/(94*c)),G)

@lru_cache(None)
def coefficients(K,lo,X,A,top):
    L=[0]*(top+1); J=L.copy()
    for i,g,mass in prev.degree_masses(K,top//B):
        s0,s1=prev.stars((g-F(1,K))*U/(192*X))
        L[i]=up(mass*s0/A)
        J[i]=up(mass*(s1*F(i,B)/(lo*A)+s0/(K*U)))
    Q=[G]
    for b in range(1,top+1):
        Q.append(ceildiv(sum(i*L[i]*Q[b-i] for i in range(B,b+1)),b*G))
    D=[ceildiv(sum(J[i]*Q[b-i] for i in range(B,b+1)),G) for b in range(top+1)]
    return Q,D

def eps(g):
    if g<1:return H
    if g<2:return F(453,1000)
    j=min(40,int(g))
    return min(H-(F(1,2) if j==2 else F(547,1000)),F(j+1,2*j*factorial(j)))

def nonprincipal(K,lo,X,Q,D,omit=2):
    v=z=F(0)
    for b in range(5*X+1):
        h=F(b,B); g=max(F(1),F(b,B+1)) if b else F(0)
        if g+1>X:continue
        y=max(F(1,X),1-h/lo); ym=max(F(1,X),1-(h+1)/lo); ymax=1-g/X
        c=y*U/192
        w,_,tail=prev.lattice(c)
        diag=F(sum(vv*max(F(1),ymax*abs(p)) for p,vv in zip(poles,w))+tail,G)-omit
        off=off_diagonal(c)/isqrt(K*lo)
        weight=H if lo-h>=2 else F(1)
        mweight=H if lo-1-h>=2 else F(1)
        v+=weight*(Q[b]*(diag+off)+D[b]*(prev.mass(c)-omit))/G
        z+=mweight*Q[b]*(prev.mass(ym*U/192)-omit)/G
    return v,z

def exact_high(K,lo,X):
    A=10
    Q,D=coefficients(K,lo,X,A,5*X)
    Q=Q.copy();Q[0]=0
    v,z=nonprincipal(K,lo,X,Q,D,0)
    ratio=prev.mass(U/(192*X))/(lo*A)
    lag=ratio*(H*prev.mass((1-F(1,lo))*U/192)+z)
    return F(1094,1000)-F(38,1000)-v-lag

def exp_upper(x,N=64):
    term=F(1);total=F(1)
    for i in range(1,N+1):
        term*=x/i;total+=term
    assert x<N+2
    return total+term*x/(N+1)/(1-x/(N+2))

def global_bounds():
    pi_lo=F(314,100);pi_hi=F(22,7); K=208; C=F(998,1000); eta=F(18,100)
    assert (1-F(10,K)**2)>C*C and pi_lo*K*C/10>65
    assert (F(36)**2<2*pi_lo*(K-1))
    assert pi_hi*exp_upper(F(100,2*K)/C**2)*(F(1,65)+F(1,36))<eta
    assert 5/(4*pi_lo*C)<F(2,5)
    # e^{-K/40}/(1-e^{-65/50}) < 1/100
    assert 1/prev.exp_lower(F(K,40))/(1-1/prev.exp_lower(F(65,50)))<F(1,100)
    # theta <= 1/20 by sin x >= x-x^3/6.
    assert F(1,20)-F(1,20)**3/6>F(10,K)
    assert 1-(eta+F(1,20))**2/2>F(97,100)
    har=F(0)
    for h in range(5):
        if h:har+=F(1,h)
        al=max(F(9,4),F(5*h,2))
        assert 2*al/pi_hi/exp_upper(har+F(19,100))>F(47,100)
    t=F(9,8)**4
    assert t+F(51,100)*t*(exp_upper(t)-1)<7
    assert t+F(51,100)*t*((1+t)*exp_upper(t)-1)<13
    base=F(9,8)
    s0,s1=prev.stars((1-F(1,K))*U/(192*48))
    assert s0<4 and s1<20
    # L(weight) <= 14, weight*L'(weight) <= 104; J(weight) <= 14.
    assert 28/F(9,4)<14 and 4*13*4/F(9,4)<104
    assert 13*F(20,20)+7*F(4,208)/U < 14
    assert 2*H*base**(-T)*exp_upper(F(14))*(1+F(104,40)+14)<F(1,10000)

def exact_low(K,lo,X,A):
    assert A>=F(9,4) and lo>=10 and T>=5*X
    Q,D=coefficients(K,lo,X,A,T)
    v,z=nonprincipal(K,lo,X,Q,D)
    pn=pm=F(1,10000)
    for b,(q,d) in enumerate(zip(Q,D)):
        h=F(b,B)
        pn+=2*eps(lo-h)*(q*max(1,h/lo-1)+d)/G
        pm+=2*eps(lo-1-h)*q/G
    amp=F(47,100)
    phase_slope=1/(A*lo)+F(18,100)/U
    lag=prev.mass(U/(192*X))/(A*lo)
    return F(97,100)-phase_slope-lag-(v+pn+lag*(z+pm))/amp

def main():
    global_bounds()
    for lo,X in [(4,6),(6,10),(10,16),(16,22),(22,28),(28,34),(34,40),(40,44),(44,48)]:
        K=10000//X
        high=exact_high(K,lo,X); assert high>0
        A=F(isqrt(192000)//X,4)
        assert A**2 * X**2 <=12000
        low=exact_low(K,lo,X,A) if A<10 else None
        assert low is None or low>0
        print(lo,X,'high margin',int(10**6*high),'low relative margin',int(10**6*low) if low else 'automatic','per million')
if __name__=='__main__':
    if not __debug__:raise SystemExit('Run without -O.')
    main()
