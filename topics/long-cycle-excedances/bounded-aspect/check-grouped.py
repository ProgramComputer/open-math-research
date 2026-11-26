"""Scratch rational bounds using a product of individually retained pole factors."""
from fractions import Fraction as F
from functools import cache
from math import factorial,isqrt

B=8
P=47
G=1<<42
H=F(59,100)
DLOW=F(547,1000)
POLES=tuple(range(-P,P+1,2))

def ceil(x):
    return -(-x.numerator//x.denominator)

def ceildiv(a,b):
    return -(-a//b)

def fix(x):
    return ceil(x*G)

def rup(x):
    return F(fix(x),G)

def rdown(x):
    return -rup(-x)

def expu(x):
    assert 0<=x<162
    x=rup(x)
    q=F(1); s=q
    for i in range(1,161):
        q*=x/i
        s+=q
    return rup(s+q*x/161/(1-x/162))

def expl(x):
    assert x>=0
    x=rdown(x)
    q=F(1); s=q
    for i in range(1,161):
        q*=x/i
        s+=q
    return rdown(s)

def atanh_pos(x):
    x=F(x)
    assert 0<=x<1
    q=x;s=q
    for i in range(1,32):
        q*=x*x
        s+=q/(2*i+1)
    return rdown(2*s),rup(2*(s+q*x*x/65/(1-x*x)))

@cache
def log(x):
    assert x>0
    if x<1:
        a,b=log(1/x)
        return -b,-a
    j=0
    while x>2:
        x/=2
        j+=1
    a,b=atanh_pos((x-1)/(x+1))
    c,d=atanh_pos(F(1,3))
    return a+j*c,b+j*d

@cache
def rate(x):
    return max(F(0),x-1-log(x)[1])

@cache
def lattice(d,E):
    c=d/(2*E)
    assert (2*E-1)*c*P**2>1-c, (d,E)
    v=tuple(fix((1+c*(p*p-1))**(-E)) for p in POLES)
    tail1=fix((1+c*(P*P-1))**(1-E)/(2*c*(E-1)))
    tail0=ceildiv(tail1,P)
    return v,tail0,tail1

@cache
def stars(d,E):
    w,m,t=lattice(d,E)
    s=d=0
    for a in range(1,P+3,2):
        s=max(s,sum(ceildiv(v,abs(p-a)) for p,v in zip(POLES,w) if p!=a))
        d=max(d,sum(ceildiv(abs(p)*v,abs(p-a)) for p,v in zip(POLES,w) if p!=a))
    return F(s+ceildiv(m,2),G),F(d+ceildiv(t,2),G)

@cache
def mass(d,E):
    w,m,_=lattice(d,E)
    return F(sum(w)+m,G)

def primitives(K,cap):
    yield B,F(1),F(1)
    for i in range(B+1,cap+1):
        g=F(i-1,B)
        j=int(g)
        if j==1:
            v=1/(g-F(1,K))-F(B,i)+(F(1,4*K) if i==2*B else 0)
        else:
            v=(F(1,B)+F(1,K))/(2*factorial(j))
        yield i,g,v

def exp_poly(L):
    q=[G]
    for b in range(1,len(L)):
        q.append(ceildiv(sum(i*L[i]*q[b-i] for i in range(B,b+1)),b*G))
    return q

def add(a,b):
    return [i+j for i,j in zip(a,b)]

def mul(a,b):
    assert len(a)==len(b)
    l=len(a)
    ma,mb=max(a),max(b)
    if not ma or not mb:
        return [0]*l
    width=max(1,((ma*mb*l).bit_length()+7)//8)
    aa=int.from_bytes(b''.join(x.to_bytes(width,'little') for x in a),'little')
    bb=int.from_bytes(b''.join(x.to_bytes(width,'little') for x in b),'little')
    cp=(aa*bb).to_bytes(2*l*width,'little')
    return [ceildiv(int.from_bytes(cp[i*width:(i+1)*width],'little'),G)
            for i in range(l)]

def envelopes(K,E,l,X,A,U,cap):
    prim=[[0]*(cap+1) for p in POLES]
    diff=[[0]*(cap+1) for p in POLES]
    tails=[0]*(cap+1);td=tails.copy(); uniform=tails.copy();ud=tails.copy()
    for i,g,v in primitives(K,cap):
        d=(g-F(1,K))*U/X
        w,t,f=lattice(d,E)
        s,s1=stars(d,E)
        for j,p in enumerate(POLES):
            prim[j][i]=fix(F(w[j],G)*v/A)
            diff[j][i]=fix(F(w[j],G)*v*(F(i,B)*abs(p)/(A*l)+1/(K*U)))
        tails[i]=fix(v*F(t,2*G)/A)
        td[i]=fix(v*(F(i,B)*F(f,2*G)/(A*l)+F(t,2*G)/(K*U)))
        uniform[i]=fix(v*s/A)
        ud[i]=fix(v*(F(i,B)*s1/(A*l)+s/(K*U)))
    tail_q=exp_poly(tails)
    tail_dq=mul(tail_q,td)
    q=exp_poly(uniform)
    dq=mul(q,ud)
    yield None,q,dq
    for a in range(1,P+1,2):
        q=tail_q;dq=tail_dq
        for j,p in enumerate(POLES):
            if p==a: continue
            gap=abs(p-a)
            v=[ceildiv(x,gap) for x in prim[j]];v[0]=G
            dv=[ceildiv(x,gap) for x in diff[j]]
            dq=add(mul(dq,v),mul(q,dv))
            q=mul(q,v)
        yield a,q,dq

def eps(r):
    if r<1:return H
    if r<2:return 1-DLOW
    j=min(40,int(r))
    return min(H-(F(1,2) if j==2 else DLOW),F(j+1,2*j*factorial(j)))

def costs(N,K,E,l,X,A,U,cap,low):
    intervals=[]
    finite=[]
    for b in range(cap+1):
        h=F(b,B); g=max(F(1),F(b,B+1)) if b else F(0)
        intervals.append((eps(l-h),eps(l-h-1),max(1,h/l-1)))
        if g+1<=X and (low or b):
            dl=max(1/X,1-h/l)*U
            dm=max(1/X,1-(h+1)/l)*U
            yp=1-g/X
            w=H if l-h>=2 else 1
            wm=H if l-h-1>=2 else 1
            finite.append((b,dl,dm,yp,w,wm))
    V=R=Eold=Eres=F(0)
    for a,q,dq in envelopes(K,E,l,X,A,U,cap):
        if a==1 and low:
            for b,(e0,e1,y) in enumerate(intervals):
                Eold+=2*e0*(q[b]*y+dq[b])/G
                Eres+=2*e1*q[b]/G
            continue
        for b,dl,dm,yp,w,wm in finite:
            en=max(E,min(96,int(N*dl/U)//2))
            em=max(E,min(96,int(N*dm/U)//2))
            assert en>=E and em>=E
            z,t,f=lattice(dl,en)
            zm,tm,_=lattice(dm,em)
            zhalf,_,fh=lattice(dl/2,en//2)
            root=isqrt(N)
            if a is None:
                V+=w*(q[b]*(f+F(fh,root))+dq[b]*t)/(G*G)
                R+=wm*q[b]*F(tm,G*G)
            else:
                j=(a+P)//2
                diag=z[j]*max(1,yp*a)
                off=F(a*zhalf[j],root) if a!=1 else 0
                V+=F(2*w*(q[b]*(diag+off)+dq[b]*z[j]),G*G)
                R+=2*wm*q[b]*F(zm[j],G*G)
    assert all(isinstance(value,F) for value in (V,R,Eold,Eres))
    return V,R,Eold,Eres

def end_tail(K,E,l,X,A,U,cap):
    lam=F(11,10); t=lam**B
    c=((1-F(1,K))*U/X)
    a,b=stars(c,E)
    # Complete bins have mass <= 1/2 + 1/K + 1/(K(K-1)) + 1/(4K), or (1+B/K)/(2j!).
    m=max(1/(1-F(1,K))-F(1,2)+F(1,4*K),(1+F(B,K))/2)
    e=expu(t)
    m0=t+m*t*(e-1)
    m1=t+m*t*((1+t)*e-1)
    L=m0*a/A; moment=B*m1*a/A
    if L>=150:
        return F(10**99)
    J=m1*b/(A*l)+m0*a/(K*U)
    return 2*H*lam**(-cap-1)*expu(L)*(1+moment/(B*l)+J)

PI0=F(314159265358979,10**14)
PI1=F(314159265358980,10**14)

def sqrtlo(a):
    return F(isqrt(int(a*G**2)),G)

def residue(K,A,Ah):
    C=sqrtlo(1-(Ah/K)**2)
    if C<=0:
        return None
    tau=PI0*C/Ah
    top=ceil(1/tau)+8
    u=PI1*K/((K-1)*A)
    t=expu(Ah**2/(2*K*C*C))
    rho=F(0); s=F(0)
    for j in range(1,top):
        nearest=min(max(F(1),j*tau),j*u)
        rho+=1/expl((K-1)*rate(nearest))
        s+=1/(j*expl(K*rate(max(F(1),j*tau))))
    q=top*tau
    rem=1/expl((K-1)*rate(q))/(1-1/expl((K-1)*tau*(1-1/q)))
    peak=sqrtlo(2*PI0*(K-1))
    eta=rup(PI1*t*(rho+rem)/peak)
    phase=Ah/(K*C)+eta
    if phase>=1:
        return None
    h=rup(s+rem/top+eta)
    amp=2*A/(PI1*expu(h))
    return 1-phase**2/2,amp,eta,tau,t,peak

def margin(N,l,X,A,Ah,k0=None,k1=None,low=True):
    l=l if isinstance(l,F) else F(l); X=F(X); A=F(A); Ah=F(Ah)
    K=max(ceil(N/X),k0 or 0)
    if low:
        implied = int(X*Ah*Ah/F(6,5))
        k1 = implied if k1 is None else min(k1,implied)
    if k1 is not None and K>k1:
        return F(10)
    N=max(N,ceil(K*l))
    E=min(96,(K-1)//2)
    U=max(F(6,5),l*A*A/k1 if k1 else F(0))
    cap=max(ceil((B+1)*X),B*65) if low else ceil((B+1)*X)
    lag=mass(U/X,E)/(A*l)
    if low:
        res=residue(K,A,Ah)
        if res is None: return F(-10)
        cosine,amp,eta,tau,tilt,peak=res
        extra=end_tail(K,E,l,X,A,U,cap)
        if extra>amp/2:
            return -extra
        if tau>=F(5,4):
            delta=rate(tau)
            if K*delta>=1:
                # k/s ratio fixed at tau gives monotonic s exp(-rate)
                # for tau>1+1/(K-1), and k exp(-(k-1)*delta) decreases beyond K.
                assert tau>1+F(1,K-1)
                lag=min(lag,tilt*K*tau/(peak*expl((K-1)*delta)*(1-1/expl((K-1)*tau*(1-1/tau)))*A*l))
        v,z,ep,er=costs(N,K,E,l,X,A,U,cap,True)
        return cosine-(1/(A*l)+eta/U)-lag-(v+ep+extra+lag*(z+er+extra))/amp
    v,z,_,_=costs(N,K,E,l,X,A,U,cap,False)
    col,tt,tf=lattice(U,E)
    w=sum(v for p,v in zip(POLES,col) if abs(p)>1)+tt
    d=sum(abs(p)*v for p,v in zip(POLES,col) if abs(p)>1)+tf
    vt=(w+d)*H/G
    return 2*DLOW-vt-v-lag*(z+H*mass((1-1/l)*U,E))

def constants():
    def atan(x):
        s=sum((-1)**j*x**(2*j+1)/(2*j+1) for j in range(20))
        return s,s+x**41/41
    a,b=atan(F(1,5));c,d=atan(F(1,239))
    assert PI0<=16*a-4*d and 16*b-4*c<=PI1
    assert expl(H-F(1,22))>1/H
    lg0,lg1=log(F(2))
    assert 1+lg1+(1+H)/22<3*H
    assert F(1,2)+(lg0-F(1,2))/4>DLOW
    assert 1+lg0+F(1,2)>4*DLOW
