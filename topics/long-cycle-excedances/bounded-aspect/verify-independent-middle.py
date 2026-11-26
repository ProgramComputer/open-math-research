"""Independent exact lattice and FLINT convolution replay for the middle slabs."""
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial, isqrt
from multiprocessing import Pool

from flint import fmpz_poly

GRID = 1 << 52
P = 55
POLES = tuple(range(-P,P+1,2))
BASE = Q(6,5)
D0 = Q(547,1000)


def up(x):
    return (x*GRID).__ceil__()


def down(x):
    return Q((x*GRID).__floor__(),GRID)


def ceildiv(a,b):
    return (a+b-1)//b


def sqrt_lower(x):
    return Q(isqrt((x*GRID**2).__floor__()),GRID)


def exp_interval(y):
    assert y >= 0
    x = Q(y)
    doublings = 0
    while x > 1:
        x /= 2
        doublings += 1
    term = total = Q(1)
    for j in range(1,43):
        term *= x/j
        total += term
    rem = term*x/43/(1-x/44)
    lo,hi = down(total),Q(up(total+rem),GRID)
    for _ in range(doublings):
        lo,hi = down(lo*lo),Q(up(hi*hi),GRID)
    return lo,hi


def log_interval(x):
    if x<1:
        a,b=log_interval(1/x)
        return -b,-a
    j=0
    while x>2:
        x/=2
        j+=1

    def atanh(y):
        low=2*sum((y**(2*i+1)/(2*i+1) for i in range(28)),Q(0))
        high=low+2*y**57/(57*(1-y*y))
        return low,high

    l0,h0=atanh((x-1)/(x+1))
    l2,h2=atanh(Q(1,3))
    return down(l0+j*l2),Q(up(h0+j*h2),GRID)


def rate(x):
    return max(0,x-1-log_interval(x)[1])


def atan_interval(x):
    low=sum(((-1)**j*x**(2*j+1)/(2*j+1) for j in range(22)),Q(0))
    return low,low+x**45/45


a,b=atan_interval(Q(1,5))
c,d=atan_interval(Q(1,239))
PI_L,PI_H=down(16*a-4*d),Q(up(16*b-4*c),GRID)


@lru_cache(None)
def lattice(d,E):
    c=d/(2*E)
    assert (2*E-1)*c*P*P>1-c
    terms=tuple(up((1+c*(p*p-1))**(-E)) for p in POLES)
    tail=up((1+c*(P*P-1))**(1-E)/(2*c*(E-1)))
    return terms,ceildiv(tail,P),tail


@lru_cache(None)
def mass(d,E):
    w,z,_=lattice(d,E)
    return Q(sum(w)+z,GRID)


@lru_cache(None)
def stars(d,E):
    w,z,f=lattice(d,E)
    best=(0,0)
    for a in range(1,P+3,2):
        row=tuple((v,abs(p)*v,abs(a-p)) for p,v in zip(POLES,w) if p!=a)
        best=(max(best[0],sum(ceildiv(v,gap) for v,_,gap in row)),
              max(best[1],sum(ceildiv(dv,gap) for _,dv,gap in row)))
    return Q(best[0]+ceildiv(z,2),GRID),Q(best[1]+ceildiv(f,2),GRID)


def primitive_mass(i,k,B):
    if i==B:
        return Q(1),Q(1)
    lo=Q(i-1,B)
    block=(i-1)//B
    if block==1:
        m=1/(lo-Q(1,k))-Q(B,i)
        return lo,m+(Q(1,4*k) if i==2*B else 0)
    return lo,(Q(1,B)+Q(1,k))/(2*factorial(block))


def exp_poly(grid,B):
    q=[GRID]
    for b in range(1,len(grid)):
        q.append(ceildiv(sum(i*grid[i]*q[b-i] for i in range(B,b+1)),b*GRID))
    return fmpz_poly(q)


def product(p,q,cap):
    # FLINT's native exact polynomial multiplication, followed by directed rounding.
    return fmpz_poly([ceildiv(int(v),GRID) for v in p.mul_low(q,cap+1)])


def envelopes(k,E,l,X,A,U,B,cap,distinct):
    L=[0]*(cap+1)
    D=L.copy()
    LT=L.copy()
    DT=L.copy()
    LQ=[L.copy() for _ in POLES]
    DQ=[L.copy() for _ in POLES]
    for i in range(B,cap+1):
        lo,m=primitive_mass(i,k,B)
        d=(lo-Q(1,k))*U/X
        st,dst=stars(d,E)
        w,z,f=lattice(d,E)
        L[i]=up(m*st/A)
        D[i]=up(m*(Q(i,B)*dst/(l*A)+st/(k*U)))
        if distinct:
            LT[i]=up(m*Q(z,2*GRID)/A)
            DT[i]=up(m*(Q(i,B)*Q(f,2*GRID)/(l*A)+Q(z,2*GRID)/(k*U)))
            for j,p in enumerate(POLES):
                LQ[j][i]=up(m*Q(w[j],GRID)/A)
                DQ[j][i]=up(m*Q(w[j],GRID)*(Q(i,B)*abs(p)/(l*A)+1/(k*U)))
    out=exp_poly(L,B)
    yield None,out,product(out,fmpz_poly(D),cap)
    if not distinct:
        return
    tail=exp_poly(LT,B)
    dt=product(tail,fmpz_poly(DT),cap)
    for a in range(1,P+1,2):
        q,dq=tail,dt
        for p,Lp,Dp in zip(POLES,LQ,DQ):
            if p==a:
                continue
            gap=abs(p-a)
            factor=fmpz_poly([GRID]+[ceildiv(i,gap) for i in Lp[1:]])
            d_factor=fmpz_poly([ceildiv(i,gap) for i in Dp])
            dq=product(dq,factor,cap)+product(q,d_factor,cap)
            q=product(q,factor,cap)
        yield a,q,dq


def difference(g,H):
    if g<1:
        return H
    if g<2:
        return 1-D0
    i=min(40,g.__floor__())
    return min(H-(Q(1,2) if i==2 else D0),Q(i+1,2*i*factorial(i)))


def main_cost(N,K,E,l,X,A,U,B,cap,low,H,distinct):
    # Resolve distinguished degree and the attainable kernel before summing poles.
    cells=[]
    errors=[]
    for b in range(cap+1):
        h=Q(b,B)
        g=max(1,Q(b,B+1)) if b else 0
        if low:
            errors.append((difference(l-h,H),difference(l-h-1,H),max(1,h/l-1)))
        if g+1>X or (not low and not b):
            continue
        y=max(1/X,1-h/l)
        ym=max(1/X,1-(h+1)/l)
        en=max(E,min(96,(N*y).__floor__()//2)) if distinct else E
        em=max(E,min(96,(N*ym).__floor__()//2)) if distinct else E
        cells.append((b,y*U,ym*U,1-g/X,en,em,H if l-h>=2 else Q(1),
                      H if l-1-h>=2 else Q(1)))
    v=z=eo=er=Q(0)
    sqrtN=isqrt(N)
    for a,q,dq in envelopes(K,E,l,X,A,U,B,cap,distinct):
        if a==1 and low:
            for b,(e0,e1,zexp) in enumerate(errors):
                eo+=2*e0*(int(q[b])*zexp+int(dq[b]))/GRID
                er+=2*e1*int(q[b])/GRID
            continue
        for b,dl,dm,yp,en,em,w,wm in cells:
            q0,dq0=int(q[b]),int(dq[b])
            if not (q0 or dq0):
                continue
            old,old0,old1=lattice(dl,en)
            res,res0,_=lattice(dm,em)
            half,_,half1=lattice(dl/2,en//2)
            if a is None and distinct:
                diag,off,od,lag=old1,Q(half1,sqrtN),old0,res0
            elif a is None:
                diag=sum(v*max(1,yp*abs(p)) for p,v in zip(POLES,old))+old1
                off=Q(sum(abs(p)*v for p,v in zip(POLES,half) if abs(p)>1)+half1,sqrtN)
                od,lag=sum(old)+old0,sum(res)+res0
            else:
                i=(a+P)//2
                diag=2*old[i]*max(1,yp*a)
                off=Q(2*a*half[i],sqrtN) if a!=1 else 0
                od,lag=2*old[i],2*res[i]
            v+=w*(q0*(diag+off)+dq0*od)/GRID**2
            z+=wm*q0*lag/GRID**2
    return v,z,eo,er


def carrier(K,A,Ah):
    cos_lo=sqrt_lower(1-(Ah/K)**2)
    tau=PI_L*cos_lo/Ah
    r_hi=PI_H*K/((K-1)*A)
    vertical=exp_interval(Ah**2/(2*K*cos_lo*cos_lo))[1]
    peak_lo=sqrt_lower(2*PI_L*(K-1))
    J=(1/tau).__ceil__()+8
    gamma=real_H=Q(0)
    for j in range(1,J):
        near=min(max(1,j*tau),j*r_hi)
        gamma+=1/exp_interval((K-1)*rate(near))[0]
        real_H+=1/(j*exp_interval(K*rate(max(1,j*tau)))[0])
    htau=J*tau
    remain=1/(exp_interval((K-1)*rate(htau))[0]
              *(1-1/exp_interval((K-1)*tau*(1-1/htau))[0]))
    eta=PI_H*vertical*(gamma+remain)/peak_lo
    phase=Ah/(K*cos_lo)+eta
    assert phase<1
    amp=2*A/(PI_H*exp_interval(real_H+remain/J+eta)[1])
    return 1-phase**2/2,amp,eta,tau,vertical,peak_lo


def tail(K,E,l,X,A,U,B,cap,H):
    lam=Q(11,10)
    t=lam**B
    scalar,first=stars((1-Q(1,K))*U/X,E)
    # Whole actual blocks, independent of the finite bin envelope.
    m=Q(1,2)+Q(1,4*K)
    e=exp_interval(t)[1]
    zeroth=t+m*t*(e-1)
    moment=t+m*t*((1+t)*e-1)
    L=zeroth*scalar/A
    derivative=moment*first/(l*A)+zeroth*scalar/(K*U)
    return 2*H*lam**(-cap-1)*exp_interval(L)[1]*(1+moment*scalar/(A*l)+derivative)


def evaluate(spec):
    N,l,X,A,Ah,klo,khi,low,H,distinct=spec
    K=max((N/X).__ceil__(),klo or 0)
    if low:
        implied=(X*Ah*Ah/BASE).__floor__()
        khi=min(implied,khi) if khi is not None else implied
    if khi is not None and K>khi:
        return None
    assert K>=13
    N=max(N,(K*l).__ceil__())
    U=max(BASE,l*A*A/khi if khi else 0)
    E=min(96,(K-1)//2) if distinct else (K-1)//2
    B=8 if distinct else 4
    cap=max(((B+1)*X).__ceil__(),65*B if low else 0)
    lag=mass(U/X,E)/(A*l)
    v,z,eo,er=main_cost(N,K,E,l,X,A,U,B,cap,low,H,distinct)
    if low:
        direction,amp,eta,tau,vertical,peak=carrier(K,A,Ah)
        extra=tail(K,E,l,X,A,U,B,cap,H)
        assert extra<amp/2
        if tau>=Q(5,4) and K*rate(tau)>=1:
            assert tau>1+Q(1,K-1)
            slope=exp_interval((K-1)*(tau-1))[0]
            geometric=exp_interval((K-1)*rate(tau))[0]*(1-1/slope)
            lag=min(lag,vertical*K*tau/(peak*geometric*A*l))
        return direction-1/(A*l)-eta/U-lag-(v+eo+extra+lag*(z+er+extra))/amp

    terms,z0,z1=lattice(U,E)
    d0=sum(v for p,v in zip(POLES,terms) if abs(p)>1)+z0
    d1=sum(abs(p)*v for p,v in zip(POLES,terms) if abs(p)>1)+z1
    if distinct:
        single=H*Q(d0+d1,GRID)
    else:
        single=Q(38,1000)
        assert H*H*Q(d0*d0+d1*d1,GRID**2)<single**2
    return 2*D0-single-v-lag*(z+H*mass((1-1/l)*U,E))


def runs():
    for i in range(16,30):
        l,X=Q(i,4),Q(i+1,4)
        A=Q(isqrt((10000*BASE*1000/(X*X)).__floor__()),100)
        yield 'narrow', (1000,l,X,A,A,None,None,False,Q(4,7),False)
    rows=((Q(15,2),Q(10),Q(9,2),Q(5)),
          (Q(10),Q(14),Q(9,2),Q(11,2)),
          (Q(14),Q(18),Q(4),Q(11,2)),
          (Q(18),Q(20),Q(4),Q(11,2)))
    for l,X,a,b in rows:
        for pivot,klo,khi in ((a,None,100),(b,100,None)):
            yield '1000-high',(1000,l,X,pivot,pivot,klo,khi,False,Q(59,100),True)
            bound=max(BASE*1000/X**2,BASE*(klo or 0)/X)
            p=Q(isqrt((10000*bound).__floor__()),100)
            while p<pivot:
                q=min(pivot,Q((2*p).__floor__()+1,2))
                assert p<q
                yield '1000-low',(1000,l,X,p,q,klo,khi,True,Q(59,100),True)
                p=q
    for l,X,a,b in ((4,Q(15,2),7,7),(Q(15,2),10,5,5),(10,14,5,6),
                    (14,18,5,6),(18,20,5,6)):
        for pivot,klo,khi in ((a,None,100),(b,100,None)):
            yield '251-high',(251,Q(l),Q(X),Q(pivot),Q(pivot),klo,khi,False,Q(61,100),True)


def check(item):
    label,s=item
    result=evaluate(s)
    if result is None:
        return label,s,None
    assert result>0,(label,s,result)
    return label,s,(result*10**6).__floor__()


if __name__=='__main__':
    assert __debug__
    for h,K in ((Q(4,7),100),(Q(59,100),22),(Q(61,100),13)):
        assert log_interval(1/h)[1]+Q(1,K)<h
        assert 1+log_interval(Q(2))[1]+(1+h)/K<3*h
    assert 1+log_interval(Q(2))[0]+Q(1,2)>4*D0
    assert Q(1,2)+(log_interval(Q(2))[0]-Q(1,2))/4>D0
    minima={}
    counts={}
    rows=list(runs())
    with Pool(4) as pool:
        for label,s,margin in pool.imap(check,rows):
            print(label,*s[1:7],margin,flush=True)
            if margin is not None:
                minima[label]=min(minima.get(label,10**12),margin)
                counts[label]=counts.get(label,0)+1
    for label,margin in minima.items():
        print(label,counts[label],margin,flush=True)
