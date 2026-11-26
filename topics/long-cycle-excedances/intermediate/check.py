"""Verify intermediate old and actual next signs between certified angular samples."""
from argparse import ArgumentParser
from functools import cache
from hashlib import sha256
from math import isqrt
from time import perf_counter

from flint import arb, arb_poly, ctx

from coefficients import eulerian, update, next_rows
from entrance import angle, entrance

ctx.prec=144
PI=arb.pi()
WIDTH=64


@cache
def phase_point(n,j):
    return (-PI*angle(n,j).cot()).exp()


@cache
def tail(n):
    return arb(WIDTH+1)**n,(arb(WIDTH+2)/(WIDTH+1))**n


@cache
def errors(n,j):
    """Separate rigorous uniform tail bounds for both rows up to phase j."""
    x=phase_point(n,j).upper()
    power=x**WIDTH
    vals=[]
    for real_n in (n,n+1):
        c,q=tail(real_n)
        if not x*q<1:
            raise ArithmeticError((n,j,"tail ratio"))
        vals.append((c*power/(1-x*q)).upper())
    return vals


def signed(poly,x,eps):
    y=poly(x)
    return 1 if y>eps else -1 if y < -eps else 0


def inside(poly,new,candidate,lo,hi,goals,eps):
    a=(candidate*(1-arb(1)/2**28)).lower()
    b=(candidate*(1+arb(1)/2**28)).upper()
    if not lo<a<b<hi or signed(new,a.union(b),eps[1])!=goals[1]:
        return None
    if signed(poly,a,eps[0])==goals[0] and signed(poly,b,eps[0])==-goals[0]:
        return a,b
    return None


def bracket(old,derivative,new,lo,hi,goals,eps):
    candidate=(lo*hi).sqrt().mid()
    for count in range(9):
        if count>=2:
            found=inside(old,new,candidate,lo,hi,goals,eps)
            if found is not None:
                return found,False
        d=derivative(candidate)
        if not d>0 and not d<0:
            break
        x=(candidate-old(candidate)/d).mid()
        if not lo<x<hi or x==candidate:
            break
        candidate=x

    low,high=lo,hi
    for i in range(100):
        if i>=4 and signed(new,low.union(high),eps[1])==goals[1]:
            return (low,high),True
        mid=((low+high)/2).mid()
        sign=signed(old,mid,eps[0])
        if sign==goals[0]:
            low=mid
        elif sign==-goals[0]:
            high=mid
        else:
            # Midpoint may be the exact root. Try a triple cut instead.
            lo1=((low+mid)/2).mid()
            hi1=((mid+high)/2).mid()
            left=signed(old,lo1,eps[0])
            right=signed(old,hi1,eps[0])
            if left==-goals[0]:
                high=lo1
            elif right==goals[0]:
                low=hi1
            elif left==goals[0] and right==-goals[0]:
                low,high=lo1,hi1
            else:
                break
    return None,True


def poly(row):
    return arb_poly([c if j%2==0 else -c for j,c in enumerate(row)])


def certify(n,k,old,new,digest):
    H,J=entrance(n,k)
    if H+1==J:
        return 0,0
    left=phase_point(n,H+1).upper()
    derivative=old.derivative()
    fallback=0
    initial=(-1)**H
    if signed(old,left,errors(n,H+2)[0])!=initial:
        raise ArithmeticError((n,k,H+1,"initial old sample"))
    for j in range(H+1,J):
        right=phase_point(n,j+1).lower()
        assert left<right,(n,k,j,"disjoint phase endpoints")
        err=errors(n,j+1)
        old_left=(-1)**(j+1)
        assert signed(old,right,err[0])==-old_left,(n,k,j,"right old sample")
        # Validate the true left candidate independently of the shorter preceding bound.
        assert signed(old,left,err[0])==old_left,(n,k,j,"left old sample")
        bounds,needed=bracket(old,derivative,new,left,right,(old_left,-old_left),err)
        if bounds is None:
            raise ArithmeticError((n,k,j,"no valid interval"))
        a,b=bounds
        digest.update(f"{n},{j},{a.man_exp()},{b.man_exp()}\n".encode())
        fallback+=needed
        left=phase_point(n,j+1).upper()
    return J-H-1,fallback


def run(n0,n1,k0,k1):
    start=perf_counter()
    new_max=n1+1
    cyc=eulerian(n1,WIDTH)
    rows={n:cyc[n-1] for n in range(new_max//2+1,new_max+1)}
    runs=ranks=used=fb=0
    switch=2*isqrt(n1)
    for k in range(new_max//2,k0-1,-1):
        lo=max(n0,4*k)
        hi=min(n1,20*k-1)
        if k>switch:
            update(rows,cyc,new_max,k,WIDTH)
        elif lo<=hi and k<=k1:
            rows=next_rows(k,new_max,cyc,WIDTH)
        if k>k1 or lo>hi:
            continue
        digest=sha256()
        old=poly(rows[lo])
        previous=(runs,ranks,used,fb)
        for n in range(lo,hi+1):
            new=poly(rows[n+1])
            r,f=certify(n,k,old,new,digest)
            runs+=1
            ranks+=r
            used+=(r>0)
            fb+=f
            old=new
        if k%5==0:
            print(f"k={k}: pairs {runs}; sampled {used}; ranks {ranks}; bisections {fb}; {perf_counter()-start:.2f}s",flush=True)
        print(f"digest k={k}: {digest.hexdigest()}, metrics {tuple(a-b for a,b in zip((runs,ranks,used,fb),previous))}",flush=True)
    print(f"TOTAL pairs={runs} sampled={used} ranks={ranks} bisections={fb} elapsed={perf_counter()-start:.3f}s")


if __name__=="__main__":
    parser=ArgumentParser(description=__doc__)
    parser.add_argument("nmin",type=int,default=251,nargs="?")
    parser.add_argument("nmax",type=int,default=1000,nargs="?")
    parser.add_argument("--kmin",type=int,default=7)
    parser.add_argument("--kmax",type=int,default=250)
    args=parser.parse_args()
    if not (251<=args.nmin<=args.nmax<=1000 and 7<=args.kmin<=args.kmax):
        parser.error("need 251 <= nmin <= nmax <= 1000 and 7 <= kmin <= kmax")
    if not __debug__:
        parser.error("run without -O")
    run(args.nmin,args.nmax,args.kmin,args.kmax)
