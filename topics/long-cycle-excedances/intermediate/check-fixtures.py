"""Exact rational replay of selected angular gaps, with independently generated prefixes."""
from math import comb

from flint import fmpq, fmpz_poly

from check import WIDTH, bracket, errors, phase_point, poly
from entrance import entrance


def eulerian(m):
    return fmpz_poly([
        sum((-1)**j*comb(m+1,j)*(p-j)**m for j in range(p))
        for p in range(1,min(m,WIDTH)+1)
    ])


def rows(k,last):
    single=eulerian(k-1)
    row={k:single}
    for n in range(k,last):
        lag=(single.mul_low(row[n+1-k],WIDTH-1)*comb(n,k-1)
             if n+1-k>=k else fmpz_poly())
        old=row[n]
        row[n+1]=fmpz_poly([
            (j+1)*old[j]+((n-j)*old[j-1]+lag[j-1] if j else 0)
            for j in range(WIDTH)
        ])
    return row[last-1],row[last]


def dyadic(x):
    m,e=map(int,x.man_exp())
    return fmpq(m<<e) if e>=0 else fmpq(m,1<<-e)


def horner_interval(row,lo,hi):
    lower=upper=fmpq(0)
    for j,c in reversed(list(enumerate(row))):
        items=[lower*lo,lower*hi,upper*lo,upper*hi]
        if j%2:
            c=-c
        lower=min(items)+c
        upper=max(items)+c
    return lower,upper


def tail(n,b):
    ratio=b*fmpq(WIDTH+2,WIDTH+1)**n
    assert ratio<1
    return fmpq((WIDTH+1)**n)*b**WIDTH/(1-ratio)


def signed(bounds,sgn,error):
    lo,hi=bounds
    return lo>error if sgn==1 else hi<-error


tests=0
for n,k in ((251,13),(421,67),(751,38),(999,99),(1000,51)):
    source,following=rows(k,n+1)
    old,new=poly(source),poly(following)
    der=old.derivative()
    H,J=entrance(n,k)
    for j in range(H+1,J):
        s=(-1)**(j+1)
        found,_=bracket(old,der,new,phase_point(n,j).upper(),
                        phase_point(n,j+1).lower(),(s,-s),errors(n,j+1))
        assert found is not None
        a,b=map(dyadic,found)
        assert a<b
        assert signed(horner_interval(source,a,a),s,tail(n,a))
        assert signed(horner_interval(source,b,b),-s,tail(n,b))
        assert signed(horner_interval(following,a,b),-s,tail(n+1,b))
        tests+=1
    print(n,k,J-H-1,flush=True)
print(f"Exact rational arithmetic independently confirmed all {tests} fixture gaps.")
