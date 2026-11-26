"""Exact outer-rank checks for consecutive ordered-partition rows."""
from fractions import Fraction
from math import comb
from functools import cache

@cache
def rows(j,nmax):
    seq=[[1]]
    for n in range(1,nmax+1):
        current=[0]*(1+n//j)
        for size in range(1,n+1):
            multiplicity=comb(n,size)
            shift=int(size>=j)
            for p,c in enumerate(seq[n-size]):
                current[p+shift]+=multiplicity*c
        seq.append(current)
    return seq

def value(v,y,sign=False):
    a,b=y.as_integer_ratio()
    m=len(v)-1
    # Clear the positive denominator b**m.
    return sum(c*((-a if sign else a)**i)*b**(m-i) for i,c in enumerate(v))

def dominance(v,y,h):
    m=len(v)-1
    a,b=y.as_integer_ratio()
    return 2*v[h]*a**h*b**(m-h)>value(v,y)

def intervals(row,count):
    v=row[::-1]
    windows=[]
    for h in range(count):
        center=Fraction(v[h],v[h+1])
        lo,hi=center/2,center*2
        if not (dominance(v,lo,h) and dominance(v,hi,h+1)):return None
        # Rouché gives exactly h and h+1 interior roots in these disks.
        for i in range(24):
            mid=(lo+hi)/2
            z=value(v,mid,True)*(-1)**h
            if z>0:lo=mid
            elif z<0:hi=mid
            else:lo=hi=mid;break
        windows.append((lo,hi))
    return windows

def check(j,m,s,count):
    n=m*j+s
    r=rows(j,(m+1)*j+1)
    f=intervals(r[n],count+1)
    g=intervals(r[n+1],count+1)
    if f is None or g is None:
        return "inconclusive"
    comparisons = []
    for h in range(count):
        if s+1<j:
            comparisons.extend(((f[h],g[h]),(g[h],f[h+1])))
        else:
            comparisons.extend(((g[h],f[h]),(f[h],g[h+1])))
    if any(left[0] >= right[1] for left,right in comparisons):
        raise ArithmeticError((j,m,s,count,"certified order failure"))
    if any(left[1] >= right[0] for left,right in comparisons):
        return "inconclusive"
    return "verified"

if __name__=='__main__':
    if not __debug__:raise SystemExit('Run with assertions enabled.')
    for j,m in [(12,7),(24,8),(32,12),(35,21)]:
        sample=sorted({0,1,j//3,j//2,j-2,j-1})
        for s in sample:
            print(j,m,s,'first rank:',check(j,m,s,1),'first two:',check(j,m,s,2),flush=True)
