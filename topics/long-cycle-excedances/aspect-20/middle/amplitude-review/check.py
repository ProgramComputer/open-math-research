"""Independent amplitude upper bounds for the short-cycle contour."""
from fractions import Fraction as Q
from time import perf_counter

from flint import arb, ctx

ctx.prec=104
PI=arb.pi()
ONE=arb(1)
NMAX=9999
NMIN=251
ASPECT=20
BINS=3
TARGET_DENOMINATOR=4000


def a(q):
    q=Q(q)
    return arb(q.numerator)/q.denominator


def coefficients(lo,hi,d):
    """Absolute Taylor coefficient majorants in units r^j."""
    u,v=a(lo),a(hi)
    r=(v*v+PI*PI).sqrt()
    fractions=[r/(v*v+(p*PI)**2).sqrt() for p in range(1,48,2)]
    powers=[z*z for z in fractions]
    tail2=r*r/(94*PI**2)
    tail=tail2
    bounds=[arb(0),r/(1+u.exp())]
    if lo>=3:
        threshold=Q(2*d,1)/lo
        last=threshold.__ceil__()+1
        assert last*lo>=2*d
        factors=[b*r for b in range(1,last+1)]
        # j=1, to be updated cumulatively to j>=2.
        series=[(-b*u).exp()*r for b in range(1,last+1)]
        geometric=1/(1-(-u/2).exp())
    else:
        series=None
    for j in range(2,d+1):
        pole=2*(sum(powers)+tail)/j
        if series is not None:
            series=[term*factor/j for term,factor in zip(series,factors)]
            poisson=sum(series[:-1])+series[-1]*geometric
            bounds.append(pole if pole<poisson else poisson)
        else:
            bounds.append(pole)
        powers=[p*z for p,z in zip(powers,fractions)]
        tail*=fractions[-1]
    return r,bounds


def cover(k0,k1):
    # Deliberately different groups from the proposed proof.
    lows=[]
    while k0<=k1:
        high=min(k1,k0+k0//24)
        lows.append((k0,high))
        k0=high+1
    assert [(k,l) for k,l in lows]
    return lows


def groups(k0,k1):
    result=[]
    for K,L in cover(k0,k1):
        # Powers increase with j and decrease with k.
        w=1+arb(3)/K
        power=w
        weights=[]
        for j in range(1,L):
            weights.append(1+power)
            power*=w
        result.append((K,L,weights))
    return result


def error(lo,r,bounds,group,first):
    K,L,weights=group
    radial_p=1+8*(PI/r)**2
    if radial_p > (1+arb(4)/K)**2:
        shift=arb(3)
        pref=max((3*r*r/PI).upper(),(arb(3)/2*L*r/PI).upper())
    else:
        shift=arb(27)/10
        count=2+(1+arb(3)/K)*r/(2*PI)
        pref=max((3*r*r/PI).upper(),(10*L*r/PI*count).upper())
    lb=max(arb(first), (1+(a(lo)/PI)**2).lower())
    penalty=max((lb*(1+shift/L).log()).lower(),
                (ASPECT*K*(1+shift/K).log()).lower())
    amplitude=sum(b*w for b,w in zip(bounds[1:L],weights))
    return pref.log()+amplitude-penalty


def audit():
    started=perf_counter()
    kmax=NMAX//ASPECT
    threshold_groups=groups(4,kmax)
    covered=[k for K,L,_ in threshold_groups for k in range(K,L+1)]
    assert covered==list(range(4,kmax+1))
    small_groups=groups(4,NMIN//ASPECT)
    checked=boundary=0
    log_target=-arb(TARGET_DENOMINATOR).log()
    worst=None
    for i in range(315*BINS):
        lo,hi=Q(i,BINS),Q(i+1,BINS)
        r,bounds=coefficients(lo,hi,kmax-1)
        for group in threshold_groups:
            v=error(lo,r,bounds,group,NMIN)
            if not v < log_target:
                raise ArithmeticError((lo,hi,group[:2],v))
            worst=v.upper() if worst is None else max(worst,v.upper())
            checked+=1
        if (1+(a(lo)/PI)**2).lower()<=NMIN:
            for group in small_groups:
                v=error(lo,r,bounds,group,NMIN)
                if not v < log_target:
                    raise ArithmeticError(("n=251",lo,hi,group[:2],v))
                boundary+=1
    print(f"Independent replay: {len(threshold_groups)} k groups, "
          f"{checked} continuous boxes, all normalized errors < S/{TARGET_DENOMINATOR}.")
    print(f"Checked n=251 separately for k=4..12 in {boundary} count-height boxes.")
    print(f"Maximum recorded log bound {worst}. Runtime {perf_counter()-started:.2f}s.")


if __name__=="__main__":
    audit()
