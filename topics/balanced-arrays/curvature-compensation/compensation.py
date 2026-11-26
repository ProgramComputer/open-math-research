"""Sufficient strict alternating signs using the second neighbor on each side."""
from fractions import Fraction as F
from math import comb,isqrt


def invsqrt_upper(q):
    denominator=2**32
    upper=isqrt(denominator**2*q.denominator//q.numerator)+1
    return F(upper,denominator)


def probabilities(n,d,r):
    lower=[];upper=[]
    for k in range(n*r//d+1):
        tail=F(sum(comb(d,j)*k**j*(n-k)**(d-j) for j in range(r+1,d+1)),n**d)
        lower.append(max(F(0),1-n*tail))
        upper.append((1-tail)**n)
    return lower,upper


def signs(n,d,r,limits=None):
    low,high=limits if limits is not None else probabilities(n,d,r)
    D=len(low)-1
    lower={}; upper={}
    for k in range(1,D):
        base=F((k+1)*(n-k+1),k*(n-k))**d
        lower[k]=max(base,base*low[k]**2/(high[k-1]*high[k+1]))
        upper[k]=(base*high[k]**2/(low[k-1]*low[k+1]) if low[k-1]*low[k+1]>0 else None)
    labels=[]
    for k in range(1,D):
        if lower[k]>4:
            labels.append('separation');continue
        tau=invsqrt_upper(lower[k])
        C=F(0)
        for e in (-1,1):
            if not 0<=k+2*e<=D or upper[k+e] is None:
                continue
            next_loss=tau/(lower[k+e]*lower[k+2*e]) if 0<=k+3*e<=D else F(0)
            C+=(1-next_loss)/upper[k+e]
        bound=1-2*tau+C*tau*tau if C*tau<=1 else 1-1/C
        labels.append('compensation' if bound>0 else 'inconclusive')
    return labels

if __name__ == "__main__":
    labels = signs(36, 12, 10)
    assert len(labels) == 29 and "inconclusive" not in labels
    compensated = [k for k, label in enumerate(labels, 1) if label == "compensation"]
    assert compensated == list(range(14, 23))
    print("(36,10,12): 29 alternating signs,", len(compensated), "by compensation")
