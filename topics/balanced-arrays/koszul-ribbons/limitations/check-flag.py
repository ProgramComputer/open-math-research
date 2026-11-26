"""Exact top-quota certificate for identical pure flag row constraints.

The 9 columns are three ordinary vertices of a triangle plus the six vertices
of a wheel with a five-cycle rim. Every labeled row is a clique in that graph.
Requires Python 3.9+ and the standard library only.
"""
from fractions import Fraction
from itertools import combinations
from math import comb, factorial, prod
from functools import cache


@cache
def factorial_ratio(a,b):
    """Compute a!/b! using only the factors between the two arguments."""
    if a < b:
        return Fraction(1,prod(range(a+1,b+1)))
    return Fraction(prod(range(b+1,a+1)))


def compositions(total, slots):
    if slots == 1:
        yield (total,)
        return
    for first in range(total+1):
        for tail in compositions(total-first, slots-1):
            yield (first,)+tail


def normalized(t, j):
    """a_(2t-j)/a_(2t) at n=7t, for j=0,1,2."""
    k=2*t-j
    answer=Fraction(0)
    for s in range((5*k+1)//2, min(5*k,7*t-k)+1):
        h=2*s-5*k
        b=7*t-s
        # z is the number of hub cells in rim-empty rows. Those rows must
        # omit all ordinary vertices; all other rim-empty rows may use them.
        hub_bulk=Fraction(0)
        for z in range(min(b-k,k)+1):
            if k-z>s:
                continue
            hub_ratio=(factorial_ratio(s,5*t)*factorial_ratio(2*t,k-z)
                       *factorial_ratio(3*t,s-k+z))
            hub_bulk+=comb(b,z)*hub_ratio*comb(b-z,b-z-k)**3
        for singles in compositions(h,5):
            margins=[k-value for value in singles]
            if min(margins)<0:
                continue
            doubled=[sum((-1)**a*margins[(i-a)%5] for a in range(5)) for i in range(5)]
            if min(doubled)<0 or any(value%2 for value in doubled):
                continue
            pair_counts=[value//2 for value in doubled]
            assignments=factorial_ratio(2*t,b)
            for edges,vertices in zip(pair_counts,singles):
                assignments*=factorial_ratio(t,edges)/factorial(vertices)
            answer+=assignments*hub_bulk
    return answer


def tiny_labeled(quota):
    """Add each of seven labeled rows by directly enumerating cliques."""
    graph_edges=set(combinations(range(3),2))
    graph_edges.update(tuple(sorted((3+i,3+(i+1)%5))) for i in range(5))
    graph_edges.update((3+i,8) for i in range(5))
    cliques=[choice for k in range(4) for choice in combinations(range(9),k)
             if all(edge in graph_edges for edge in combinations(choice,2))]
    # Base-8 packing implements nine exact column-margin counters.
    masks=[(sum(1<<(3*i) for i in row), row) for row in cliques]
    layer={0:1}
    for completed in range(7):
        following={}
        for state,count in layer.items():
            for mask,row in masks:
                if any((state>>(3*i))&7==quota for i in row):
                    continue
                target=state+mask
                if completed+1==7 and target!=sum(quota<<(3*i) for i in range(9)):
                    continue
                following[target]=following.get(target,0)+count
        layer=following
    return layer.get(sum(quota<<(3*i) for i in range(9)),0)


if __name__=='__main__':
    tiny=[tiny_labeled(k) for k in range(3)]
    assert [Fraction(a,tiny[2]) for a in reversed(tiny)]==[normalized(1,j) for j in range(3)]
    print('seven-row labeled coefficient vector',tiny)
    for t in (100_000_000,):
        top,middle,bottom=(normalized(t,j) for j in range(3))
        ratio=middle**2/(top*bottom)
        if ratio<Fraction(9,10):
            print('rows',7*t,'columns',9,'middle quota',2*t-1)
            print('ratio numerator',ratio.numerator)
            print('ratio denominator',ratio.denominator)
            print('ratio below 9/10',10*ratio.numerator<9*ratio.denominator)
            break
    else:
        raise ArithmeticError('no certificate in the selected range')
