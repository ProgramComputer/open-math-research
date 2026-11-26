"""Uniform-in-n exact alternating-series lower-edge certificates for U(2,4)."""
import argparse
import json
from math import ceil, comb, factorial, perm
from functools import cache
from flint import arb, ctx, fmpz_poly


@cache
def edge_counts(k):
    old = [1]
    for color in range(4):
        vertices = color*k
        new = [0] * ((vertices+k)//2 + 1)
        for edges, count in enumerate(old):
            if count:
                free = vertices-2*edges
                for i in range(min(free,k)+1):
                    new[edges+i] += count*comb(free,i)*perm(k,i)
        old = new
    return old


def grid(j):
    if j<1:
        raise ValueError("positive phase index required")
    root_two = arb(2).sqrt()
    y = (j + arb(3)/8)*arb.pi()/(2*root_two)
    def nearest(x):
        return int((x+arb(1)/2).floor().unique_fmpz())
    return nearest(16*y), nearest(16*y/root_two)


def certify(j, n0, m=None):
    y, shift = grid(j)
    if m is None:
        m = ceil(2.3*y/16 + 5)
    if m%2==j%2:
        m += 1
    # Positive sign needs a lower (odd) sum. Negative sign needs an upper (even) sum.
    if not (16*n0>shift and (m+1)*(16*n0-shift)>n0*y):
        raise ValueError("the tail need not alternate with decreasing magnitude")
    x = fmpz_poly([n0,1])
    den4 = (16*x-shift)**4
    scale = factorial(m)**4
    # Falling factorials at n=n0+X. Unlabeled token quotient is scaled only once.
    fall = [fmpz_poly([1])]
    for h in range(4*m):
        fall.append(fall[-1]*(x-h))
    acc = fmpz_poly([])
    for k in range(m+1):
        matching = edge_counts(k)
        row = sum((fall[4*k-e]*v for e,v in enumerate(matching) if v), fmpz_poly([]))
        acc = acc*den4 + row*((-1)**k * y**(4*k) * (scale//factorial(k)**4))
    sign = (-1)**j
    bad = [i for i,c in enumerate(acc) if sign*c<=0]
    return {"j":j,"n0":n0,"y16":y,"shift16":shift,"M":m,"degree":acc.degree(),
            "wrong_coefficients":len(bad),"first_wrong":bad[:2]}


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("n0",type=int)
    parser.add_argument("j",nargs="+",type=int)
    args=parser.parse_args()
    ctx.prec=128
    for j in args.j:
        print(json.dumps(certify(j,args.n0)),flush=True)
