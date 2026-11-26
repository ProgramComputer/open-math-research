"""Exact finite-dimension cutoff from all simple proper binomial sections.

Python 3.10+; SymPy finds rational probes, and Fraction arithmetic certifies
every sign and margin. The JSON certificate can be replayed without SymPy.
"""
import argparse
from fractions import Fraction
import json
from math import comb
from pathlib import Path


def evaluate(coeffs,x):
    result=0
    for a in coeffs:
        result=result*x+a
    return result


def probe_bound(n, s, m, probes):
    """Check alternating signs for both reversed endpoints of degree m."""
    if len(probes)!=m-1 or probes!=sorted(set(probes)):
        raise ValueError("wrong number or order of rational probes")
    h=[comb(n,k)**s for k in range(m+1)]
    largest=Fraction(0)
    for i,x in enumerate(probes):
        required=(-1)**(m-1-i)
        low=evaluate(h[:-1]+[0],x)
        high=low+h[-1]
        if min(required*low,required*high)<=0:
            raise ValueError("wrong endpoint sign")
        error_scale=evaluate(h[:-1]+[0],abs(x))
        largest=max(largest,Fraction(n*error_scale,min(abs(low),abs(high))))
    return largest


def verify(record):
    n=record['n']
    s=record['retained']
    if n<2 or s<1:
        raise ValueError("need n>=2 and a positive integral retained exponent")
    if set(record['probes'])!={str(m) for m in range(2,n)}:
        raise ValueError("incomplete degrees")
    bound=max([Fraction(0)]+[probe_bound(n,s,m,[Fraction(x) for x in record['probes'][str(m)]])
                             for m in range(2,n)])
    cutoff=record['dimension_cutoff']
    if cutoff<1 or 2**(2*cutoff//(n*n))<=bound:
        raise ValueError("insufficient dimension cutoff")
    return bound


def construct(n,s):
    import sympy as sp
    X=sp.Symbol('x')
    by_degree={}
    bound=Fraction(0)
    for m in range(2,n):
        h=[comb(n,k)**s for k in range(m+1)]
        hi=sp.Poly.from_list(h,gens=X)
        lo=hi-hi.TC()
        for endpoint in (lo,hi):
            if endpoint.gcd(endpoint.diff()).degree() or endpoint.count_roots(-sp.oo,sp.oo)!=m:
                raise ValueError(f"degree {m} endpoint is not simple real-rooted")
        derivative=hi.diff()
        bits=4
        while True:
            intervals=derivative.intervals(eps=sp.Rational(1,2**bits))
            probes=[Fraction(int(v.p),int(v.q)) for (a,b),multiplicity in intervals for v in [(a+b)/2]]
            try:
                degree_bound=probe_bound(n,s,m,probes)
            except ValueError:
                bits*=2
                continue
            break
        bound=max(bound,degree_bound)
        by_degree[str(m)]=[str(x) for x in probes]
    exponent=0
    while 2**exponent<=bound:
        exponent+=1
    cutoff=max(1,(n*n*exponent+1)//2)
    record=dict(n=n,retained=s,dimension_cutoff=cutoff,probes=by_degree)
    verify(record)
    return record


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n',nargs='?',type=int)
    parser.add_argument('s',nargs='?',type=int)
    parser.add_argument('--verify',type=Path)
    opts=parser.parse_args()
    if opts.verify:
        for line in opts.verify.read_text().splitlines():
            row=json.loads(line)
            verify(row)
            print('verified',row['n'],row['retained'],row['dimension_cutoff'])
    elif opts.n is not None and opts.s is not None and opts.n>=2 and opts.s>=1:
        print(json.dumps(construct(opts.n,opts.s),separators=(',',':')))
    else:
        parser.error("give n>=2 and s>=1, or --verify a JSONL archive")
