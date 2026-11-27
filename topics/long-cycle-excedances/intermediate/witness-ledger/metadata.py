"""Verify witness ledger coverage/order using only exact integer and rational arithmetic."""
import argparse
import hashlib
import json
import re
import sys
from fractions import Fraction
from functools import cache
from math import isqrt


def arctan_bounds(x, terms):
    s = sum((-1)**i * x**(2*i+1) / (2*i+1) for i in range(terms))
    t = s + (-1)**terms * x**(2*terms+1) / (2*terms+1)
    return min(s,t), max(s,t)


def pi_bounds():
    a,b = arctan_bounds(Fraction(1,5), 27)
    c,d = arctan_bounds(Fraction(1,239), 12)
    return 16*a-4*d,16*b-4*c


PI_LO, PI_HI = pi_bounds()
if not 0 < Fraction(999, 1000)*PI_HI < PI_LO < PI_HI < 4:
    raise ArithmeticError("The proved angle bounds are too wide")
FIELD = re.compile(rb'(0|[1-9][0-9]*)')


def sin_partial(x, terms):
    term = x
    s = term
    for i in range(1, terms):
        term *= -x*x / ((2*i)*(2*i+1))
        s += term
    return s


@cache
def sin_bounds(n, j):
    if 2*j == n:
        return Fraction(1), Fraction(1)
    if not 0 < 2*j < n:
        raise ValueError(f"Invalid sample angle {n}, {j}")
    # Increasing sine, alternating truncations, and Machin's formula.
    return sin_partial(PI_LO*j/n, 16), sin_partial(PI_HI*j/n, 17)


def expected(nmin, nmax, kmin, kmax, stats):
    if not 251 <= nmin <= nmax <= 1000 or not 7 <= kmin <= kmax <= 250:
        raise ValueError('Shard lies outside the certified parameter range.')
    for k in range(kmin, kmax+1):
        for n in range(max(nmin,4*k),min(nmax,20*k-1)+1):
            first=isqrt(49*n)//20+1
            cutoff=7 if 2*n<=15*k else 5 if n<=10*k or k<=100 else 6
            for j in range(first,n//2+1):
                lo,hi = sin_bounds(n,j)
                if k*lo>=cutoff and 5*n*lo*lo>=6:
                    break
                if not (k*hi<cutoff or 5*n*hi*hi<6):
                    raise ValueError(f"Indeterminate entrance at {(n,k,j)}")
                yield n,k,j
            else:
                raise ValueError(f"Missing analytic entrance at {(n,k)}")
            stats['pairs']+=1
            stats['witnessed_pairs']+= j>first
            stats['highest_entrance']=max(stats['highest_entrance'],j)


def dyadic_lt(a, bits_a, b, bits_b):
    return a << bits_b < b << bits_a


def verify(source,nmin,nmax,kmin,kmax):
    digest=hashlib.sha256()
    stats=dict(pairs=0,witnessed_pairs=0,highest_entrance=0,gaps=0,bytes=0,max_bits=0)
    previous_key=None
    right_previous=None
    for target in expected(nmin,nmax,kmin,kmax,stats):
        line=source.readline(1024)
        fields=line.removesuffix(b'\n').split(b',')
        if not line.endswith(b'\n') or len(fields)!=7 or not all(FIELD.fullmatch(x) for x in fields):
            raise ValueError(f"Invalid record at {target}")
        n,k,j,a,abit,b,bbit=map(int,fields)
        if (n,k,j)!=target:
            raise ValueError(f"Expected {target}, found {(n,k,j)}")
        if not (0<abit<=512 and 0<bbit<=512 and a%2==b%2==1 and
                0<a<(1<<abit) and 0<b<(1<<bbit) and dyadic_lt(a,abit,b,bbit)):
            raise ValueError(f"Noncanonical or unordered dyadic endpoints at {target}")
        key=(n,k)
        if previous_key==key and not dyadic_lt(*right_previous,a,abit):
            raise ValueError(f"Neighboring brackets touch or overlap at {target}")
        previous_key=key
        right_previous=b,bbit
        digest.update(line)
        stats['gaps']+=1
        stats['bytes']+=len(line)
        stats['max_bits']=max(stats['max_bits'],abit,bbit)
    if source.read(1):
        raise ValueError('Extra records at end of ledger')
    stats['sha256']=digest.hexdigest()
    return stats


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--nmin',type=int,default=251)
    ap.add_argument('--nmax',type=int,default=1000)
    ap.add_argument('--kmin',type=int,default=7)
    ap.add_argument('--kmax',type=int,default=250)
    args=ap.parse_args()
    print(json.dumps(verify(sys.stdin.buffer,args.nmin,args.nmax,args.kmin,args.kmax),sort_keys=True))
