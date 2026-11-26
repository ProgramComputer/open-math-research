"""Replay the integer sufficient criterion for actual upper-edge sign intervals."""
import argparse
from math import comb, factorial
from fractions import Fraction
import json
from pathlib import Path

def passed(n,r,d,k,factor=4):
    if not 1 <= k < n*r//d: return False
    e=n*r-d*k
    m=e+d
    b=n-m
    return b>0 and b*min(r,d-r)>=2*m*d and 192*m*m<=b*d and factor*m<=d*d

def terminal_range(n,r,d):
    degree=n*r//d
    first=degree
    while passed(n,r,d,first-1): first-=1
    if passed(n,r,d,first-1): raise ArithmeticError("interval error")
    outer=degree
    while passed(n,r,d,outer-1,6): outer-=1
    return dict(n=n,r=r,d=d,degree=degree,first=first,sign_nodes=degree-first,first_separating_circle=outer,simple_outer_roots=degree-outer)

def rank_one_curvature(n,k,d):
    e=n-d*k
    return Fraction(k+1,k)**d*Fraction(comb(e+d,d),comb(e,d))

def raw_bound(n, r, d, k):
    if not 1 <= k < n*r//d:
        return None
    deficit = n*r - d*k
    span = deficit + d
    bulk = n - span
    if bulk <= 0 or bulk*min(r, d-r) < 2*span*d:
        return None
    return (Fraction(2*d*d*(n-1), (n+span-1)*(2*deficit+d))
            - Fraction(24*d*span, bulk))


def raw_range(n, r, d, threshold):
    degree = n*r//d
    first = degree
    witness = None
    while True:
        bound = raw_bound(n, r, d, first-1)
        if bound is None or bound <= threshold:
            return dict(first=first, count=degree-first,
                        lower_bound=None if witness is None else str(witness))
        witness = bound
        first -= 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate the archive")
    args = parser.parse_args()

    for exponent, target in ((Fraction(139, 200), 2), (Fraction(11, 10), 3)):
        if sum(exponent**j/factorial(j) for j in range(6)) <= target:
            raise ArithmeticError("exponential threshold comparison failed")

    cases=[(20000,10,20),(100000000,50,100)]
    cases += [(1000*d,1,d) for d in (8,12,16,20,40,80)]
    cases += [(10**6,1,64),(10**7,1,64),(10**8,1,64)]
    answer=[]
    for n,r,d in cases:
        row=terminal_range(n,r,d)
        if r==1:
            for k in range(row['first'],row['degree']):
                if rank_one_curvature(n,k,d)<=4:
                    raise ArithmeticError((n,d,k))
            row['rank_one_direct_curvature']=True
        row["raw_sign_band"] = raw_range(n, r, d, Fraction(139, 100))
        row["raw_simple_outer_band"] = raw_range(n, r, d, Fraction(11, 5))
        answer.append(row)
        print(n, r, d, row["sign_nodes"], row["simple_outer_roots"],
              row["raw_sign_band"]["count"], row["raw_simple_outer_band"]["count"])

    target = Path(__file__).with_suffix('.jsonl')
    content = ''.join(json.dumps(row) + chr(10) for row in answer)
    if args.write:
        target.write_text(content, encoding="utf-8")
    elif target.read_text(encoding="utf-8") != content:
        raise SystemExit("Archive differs")


if __name__ == "__main__":
    main()
