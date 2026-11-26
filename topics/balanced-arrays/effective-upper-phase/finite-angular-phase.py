"""Uniform rational bounds for leading angular terms on the upper-tilt half-line."""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from math import comb
from pathlib import Path
import json

@lru_cache
def moments(d,r,v,weighted):
    # All probabilities are written as polynomials in the integer lower tilt v.
    w=[comb(d,s)*v**s*(s*(d-s) if weighted else 1) for s in range(r+1)]
    return [F(sum(z*(r-s)**j for s,z in enumerate(w)),sum(w)) for j in (1,2,3)]

def phase_bound(m,t):
    mu,m2,m3=m
    low=1-m2*t*t/2
    if low<=0:
        return None
    # |J-E J|^3 <= J^3 + (E J)^3 and Var J <= E J^2.
    return (m3+mu**3)*t**3/(6*low)

def certificate(n,r,d,v,j):
    k=n*r//d-j
    if k<1: raise ValueError('node must be internal')
    nu=F(d-1,2)
    a,b=[moments(d,r,v,x) for x in (False,True)]
    # A larger occupied tilt reweights both deficit laws by a decreasing
    # geometric factor. Raw moments at v therefore bound every later tilt.
    def phase_errors(ell):
        t=F(22*ell,7*d)
        lo,hi=phase_bound(a,t),phase_bound(b,t)
        if lo is None or hi is None:
            return None
        phase = (n+nu)*lo + nu*hi
        branch = max(a[0], b[0])*t + lo + hi
        return phase, branch
    principal = phase_errors(1)
    e = None if principal is None else principal[0]
    # Divide the error in radians by pi, using pi>3.
    crossed=e is not None and F(n*r,d)-((n+nu)*a[0]-nu*b[0])/d+e/3 < k
    retained = []
    if crossed:
        if principal[1] >= F(3, 4):
            raise ArithmeticError("principal branch bound failed")
        retained.append(1)
    if crossed:
        for ell in range(3,d+1,2):
            bound = phase_errors(ell)
            if bound is None or bound[0] + ell*e >= F(3, 2):
                break
            if bound[1] >= F(3, 4):
                raise ArithmeticError("retained branch bound failed")
            retained.append(ell)
    return dict(n=n,r=r,d=d,node=k,tilt_lower=v,crossing=bool(crossed),odd_labels=retained)

def replay():
    records, evaluations = [], []

    def probe(n, r, d, v, j, stage):
        record = certificate(n, r, d, v, j)
        evaluations.append(dict(stage=stage, **record))
        return record

    for n,r,d in [(36,6,12),(100,10,20),(400,20,40),(1600,40,80),(6400,80,160),(25600,160,320)]:
        for j in (1,2,4):
            # Signs only select witnesses. Insufficient bounds exclude nothing.
            lo, hi = 1, 2
            while probe(n, r, d, hi, j, "doubling")["crossing"]:
                lo, hi = hi, 2*hi
            while hi-lo > 1:
                mid = (lo+hi)//2
                if probe(n, r, d, mid, j, "bisection")["crossing"]:
                    lo = mid
                else:
                    hi = mid
            for v in sorted({1, lo, hi}):
                records.append(probe(n, r, d, v, j, "archive"))
    return records, evaluations


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate both archives")
    args = parser.parse_args()
    records, evaluations = replay()
    script = Path(__file__)
    for target, data in (
        (script.with_suffix(".jsonl"), records),
        (script.with_name("finite-angular-phase-search.jsonl"), evaluations),
    ):
        content = "".join(json.dumps(row) + "\n" for row in data)
        if args.write:
            target.write_text(content, encoding="utf-8")
        elif target.read_text(encoding="utf-8") != content:
            raise SystemExit(f"Archive differs: {target.name}")
    crossings = sum(row["crossing"] for row in records)
    labels = sum(len(row["odd_labels"]) for row in records)
    print(f"{len(evaluations)} evaluations, {len(records)} sampled records, "
          f"{crossings} crossing witnesses, {labels} retained positive labels")


if __name__ == "__main__":
    main()
