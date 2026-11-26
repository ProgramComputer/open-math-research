"""Exact inclusion-exclusion for rows whose omission budget is at most two."""
from collections import defaultdict
from fractions import Fraction
from math import comb
from time import perf_counter
from pathlib import Path
from runpy import run_path

common = run_path(str(Path(__file__).with_name('independent-count.py')))
evaluate = common['evaluate']
rational_node = common['rational_node']


def bad_assignments(n, d, k, ell):
    weight = {q: comb(n - ell, k - ell + q)
              for q in range(max(0, ell-k), min(ell, n-k)+1)}
    if not weight:
        return 0
    required, allowed = min(weight), max(weight)
    choices = [[comb(s, j) for j in range(s+1)] for s in range(ell+1)]
    states = {(ell, 0): 1}
    for step in range(d):
        following = defaultdict(int)
        remaining = d - step - 1
        for (unused, once), count in states.items():
            for a in range(max(0, required-once), min(unused, allowed)+1):
                left = unused - a
                first = count * choices[unused][a]
                for b in range(max(0, required-a), min(once,allowed-a)+1):
                    middle = once - b + a
                    if 2*left + middle < remaining*required:
                        continue
                    following[left,middle] += first * choices[once][b] * weight[a+b]
        states = following
        if not states:
            return 0
    return sum(states.values())


def coefficients(n, d):
    r = d - 3
    return [sum((-1)**ell * comb(n,ell) * bad_assignments(n,d,k,ell)
                for ell in range(min(n,d*k//(r+1))+1)) for k in range(n*r//d+1)]


def verify(n, d):
    t = perf_counter()
    poly = coefficients(n,d)
    degree=len(poly)-1
    assert poly[0]==1 and all(c>0 for c in poly)
    probes=[rational_node(Fraction(poly[k-1],poly[k+1])) for k in range(1,degree)]
    assert all(a<b for a,b in zip([0]+probes,probes))
    assert all((-1)**k*evaluate(poly,-point)>0 for k,point in enumerate(probes,1))
    print((n,d-3,d), degree, f"{perf_counter()-t:.2f}s")


if __name__ == "__main__":
    verify(36, 11)
    verify(36, 12)
