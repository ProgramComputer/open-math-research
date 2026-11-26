"""Reconstruct exact ordinary coefficient vectors via a separate cycle-product DP."""
import argparse
from itertools import permutations
from math import comb, factorial
from time import perf_counter

from flint import fmpz_poly

from certify import eulerian_gamma


def ordinary_eulerian(limit):
    result = [None, fmpz_poly([1])]
    for size in range(2, limit + 1):
        prev = result[-1]
        result.append(fmpz_poly([
            (j + 1) * prev[j] + (size - j) * prev[j - 1]
            for j in range(size)
        ]))
    return result


def ordinary_rows(k, limit, eul):
    # Add the possible cycle lengths one at a time. In the stage for length
    # ell, every newly added cycle has that same length. The number of
    # ways to select and partition their labels is
    # n! / ((n-h*ell)! (ell!)^h h!). The Eulerian factor is each selected
    # cycle's weighted polynomial on an ordered label set.
    t = fmpz_poly([0,1])
    rows = [fmpz_poly() for _ in range(limit+1)]
    rows[0] = fmpz_poly([1])
    for ell in range(k,limit+1):
        weighted = t*eul[ell-1]
        nxt = rows.copy()
        fac = factorial(ell)
        power = fmpz_poly([1])
        for h in range(1,limit//ell+1):
            power *= weighted
            multiplicity = factorial(h*ell)//(fac**h*factorial(h))
            for n in range(h*ell,limit+1):
                if rows[n-h*ell]:
                    nxt[n] += comb(n,h*ell)*multiplicity*power*rows[n-h*ell]
        rows = nxt
    return [None if not p else fmpz_poly(list(p)[1:]) for p in rows]


def check(limit):
    started = perf_counter()
    eul = ordinary_eulerian(limit-1)
    cyc = eulerian_gamma(limit-1)
    t = fmpz_poly([0,1])
    oneplus = fmpz_poly([1,1])
    lifts = [None,None]
    for d in range(2,limit-1):
        lifts.append([t**j*oneplus**(d-2*j) for j in range(d//2+1)])
    total = 0
    for k in range(4,limit//4+1):
        ordinary = ordinary_rows(k,limit,eul)
        rows = {}
        for n in range(k,limit+1):
            gamma = cyc[n-1]
            for length in range(k,n-k+1):
                gamma += comb(n-1,length-1)*t*cyc[length-1]*rows[n-length]
            rows[n] = gamma
            if sum((b*c for b,c in zip(lifts[n-2],gamma)),fmpz_poly()) != ordinary[n]:
                raise ArithmeticError((n,k))
            total += 1
    print(f"Ordinary and gamma routes agree on {total} whole vectors through row size {limit} in {perf_counter()-started:.3f}s.")


if __name__ == "__main__":
    import sys
    check(int(sys.argv[1]))
