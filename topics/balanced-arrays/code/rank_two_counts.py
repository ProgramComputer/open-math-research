"""Balanced arrays with row cap two counted by labeled matchings."""

from functools import lru_cache
from math import comb, factorial, perm


@lru_cache(maxsize=2048)
def multipartite_matchings(d, k):
    """Numbers of p-edge matchings of K_{k,...,k} for d color classes."""
    old = [1]
    for color in range(d):
        vertices = color*k
        new = [0]*((vertices+k)//2+1)
        for p, ways in enumerate(old):
            if not ways:
                continue
            available = vertices-2*p
            for i in range(min(k,available)+1):
                new[p+i] += ways * comb(available,i) * perm(k,i)
        old = new
    return tuple(old)


def rank_two(n, k, d):
    scale = factorial(k)**d
    total = sum(ways * perm(n,d*k-p) for p,ways in enumerate(multipartite_matchings(d,k))
                if d*k-p <= n)
    value, rem = divmod(total, scale)
    if rem:
        raise ArithmeticError("Occupied-cell labels did not divide out exactly")
    return value
