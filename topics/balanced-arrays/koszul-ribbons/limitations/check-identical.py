"""Exact consecutive-quota ratios for identical hereditary row families."""
from fractions import Fraction
from itertools import product
from math import comb, factorial, prod

from collections import defaultdict


def factorial_ratio(a, b):
    if a >= b:
        return Fraction(prod(range(b+1, a+1)))
    return Fraction(1, prod(range(a+1, b+1)))


def ratio(t, ordinary, j):
    """Return A_j / A_0 with products only over bounded factorial gaps."""
    k = 2*t-j
    value = Fraction(0)
    for s in range((3*k+1)//2, 5*t-k+1):
        h = 2*s-3*k
        bulk = comb(5*t-s, k)**ordinary
        for u0 in range(h+1):
            for u1 in range(h-u0+1):
                u = u0, u1, h-u0-u1
                w = tuple(s-h-k+x for x in u)
                if min(w) < 0:
                    continue
                term = bulk * factorial_ratio(2*t, 5*t-s)
                term *= prod(factorial_ratio(t, v)/factorial(x) for x, v in zip(u, w))
                value += term
    return value


def direct_small():
    t, ordinary = 1, 3
    d = ordinary+3
    # Bit masks are used only to define row supports, then rows are labeled.
    supports = [tuple((mask >> i) & 1 for i in range(d)) for mask in range(1 << d)
                if (mask >> ordinary == 0) or
                (mask & ((1 << ordinary)-1) == 0 and (mask >> ordinary).bit_count() <= 2)]
    counts = defaultdict(int)
    for rows in product(supports, repeat=5):
        margins = tuple(map(sum, zip(*rows)))
        if len(set(margins)) == 1:
            counts[margins[0]] += 1
    assert dict(counts) == {0: 1, 1: 2100, 2: 60}, counts
    assert all(ratio(t, ordinary, j) == Fraction(counts[2-j], 60) for j in range(3))
    print("direct counts", dict(counts))


def verify():
    t, ordinary = 100_000, 3
    r1, r2 = ratio(t, ordinary, 1), ratio(t, ordinary, 2)
    assert ratio(t, ordinary, 0) == 1
    quotient = r1*r1/r2
    assert quotient < Fraction(61, 100)
    print("t", t, "ordinary columns", ordinary)
    print("A1/A0", r1)
    print("A2/A0", r2)
    print("A1^2/(A0 A2)", quotient)
    print("ratio < 61/100")


if __name__ == "__main__":
    direct_small()
    verify()
