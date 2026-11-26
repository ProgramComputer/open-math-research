"""Exact capped-array coefficients via overload inclusion-exclusion."""
import argparse
from collections import defaultdict
from itertools import product
import json
from math import comb
from time import perf_counter


def joint_overload(n, d, r, k, h):
    """Number of unconstrained quota-k arrays with specified h rows overloaded."""
    limit = d-r-1
    outside = n-h
    miss_min = max(h-k, 0)
    miss_max = min(h, n-k)
    outside_weights = {misses: comb(outside, k-h+misses)
                       for misses in range(miss_min, miss_max+1)}
    dp = {(h,) + (0,)*limit: 1}
    choose = [[comb(q, b) for b in range(q+1)] for q in range(h+1)]
    for step in range(d):
        nxt = defaultdict(int)
        remaining = d-step-1
        for hist, count in dp.items():
            # A specified row cannot use more than limit misses in all d columns.
            # Rows with no remaining freedom are still counted in the last group.
            used = sum(i*v for i, v in enumerate(hist))
            max_now = min(miss_max, h*limit - used - remaining*miss_min)
            if max_now < miss_min:
                continue
            for selected in product(*(range(min(q, max_now)+1) for q in hist[:-1])):
                misses = sum(selected)
                if not miss_min <= misses <= max_now:
                    continue
                weight = outside_weights[misses]
                new_hist = list(hist)
                for i, b in enumerate(selected):
                    weight *= choose[hist[i]][b]
                    new_hist[i] -= b
                    new_hist[i+1] += b
                nxt[tuple(new_hist)] += count * weight
        dp = nxt
    return sum(dp.values())


def coefficient(n, d, r, k, order=None):
    total = comb(n, k)**d
    if k == 0 or r == d:
        return total, total, 0
    if k*d > n*r:
        return 0, 0, 0
    bound = min(n, k*d//(r+1))
    partial = total
    lower, upper = 0, total
    for h in range(1, bound+1 if order is None else min(order, bound)+1):
        term = comb(n,h)*joint_overload(n,d,r,k,h)
        partial += (-1)**h*term
        if h % 2:
            lower = max(lower, partial)
        else:
            upper = min(upper, partial)
        if h == bound or term == 0:
            return partial, partial, h
    return lower, upper, min(bound, order)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int)
    parser.add_argument('d', type=int)
    parser.add_argument('r', type=int)
    parser.add_argument('--max-k', type=int)
    parser.add_argument('--min-k', type=int, default=0)
    parser.add_argument('--order', type=int)
    args = parser.parse_args()
    n, d, r = args.n, args.d, args.r
    maximum = n*r//d if args.max_k is None else min(n*r//d,args.max_k)
    for k in range(args.min_k, maximum+1):
        start = perf_counter()
        lower, upper, order = coefficient(n,d,r,k,args.order)
        print(json.dumps(dict(n=n,d=d,r=r,k=k,lower=lower,upper=upper,
                              order=order, seconds=round(perf_counter()-start,4))),
              flush=True)

if __name__ == '__main__':
    main()
