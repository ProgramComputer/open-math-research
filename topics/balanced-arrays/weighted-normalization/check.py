#!/usr/bin/env python3
"""Direct finite check of proposed weighted array inequalities using integers."""
import argparse
from collections import Counter, defaultdict
from contextlib import ExitStack
import gzip
import json
from itertools import product
from math import comb, prod
from random import Random

MODES = ("pure", "mixed", "diagonal", "box_support", "CAPP")


def subsets(n):
    return tuple(range(1 << n))


def between(a, b):
    return product(*(range(x, y + 1) for x, y in zip(a, b)))


def increment(a, i):
    return a[:i] + (a[i] + 1,) + a[i + 1:]


def add_check(totals, failures, mode, passed, witness):
    totals[mode] += 1
    if not passed:
        failures.setdefault(mode, witness)


def check(n, d, weights, intervals, totals, failures, ledger):
    before = totals.copy()
    local_failures = {}
    masks = subsets(n)
    cells = [
        [
            prod(weights[i][j] for i in range(n) if mask & (1 << i))
            for mask in masks
        ]
        for j in range(d)
    ]
    counts = Counter()
    fibers = [defaultdict(Counter) for _ in range(d)]
    totals["models"] += 1
    totals["binary_arrays_considered"] += len(masks) ** d
    for columns in product(*[tuple(m for m in masks if w[m]) for w in cells]):
        rows = tuple(sum(bool(m & (1 << i)) for m in columns) for i in range(n))
        if not all(lo <= k <= hi for k, (lo, hi) in zip(rows, intervals)):
            continue
        totals["positive_weight_arrays"] += 1
        margins = tuple(m.bit_count() for m in columns)
        weight = prod(w[m] for w, m in zip(cells, columns))
        counts[margins] += weight
        for j in range(d):
            fibers[j][margins[:j] + margins[j + 1:]][columns[j]] += weight

    model = (n, d, weights, intervals)
    for a in product(range(n + 1), repeat=d):
        for i in range(d):
            k = a[i]
            if k + 2 <= n:
                b = increment(a, i)
                c = increment(b, i)
                u, v, w = counts[a], counts[b], counts[c]
                left = v*v*comb(n,k)*comb(n,k+2)
                right = u*w*comb(n,k+1)**2
                add_check(totals, local_failures, "pure", left >= right, (model, a, i, (u,v,w), (left,right)))
            if k == n:
                continue
            for j in range(i+1, d):
                if a[j] == n:
                    continue
                b, c = increment(a, i), increment(a, j)
                both = increment(b, j)
                u, v, w, x = (counts[p] for p in (a, b, c, both))
                add_check(totals, local_failures, "mixed", v*w >= u*x, (model, a, i, j, (u,v,w,x)))
    for k in range(1, n):
        u, v, w = (counts[(t,)*d] for t in (k-1,k,k+1))
        left = v*v*(comb(n,k-1)*comb(n,k+1))**d
        right = u*w*comb(n,k)**(2*d)
        add_check(totals, local_failures, "diagonal", left >= right, (model, k, (u,v,w), (left,right)))

    support = tuple(counts)
    for i, a in enumerate(support):
        for b in support[i+1:]:
            if all(x >= y for x, y in zip(a,b)):
                lo, hi = b, a
            elif all(x <= y for x, y in zip(a,b)):
                lo, hi = a, b
            else:
                continue
            for c in between(lo, hi):
                if c not in (lo, hi):
                    add_check(totals, local_failures, "box_support", c in counts, (model, lo, c, hi))

    full = (1 << n)-1
    for j, fixed_margin_fibers in enumerate(fibers):
        for fixed_margins, mass in fixed_margin_fibers.items():
            for free in masks:
                size = free.bit_count()
                if size < 2 or size % 2:
                    continue
                outside = full ^ free
                for bits in masks:
                    if bits & free:
                        continue
                    # Conditional normalizer cancels from every antipodal product.
                    total_mass = sum(v for m, v in mass.items() if m & outside == bits)
                    if not total_mass:
                        continue
                    m = size // 2
                    sums = [0,0]
                    for s in masks:
                        if s & outside or s.bit_count() not in (m-1,m):
                            continue
                        sums[s.bit_count()-(m-1)] += mass[bits|s] * mass[bits|(free^s)]
                    left = sums[1] * comb(size, m-1)
                    right = sums[0] * comb(size, m)
                    add_check(totals, local_failures, "CAPP", left >= right,
                              (model, j, fixed_margins, free, bits, tuple(sums), (left,right)))


    for mode, witness in local_failures.items():
        failures.setdefault(mode, witness)
    if ledger is not None:
        record = {
            "rows": n, "columns": d, "weights": weights, "intervals": intervals,
            "positive_profiles": [[list(q), v] for q, v in sorted(counts.items())],
            "diagonal": [counts[(k,) * d] for k in range(n + 1)],
            "tests": {mode: totals[mode] - before[mode] for mode in MODES},
            "failures": local_failures,
        }
        ledger.write((json.dumps(record, separators=(",", ":")) + "\n").encode())


def run(ledger):
    totals, failures = Counter(), {}
    intervals = tuple((lo,hi) for lo in range(4) for hi in range(lo,4))
    for flat in product((0,1), repeat=6):
        weights = (flat[:3],flat[3:])
        for bounds in product(intervals, repeat=2):
            check(2, 3, weights, bounds, totals, failures, ledger)
    print("Exhaustive 2x3 binary weight models complete.", flush=True)
    rng = Random(20261126)
    for n, d, count in ((2,3,250),(3,3,500),(4,3,225),(4,4,30)):
        intervals = tuple((lo,hi) for lo in range(d+1) for hi in range(lo,d+1))
        for _ in range(count):
            weights = tuple(tuple(rng.choice((0,1,1,2,3,7)) for _ in range(d)) for _ in range(n))
            bounds = tuple(rng.choice(intervals) for _ in range(n))
            check(n, d, weights, bounds, totals, failures, ledger)
        print(f"{count} seeded weighted {n}x{d} models complete.", flush=True)
    for mode, total in sorted(totals.items()):
        print(f"{mode}: {total}")
    for mode in MODES:
        print(f"{mode}: {failures.get(mode, 'no failure')}")
    return bool(failures)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ledger", help="write a deterministic JSONL gzip of each model")
    args = parser.parse_args()
    with ExitStack() as stack:
        ledger = None
        if args.ledger:
            raw = stack.enter_context(open(args.ledger, "wb"))
            ledger = stack.enter_context(gzip.GzipFile(filename="", fileobj=raw, mode="wb", mtime=0))
        return run(ledger)


if __name__ == "__main__":
    raise SystemExit(main())
