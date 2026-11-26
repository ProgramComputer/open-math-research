"""Check the rank-two row/quota minors from direct labeled row enumeration."""
import argparse
from collections import Counter, defaultdict
from itertools import combinations
import json
from pathlib import Path


def row_tables(dimension, last):
    edges = list(combinations(range(dimension), 2))
    choices = [((), None)] + [((i,), None) for i in range(dimension)]
    choices += [(edge, index) for index, edge in enumerate(edges)]
    start = (0,) * dimension
    current = {start: Counter({(0,) * len(edges): 1})}
    tables = [current]
    for _ in range(last):
        following = defaultdict(Counter)
        for quota, polynomial in current.items():
            for columns, index in choices:
                margin = list(quota)
                for column in columns:
                    margin[column] += 1
                target = following[tuple(margin)]
                if index is None:
                    target.update(polynomial)
                    continue
                for powers, coefficient in polynomial.items():
                    degree = list(powers)
                    degree[index] += 1
                    target[tuple(degree)] += coefficient
        current = dict(following)
        tables.append(current)
    return tables


def products(left, right):
    result = Counter()
    for a, x in left.items():
        for b, y in right.items():
            result[tuple(i+j for i, j in zip(a, b))] += x*y
    return result


def check(dimension, last, archive):
    tables = row_tables(dimension, last)
    checked = 0
    nonzero = 0
    for n, low in enumerate(tables):
        if archive is not None:
            for quota, poly in sorted(low.items()):
                archive.write(json.dumps(dict(
                    d=dimension, n=n, quota=quota,
                    terms=[[list(exp), val] for exp, val in sorted(poly.items())]
                ), separators=(',', ':')) + '\n')
        for m in range(n+1, last+1):
            high = tables[m]
            # Any minor with a zero subtracted product is already nonnegative.
            # Thus it suffices to examine its two possibly nonzero factors.
            for larger, low_large in low.items():
                for smaller, high_small in high.items():
                    if smaller == larger or any(x>y for x, y in zip(smaller, larger)):
                        continue
                    minor = products(low.get(smaller, {}), high.get(larger, {}))
                    minor.subtract(products(low_large, high_small))
                    if any(value < 0 for value in minor.values()):
                        raise ArithmeticError((n, m, smaller, larger, dict(minor)))
                    checked += 1
                    nonzero += any(minor.values())
    return dict(d=dimension, through=last, nontrivial_minors_checked=checked,
                nonzero_minors=nonzero, nonzero_quota_vectors=sum(map(len, tables)))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', type=Path, help='write all enumerated polynomials as JSONL')
    args = parser.parse_args()
    archive = args.archive.open('w') if args.archive else None
    try:
        for d, last in ((3, 4), (4, 3)):
            print(json.dumps(check(d, last, archive), sort_keys=True))
    finally:
        if archive:
            archive.close()
