"""Independent labeled enumeration and dummy-edge refinement for small profiles."""
from collections import Counter, defaultdict
from itertools import permutations, product
import json
from math import factorial, prod

CASES = (
    (3, ((0, 2), (0, 2), (0, 2)), (0, 1, 1), (2, 2, 2), (1, 0, 1)),
    (4, ((0, 3), (1, 2), (1, 3), (0, 2)), (0, 1, 1, 2), (2, 2, 3, 3), (1, 1, 1, 0)),
    (4, ((2, 2), (0, 3), (1, 1), (1, 3)), (1, 1, 0, 2), (3, 2, 2, 2), (1, 0, 1, 0)),
    (3, ((0, 0), (1, 3), (0, 2), (1, 3)), (1, 0, 1), (3, 3, 2), (2, 1, 0)),
    (4, ((0, 4), (0, 4)), (0, 0, 0, 0), (2, 2, 2, 2), (1, 1, 1, 1)),
)


def arrays(d, intervals):
    options = [[m for m in range(1 << d) if lo <= m.bit_count() <= hi]
               for lo, hi in intervals]
    table = defaultdict(list)
    for rows in product(*options):
        columns = tuple(sum(((row >> j) & 1) << i for i, row in enumerate(rows))
                        for j in range(d))
        table[tuple(col.bit_count() for col in columns)].append(columns)
    return table


def paired(red, blue):
    return tuple((a & b, a ^ b) for a, b in zip(red, blue))


def real_rows(mask, n):
    return tuple(i for i in range(n) if (mask >> i) & 1)


def refinements(red, blue, n, deltas, flips):
    matchings = []
    for a, b, delta, flip in zip(red, blue, deltas, flips):
        left = real_rows(a & ~b, n) + tuple(range(n+flip, n+delta))
        right = real_rows(b & ~a, n) + tuple(range(n, n+flip))
        assert len(left) == len(right)
        matchings.append([tuple(sorted((min(u, v), max(u, v)) for u, v in zip(left, image)))
                          for image in permutations(right)
                          if all(u < n or v < n for u, v in zip(left, image))])
    return product(*matchings)


def buckets(red_arrays, blue_arrays, n, deltas, flips):
    counts, skeletons = Counter(), defaultdict(Counter)
    for red, blue in product(red_arrays, blue_arrays):
        key = paired(red, blue)
        counts[key] += 1
        skeletons[key].update(refinements(red, blue, n, deltas, flips))
    return counts, skeletons


def group(key, n, labels):
    grouped = [0]*(1+max(labels))
    for j, (both, either) in enumerate(key):
        for i in range(n):
            grouped[labels[i*len(key)+j]] += 2*((both >> i) & 1) + ((either >> i) & 1)
    return tuple(grouped)


def multiplier(a, b, transfer):
    numerator = prod(factorial(x)*factorial(y) for x, y in zip(a, b))
    denominator = prod(factorial(x+t)*factorial(y-t) for x, y, t in zip(a, b, transfer))
    return numerator, denominator


def wronskian(table, n, d, offsets):
    checked = 0
    for u in offsets:
        for i in range(d):
            v = tuple(a+(j == i) for j, a in enumerate(u))
            terms = Counter()
            for k, l in product(range(-n, n+1), repeat=2):
                if k == l:
                    continue
                left = table.get(tuple(k+a for a in u), ())
                right = table.get(tuple(l+a for a in v), ())
                for a, b in product(left, right):
                    terms[k+l-1, paired(a, b)] += k-l
            assert all(value >= 0 for value in terms.values()), (n, d, u, i)
            checked += len(terms)
    return checked


def run_case(d, intervals, a, b, transfer):
    n = len(intervals)
    table = arrays(d, intervals)
    assert table[a] and table[b]
    delta = tuple(y-x for x, y in zip(a, b))
    assert all(0 <= t <= z for t, z in zip(transfer, delta))
    c, e = (tuple(x+t for x, t in zip(a, transfer)),
            tuple(y-t for y, t in zip(b, transfer)))
    before, source_graphs = buckets(table[a], table[b], n, delta, (0,)*d)
    after, target_graphs = buckets(table[c], table[e], n, delta, transfer)
    strong = structure_count = 0
    big_num, big_den = multiplier(a, b, transfer)
    for key, qty in before.items():
        x = tuple(v-mask.bit_count() for v, (mask, _) in zip(a, key))
        y = tuple(v-mask.bit_count() for v, (mask, _) in zip(b, key))
        top, bottom = multiplier(x, y, transfer)
        assert top * big_den >= bottom * big_num
        assert after[key]*bottom >= qty*top
        strong += after[key]*bottom > qty*top
        target_refinements = bottom // prod(map(factorial, x))
        source_refinements = prod(map(factorial, y))
        assert sum(source_graphs[key].values()) == qty*source_refinements
        assert sum(target_graphs[key].values()) == after[key]*target_refinements
        for skeleton, old in source_graphs[key].items():
            assert target_graphs[key][skeleton] >= old
            structure_count += 1
    labelings = (list(range(n*d)),
                 [i for i in range(n) for j in range(d)],
                 [j for i in range(n) for j in range(d)],
                 [(i+2*j+i*j) % 5 for i in range(n) for j in range(d)])
    sizes = []
    for labels in labelings:
        old, new = Counter(), Counter()
        for counter, grouped in ((before, old), (after, new)):
            for key, value in counter.items():
                grouped[group(key, n, labels)] += value
        assert all(new[key]*big_den >= qty*big_num for key, qty in old.items())
        sizes.append(len(old))
    mixed = tuple(1 if i == 0 else -1 if i == 1 else 0 for i in range(d))
    report = dict(n=n, d=d, row_intervals=intervals, lower=a, upper=b, transfer=transfer,
                  enumerated_arrays=sum(map(len, table.values())),
                  source_pairs=before.total(), target_pairs=after.total(),
                  mask_buckets=len(before), strict_local_gain=strong,
                  refined_skeletons=structure_count, grouped_buckets=sizes,
                  wronskian_coefficients=wronskian(table, n, d, ((0,)*d, mixed)))
    return report


def main():
    for case in CASES:
        print(json.dumps(run_case(*case), separators=(",", ":")))
    p, q, r = (factorial(9)//factorial(9-2*k) for k in (1, 2, 3))
    negative_minor = p*(p*p-q)-q*p+r
    assert negative_minor == -1728
    print(json.dumps({"factorial_TP3_minor": negative_minor}, separators=(",", ":")))


if __name__ == "__main__":
    main()
