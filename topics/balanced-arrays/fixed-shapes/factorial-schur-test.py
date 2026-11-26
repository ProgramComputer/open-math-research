"""Exact dimension certificates for straight Schur determinants of balanced arrays.

Run with Python 3.10+ and python-flint.  Output one row for each partition;
for unhandled low dimensions reconstruct the full polynomial in the row count.
"""
import argparse
from collections import Counter, defaultdict
from functools import cache
from itertools import combinations
from math import comb, factorial, prod
from pathlib import Path
import gzip
import json

from flint import fmpz_mat


def partitions(weight, ceiling=None):
    if not weight:
        yield ()
        return
    largest = weight if ceiling is None else min(weight, ceiling)
    for part in range(largest, 0, -1):
        for rest in partitions(weight - part, part):
            yield (part,) + rest


def quota_matrix(shape, inner=()):
    inside = tuple(inner) + (0,) * (len(shape)-len(inner))
    return [[part - i + j - cut for j, cut in enumerate(inside)]
            for i, part in enumerate(shape)]


def odd_bound(shape, dimension, inner=()):
    """Return the odd-permutation determinant mass and identity, at a common scale."""
    height = len(shape)
    integer_matrix = []
    positive_columns = []
    for indices in quota_matrix(shape, inner):
        maximum = factorial(max(indices))
        row = [(maximum // factorial(k)) ** dimension if k >= 0 else 0
               for k in indices]
        integer_matrix.append(row)
        positive_columns.append(sum(1 << j for j, w in enumerate(row) if w))
    identity = prod(row[i] for i, row in enumerate(integer_matrix))
    # Fill bottom rows first: their initial zero runs eliminate most subsets.
    @cache
    def permanent(available):
        if not available:
            return 1
        i = available.bit_count() - 1
        candidates = available & positive_columns[i]
        value = 0
        while candidates:
            bit = candidates & -candidates
            candidates ^= bit
            value += integer_matrix[i][bit.bit_length() - 1] * permanent(available ^ bit)
        return value
    total = permanent((1 << height) - 1)
    determinant = int(fmpz_mat(integer_matrix).det())
    return (total - determinant) // 2, identity


def cutoff(shape, inner=()):
    low, high = 0, 1
    while True:
        odd, identity = odd_bound(shape, high, inner)
        if odd <= identity:
            break
        low, high = high, 2 * high
    while high - low > 1:
        middle = (high + low) // 2
        odd, identity = odd_bound(shape, middle, inner)
        if odd <= identity:
            high = middle
        else:
            low = middle
    return high


def all_counts(columns, cap, largest, max_rows):
    """All a(n,k) used by the check, indexed by n and common quota k."""
    if cap in {1, columns - 1, columns}:
        def direct(n, k):
            if columns * k > n * cap:
                return 0
            if cap == columns:
                return comb(n, k) ** columns
            if cap == 1:
                return factorial(n) // (factorial(n-columns*k) * factorial(k)**columns)
            return sum((-1)**j * comb(n,j) * comb(n-j,k-j)**columns for j in range(k+1))
        return [[direct(n, k) for k in range(largest+1)] for n in range(max_rows+1)]
    # A sorted tuple records the occupancies of *labeled* columns; the number
    # of subsets leading to each orbit is its transition multiplicity.
    allowed = [subset for size in range(1, cap+1) for subset in combinations(range(columns), size)]
    @cache
    def moves(state):
        neighbors = Counter()
        for subset in allowed:
            if any(state[j] == largest for j in subset):
                continue
            target = list(state)
            for j in subset:
                target[j] += 1
            neighbors[tuple(sorted(target))] += 1
        return tuple(neighbors.items())
    diagonal = [(k,)*columns for k in range(largest+1)]
    current = {diagonal[0]: 1}
    totals = []
    for n in range(max_rows+1):
        totals.append([current.get(t, 0) for t in diagonal])
        if n == max_rows:
            break
        following = defaultdict(int, current)  # the empty next row
        for state, count in current.items():
            for target, multiplicity in moves(state):
                following[target] += count*multiplicity
        current = following
    return totals


def coefficients(shape, dimension, counts, inner=()):
    indices = quota_matrix(shape, inner)
    values = [int(fmpz_mat([[row[k] if k >= 0 else 0 for k in line]
                            for line in indices]).det())
              for row in counts[:dimension * (sum(shape)-sum(inner))+1]]
    result = []
    while values:
        result.append(values[0])
        values = [b-a for a,b in zip(values, values[1:])]
    return result


def put(stream, fields):
    stream.write(json.dumps(fields, separators=(',', ':')) + '\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('weight', type=int)
    parser.add_argument('output_directory', type=Path)
    args = parser.parse_args()
    output = args.output_directory
    output.mkdir(parents=True, exist_ok=True)
    shapes = {}
    with (output/'cutoffs.jsonl').open('w') as out:
        for weight in range(1, args.weight+1):
            thresholds = Counter()
            for shape in partitions(weight):
                if len(shape) <= 2:
                    put(out, dict(shape=shape, reason='order at most two'))
                elif shape[1] == 1:
                    put(out, dict(shape=shape, reason='ribbon'))
                else:
                    threshold = cutoff(shape)
                    shapes[shape] = threshold
                    thresholds[threshold] += 1
                    put(out, dict(shape=shape, threshold=threshold))
            print('weight', weight, 'threshold histogram', dict(sorted(thresholds.items())), flush=True)
    total = 0
    from io import TextIOWrapper
    with (output/'residuals.jsonl.gz').open('wb') as raw, gzip.GzipFile(filename='', fileobj=raw,mode='wb',mtime=0) as gz, TextIOWrapper(gz, encoding='utf-8') as out:
        for d in range(1, max(shapes.values(), default=1)):
            work = [s for s,t in shapes.items() if d < t]
            largest = max(s[0]+len(s)-1 for s in work)
            max_rows = d * max(map(sum,work))
            for r in range(1,d+1):
                counts = all_counts(d,r,largest,max_rows)
                for shape in work:
                    vector = coefficients(shape,d,counts)
                    if any(v<0 for v in vector):
                        raise ArithmeticError((shape,d,r,vector))
                    put(out,dict(shape=shape,d=d,r=r,binomial_coefficients=vector))
                    total += 1
                print('dimension',d,'cap',r,'cumulative identities',total,flush=True)
    print('completed',total,'residual identities',flush=True)


if __name__ == '__main__':
    main()
