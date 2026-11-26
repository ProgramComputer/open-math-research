"""Independent checks for shape cutoffs and exact residual identities through weight 18."""
from collections import Counter, defaultdict
from functools import cache
import gzip
from hashlib import sha256
import json
from itertools import combinations, permutations
from math import comb, factorial, prod
from pathlib import Path
import sys

from flint import fmpz_mat

ROOT = Path(__file__).resolve().parent.parent
ARCHIVE = ROOT / "universal-w18"
FAC = tuple(factorial(i) for i in range(100))


def partitions(weight, largest):
    if weight == 0:
        yield ()
    else:
        for first in range(min(weight, largest), 1-1, -1):
            for tail in partitions(weight-first, first):
                yield (first, *tail)


def odd_ratio_test(shape, d):
    """Use integral row-scalings and a subset DP for the odd permanent."""
    ell = len(shape)
    rows = []
    for i, part in enumerate(shape):
        high = FAC[part-i+ell-1]
        rows.append([(high//FAC[part-i+j])**d if part-i+j >= 0 else 0
                     for j in range(ell)])
    layer = {0: (1, 0)}
    for row in rows:
        next_layer = {}
        for mask, (even, odd) in layer.items():
            for j, weight in enumerate(row):
                bit = 1 << j
                if not weight or bit & mask:
                    continue
                if (mask >> (j+1)).bit_count() % 2:
                    plus, minus = odd, even
                else:
                    plus, minus = even, odd
                key = mask | bit
                old_plus, old_minus = next_layer.get(key, (0, 0))
                next_layer[key] = old_plus+weight*plus, old_minus+weight*minus
        layer = next_layer
    _, odd = layer[(1 << ell)-1]
    return odd <= prod(row[i] for i, row in enumerate(rows))


def check_cutoffs(path):
    shapes = {shape for w in range(1, 19) for shape in partitions(w, w)}
    needed = set()
    summary = Counter()
    for record in map(json.loads, path.read_text().splitlines()):
        shape = tuple(record["shape"])
        shapes.remove(shape)
        if len(shape) <= 2:
            assert record["reason"] == "order at most two"
            summary["order_two"] += 1
        elif shape[1] == 1:
            assert record["reason"] == "ribbon"
            summary["ribbon"] += 1
        else:
            cutoff = record["threshold"]
            assert cutoff >= 1 and odd_ratio_test(shape, cutoff), shape
            assert cutoff == 1 or not odd_ratio_test(shape, cutoff-1), shape
            needed.update((shape, d, r) for d in range(1, cutoff) for r in range(1, d+1))
            summary[f"cutoff_{cutoff}"] += 1
    assert not shapes
    return needed, dict(summary)


@cache
def binomial(n, k):
    return comb(n, k) if 0 <= k <= n else 0


def selections(hist, total):
    """Selections by previous row size, with independent binomial multiplicities."""
    if len(hist) == 1:
        w = binomial(hist[0], total)
        if w:
            yield (total,), w
    else:
        for t in range(max(0, total-sum(hist[1:])), min(hist[0], total)+1):
            first = binomial(hist[0], t)
            for rest, weight in selections(hist[1:], total-t):
                yield (t, *rest), first*weight


@cache
def count(n, d, r, k):
    if k == 0:
        return 1
    if k > n or d*k > r*n:
        return 0
    if r == d:
        return binomial(n, k)**d
    if r == 1:
        return FAC[n]//(FAC[n-d*k]*FAC[k]**d)
    if r == d-1:
        return sum((-1)**t * binomial(n, t)*binomial(n-t, k-t)**d for t in range(k+1))
    layer = {(n,) + (0,)*r: 1}
    # Add whole columns, selecting rows grouped by their prior row loads.
    for _ in range(d-1):
        next_layer = defaultdict(int)
        for hist, total in layer.items():
            for picks, multiplicity in selections(hist[:-1], k):
                nxt = tuple(a+inc-dec for a, inc, dec in zip(hist, (0, *picks), (*picks, 0)))
                next_layer[nxt] += total*multiplicity
        layer = next_layer
    return sum(total*binomial(n-hist[-1], k) for hist, total in layer.items())


@cache
def elementary(n, d, r, top):
    h = [count(n, d, r, k) for k in range(top+1)]
    e = [1]
    for i in range(1, top+1):
        e.append(sum((-1)**(j+1)*h[j]*e[i-j] for j in range(1, i+1)))
    return e


def determinant(shape, n, d, r):
    # Dual Jacobi--Trudi for e(t) = 1 / h(-t).
    transpose = tuple(sum(part > j for part in shape) for j in range(shape[0]))
    e = elementary(n, d, r, max(transpose)+len(transpose)-1)
    return int(fmpz_mat([[e[q-i+j] if q-i+j >= 0 else 0
                          for j in range(len(transpose))]
                         for i, q in enumerate(transpose)]).det())


def direct_determinant(shape, n, d, r):
    total = 0
    for perm in permutations(range(len(shape))):
        quotas = [q-i+j for i, (q, j) in enumerate(zip(shape, perm))]
        if min(quotas) < 0:
            continue
        odd = sum(j > k for i, j in enumerate(perm) for k in perm[i+1:]) % 2
        total += (-1)**odd * prod(count(n, d, r, quota) for quota in quotas)
    return total


def labeled_row_check():
    checked = 0
    for d in range(1, 6):
        for r in range(1, d+1):
            supports = [subset for j in range(r+1) for subset in combinations(range(d), j)]
            layer = {(0,)*d: 1}
            for n in range(5):
                for k in range(n+1):
                    assert layer.get((k,)*d, 0) == count(n, d, r, k)
                    checked += 1
                if n == 4:
                    break
                rows = defaultdict(int)
                for margins, weight in layer.items():
                    for subset in supports:
                        target = list(margins)
                        for col in subset:
                            target[col] += 1
                        rows[tuple(target)] += weight
                layer = rows
    return checked


def forward_differences(values):
    output = []
    while values:
        output.append(values[0])
        values = [b-a for a, b in zip(values, values[1:])]
    return output


def main():
    cutoffs = ARCHIVE / "cutoffs.jsonl"
    residuals = ARCHIVE / "residuals.jsonl.gz"
    needed, summary = check_cutoffs(cutoffs)
    print("cutoffs", sum(summary.values()), summary, flush=True)
    assert len(needed) == 5581
    print("small labeled-row count checks", labeled_row_check(), flush=True)
    counts, dig = Counter(), sha256()
    direct_checks = 0
    with gzip.open(residuals, "rt", encoding="utf-8") as stream:
        for line in stream:
            record = json.loads(line)
            shape, d, r = tuple(record["shape"]), record["d"], record["r"]
            needed.remove((shape, d, r))
            values = [determinant(shape, n, d, r) for n in range(d*sum(shape)+1)]
            if len(shape) <= 5:
                for n in {0, min(4, d*sum(shape)), d*sum(shape)}:
                    assert direct_determinant(shape, n, d, r) == values[n]
                    direct_checks += 1
            coefficients = forward_differences(values)
            assert record["binomial_coefficients"] == coefficients, (shape, d, r)
            assert min(coefficients) >= 0, (shape, d, r)
            counts[d, r] += 1
            dig.update(json.dumps([shape, d, r, coefficients], separators=(",", ":")).encode())
            dig.update(b"\n")
    assert not needed
    print("residuals", sum(counts.values()), dict(counts))
    print("direct determinant spot checks", direct_checks)
    print("canonical residual SHA-256", dig.hexdigest())
    for path in (cutoffs, residuals):
        print(path.name, sha256(path.read_bytes()).hexdigest())
    print("column-capacity cache", count.cache_info())


if __name__ == "__main__":
    main()
