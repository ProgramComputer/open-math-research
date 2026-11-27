"""Confirm the insertion convolution by appending one letter to every short word."""
from collections import Counter
from itertools import permutations, product
from math import comb, factorial


def components(perm):
    remaining = set(range(len(perm)))
    sizes, component = [], [None] * len(perm)
    while remaining:
        x = min(remaining)
        size = 0
        while x in remaining:
            remaining.remove(x)
            component[x] = len(sizes)
            x = perm[x]
            size += 1
        sizes.append(size)
    return sizes, component


def accepted_counts(n, p, cutoffs):
    counts = Counter()
    gained = Counter()
    for perm in permutations(range(p)):
        sizes, component = components(perm)
        for word in product(range(p), repeat=n):
            loads = [0] * len(sizes)
            for color in word:
                loads[component[color]] += 1
            minimum = min(loads, default=n + 8)
            for k in cutoffs:
                if minimum >= k:
                    counts[k] += 1
                    continue
                for c in range(p):
                    loads[component[c]] += 1
                    if min(loads) >= k:
                        gained[k, sizes[component[c]]] += 1
                    loads[component[c]] -= 1
    return counts, gained


def original_rows(limit, cutoffs):
    rows = Counter()
    eulerian = Counter()
    for n in range(limit + 1):
        for perm in permutations(range(n)):
            sizes, _ = components(perm)
            s = sum(i < x for i, x in enumerate(perm))
            eulerian[n, s] += 1
            for k in cutoffs:
                if min(sizes, default=limit+1) >= k:
                    rows[n, k, s] += 1
    return rows, eulerian


def main():
    cutoffs = range(2, 7)
    data = {(n, p): accepted_counts(n, p, cutoffs)
            for n in range(8) for p in range(5)}
    rows, eulerian = original_rows(7, cutoffs)
    cases = channels = equality = 0
    for n in range(7):
        for p in range(1, 5):
            for k in cutoffs:
                if k > n+1:
                    continue
                residual = n+1-k
                old, gained = data[n, p]
                successor, _ = data[n+1, p]
                difference = successor[k] - p*old[k]
                assert difference == sum(gained[k, j] for j in range(1, p+1))
                for j in range(1, p+1):
                    residual_count = data[residual, p-j][0][k]
                    expected = (comb(n, k-1)*comb(p, j)*factorial(j)
                                * j**(k-1)*residual_count)
                    assert gained[k, j] == expected, (n, p, k, j)
                    channels += 1
                lag = comb(n, k-1)*sum(eulerian[k-1, j-1]*rows[residual, k, p-j]
                                              for j in range(1, p+1))
                assert 0 <= factorial(p)*lag <= difference, (n, p, k)
                equality += factorial(p)*lag == difference
                cases += 1
    print(f"{cases} adjacent-size triples and {channels} marked color-cycle sizes passed.")
    print(f"The literal lag was bounded in all {cases} triples; equality in {equality}.")
    print("Old sizes 0..6, 1..4 colors, 2 <= cutoff <= min(6, old size + 1).")


if __name__ == "__main__":
    main()
