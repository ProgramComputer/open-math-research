"""Literal small checks of normalized accepted color words and barred fibers."""
from collections import Counter
from itertools import permutations, product
from math import comb, factorial


def cycles(perm):
    left = set(range(len(perm)))
    while left:
        start = min(left)
        cycle = []
        vertex = start
        while vertex in left:
            left.remove(vertex)
            cycle.append(vertex)
            vertex = perm[vertex]
        assert vertex == start
        yield cycle


def erase_bars(word, color_cycles):
    n = len(word)
    p = sum(map(len, color_cycles))
    classes = [[i for i in reversed(range(n)) if word[i] == c] for c in range(p)]
    perm = [-1] * n
    edges = [None] * n
    min_cycle = float("inf")
    for cycle in color_cycles:
        ribbon = [token for c in cycle for token in [n + c, *classes[c]]]
        labels = [i for i, token in enumerate(ribbon) if token < n]
        min_cycle = min(min_cycle, len(labels))
        if not labels:
            return None
        for i, j in zip(labels, labels[1:] + [len(ribbon) + labels[0]]):
            x = ribbon[i]
            perm[x] = ribbon[j % len(ribbon)]
            edges[x] = tuple(ribbon[z % len(ribbon)] - n for z in range(i + 1, j))
    return tuple(perm), tuple(edges), min_cycle


def boxed_binomial(n, p, s):
    if p < s:
        return 0
    if not n:
        return int(p == 0)
    return comb(n + p - s - 1, p - s)


def main():
    grid = 0
    eligible_words = 0
    for k in (2, 3, 4, 5):
        table = {}
        for n in range(7):
            original_rows = [
                (perm, sum(i < j for i, j in enumerate(perm)))
                for perm in permutations(range(n)) if all(len(c) >= k for c in cycles(perm))
            ]
            for p in range(5):
                grid += 1
                fibers = Counter()
                seen = set()
                for color_perm in permutations(range(p)):
                    color_cycles = list(cycles(color_perm))
                    for word in product(range(p), repeat=n):
                        result = erase_bars(word, color_cycles)
                        if result is None or result[2] < k:
                            continue
                        perm, bars, _ = result
                        assert all(bars[x] for x in range(n) if x < perm[x])
                        assert (perm, bars) not in seen
                        seen.add((perm, bars))
                        fibers[perm] += 1
                expected = Counter({
                    perm: factorial(p) * boxed_binomial(n, p, s)
                    for perm, s in original_rows
                })
                assert fibers == expected, (n, p, k)
                total = sum(fibers.values())
                eligible_words += total
                assert total % factorial(p) == 0
                normalized = total // factorial(p)
                table[n, p] = normalized
                if n:
                    recurrence = sum(
                        comb(n - 1, m - 1) * j**(m - 1) * table[n - m, p - j]
                        for m in range(k, n + 1) for j in range(1, p + 1)
                    )
                    assert normalized == recurrence, (n, p, k)
                else:
                    assert normalized == int(p == 0)
    print(f"Literal enumeration checked {grid} triples and {eligible_words} accepted tagged words.")
    print("Every per-permutation barred fiber, row transform, recurrence and boundary passed.")


if __name__ == "__main__":
    main()
