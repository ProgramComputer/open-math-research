"""Reconstruct the weighted four-column certificate by row and by column."""
from collections import Counter
from itertools import combinations, product

TRIANGLE = {(0, 1), (0, 2), (1, 2)}
ROWS = [()] + [(i,) for i in range(4)] + list(combinations(range(4), 2))


def rows(n):
    layer = Counter({((0, 0, 0, 0), 0): 1})
    for _ in range(n):
        following = Counter()
        for (quota, exponent), ways in layer.items():
            for row in ROWS:
                target = list(quota)
                for i in row:
                    target[i] += 1
                if max(target) <= n//2:
                    following[(tuple(target), exponent + (row in TRIANGLE))] += ways
        layer = following
    return [Counter({p: v for (quota, p), v in layer.items() if quota == (k,)*4})
            for k in range(n//2+1)]


def columns(n, k):
    weights = Counter()
    for choice in product(combinations(range(n), k), repeat=4):
        used = [tuple(i for i, col in enumerate(choice) if row in col) for row in range(n)]
        if all(len(row) <= 2 for row in used):
            weights[sum(row in TRIANGLE for row in used)] += 1
    return weights


def main():
    expected = {
        4: [{0: 1}, {0: 96, 1: 108}, {2: 90}],
        5: [{0: 1}, {0: 300, 1: 240}, {1: 1080, 2: 1350, 3: 60}],
    }
    for n, want in expected.items():
        by_row = rows(n)
        by_column = [columns(n, k) for k in range(n//2 + 1)]
        if by_row != want or by_row != by_column:
            raise ArithmeticError((n, by_row, by_column))
    for t, discriminant in [(1, 281640), (256, -569704560)]:
        co = [sum(v*t**p for p, v in terms.items()) for terms in expected[5]]
        if co[1]**2-4*co[0]*co[2] != discriminant:
            raise ArithmeticError((t, co, discriminant))
        print(f't={t}, ascending coefficients {co}, discriminant {discriminant}')


if __name__ == '__main__':
    main()
