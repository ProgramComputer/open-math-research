"""Check the two extreme terminal ranks directly and replay the Eulerian sign witnesses."""

from collections import Counter, defaultdict
from fractions import Fraction
from itertools import permutations
from math import comb, factorial


def eulerian(degree_parameter):
    poly = [1]
    for n in range(1, degree_parameter + 1):
        extended = poly + [0]
        poly = [
            (i + 1) * extended[i] + ((n - i) * extended[i - 1] if i else 0)
            for i in range(n)
        ]
    return poly


def permutation_rows(maximum):
    by_size = {}
    extreme = {}
    for n in range(1, maximum + 1):
        rows = defaultdict(Counter)
        ranks = defaultdict(Counter)
        for perm in permutations(range(n)):
            unseen = set(range(n))
            minimum = n
            while unseen:
                i = next(iter(unseen))
                length = 0
                while i in unseen:
                    unseen.remove(i)
                    length += 1
                    i = perm[i]
                minimum = min(minimum, length)
            if minimum < 3:
                continue
            exponent = sum(j > i for i, j in enumerate(perm))
            rank = n - 1 - perm[-1]
            for k in range(3, minimum + 1):
                rows[k][exponent] += 1
                if rank in (1, n - 1):
                    ranks[k, rank][exponent] += 1
        by_size[n] = rows
        extreme[n] = ranks
    return by_size, extreme


def verify_counts():
    by_size, extreme = permutation_rows(9)
    total = 0
    for n in range(6, 10):
        for k in range(3, n // 2 + 1):
            predicted = by_size[n - 1][k].copy()
            for left, count in enumerate(eulerian(k - 2)):
                for right, multiplicity in by_size[n - k][k].items():
                    predicted[1 + left + right] += comb(n - 2, k - 2) * count * multiplicity
            shifted = Counter({i + 1: count for i, count in predicted.items()})
            if predicted != extreme[n][k, 1] or shifted != extreme[n][k, n - 1]:
                raise ArithmeticError((n, k, "terminal-rank counts"))
            total += 1
    return total


def value_and_derivative(poly, x):
    value, derivative = 0, 0
    for coefficient in reversed(poly):
        derivative = derivative * x + value
        value = value * x + coefficient
    return value, derivative


def verify_signs():
    cases = [
        (3, -4, -2367000),
        (4, Fraction(-1, 8), Fraction(-109219277995695, 4398046511104)),
        (5, Fraction(-5, 2), Fraction(-878212034554338351, 262144)),
    ]
    for m, t, expected in cases:
        p, dp = value_and_derivative(eulerian(2 * m), t)
        a, da = value_and_derivative(eulerian(m), t)
        b, db = value_and_derivative(eulerian(m - 1), t)
        coefficient = comb(2 * m, m - 1)
        r = p + coefficient * t * a * b
        dr = dp + coefficient * (a * b + t * (da * b + a * db))
        w = (r + (1 + t) * dr) * p - (1 + t) * r * dp
        if w != expected or w >= 0:
            raise ArithmeticError((m, t, w))
    if 9**6 <= 2 * 8**6 or 4 * 9**6 >= 16**6:
        raise ArithmeticError("Eulerian series bounds at m=6")


if __name__ == "__main__":
    total = verify_counts()
    verify_signs()
    print(f"Checked both terminal ranks on {total} parameter pairs from direct enumeration.")
    print(f"Enumerated all {sum(factorial(n) for n in range(1, 10))} permutations of sizes 1 through 9.")
    print("Three signed Wronskians and the two rational series bounds passed.")
