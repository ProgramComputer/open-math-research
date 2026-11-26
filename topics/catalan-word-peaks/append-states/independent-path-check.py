"""Verify append-state examples using Dyck steps and Descartes' rule."""
from collections import Counter
from fractions import Fraction
from math import comb


def coefficients(n, height, strict_drop=False):
    """Count Dyck prefixes ending at up-step n, then append forced downs.

    Height is measured before the last up-step. Runs of at least two down
    steps have the same effect on the next peak as exactly two.
    """
    layer = Counter({(0, 0, 0, False, 0): 1})
    result = Counter()
    for _ in range(2 * n - 1):
        following = Counter()
        for (ups, level, downs, consecutive, peaks), count in layer.items():
            if level:
                following[ups, level - 1, min(downs + 1, 2), consecutive, peaks] += count
            peak_total = peaks + (consecutive and downs == 2)
            if ups + 1 == n:
                legal = (downs == 2 if strict_drop else downs > 0 or n == 1)
                if level == height and legal:
                    result[peak_total] += count
            else:
                following[ups + 1, level + 1, 0, ups > 0 and downs == 0, peak_total] += count
        layer = following
    return [result[j] for j in range(max(result) + 1)]


def evaluate(poly, point):
    result = 0
    for coefficient in reversed(poly):
        result = result * point + coefficient
    return result


def positive_root_bound(poly, left, right):
    """Descartes bound under x=(left+right*u)/(1+u), or x=left+u."""
    degree = len(poly) - 1
    transformed = [0] * (degree + 1)
    for i, coefficient in enumerate(poly):
        if right is None:
            for j in range(i + 1):
                transformed[j] += coefficient * comb(i, j) * left ** (i - j)
        else:
            for j in range(i + 1):
                for k in range(degree - i + 1):
                    transformed[j + k] += (coefficient * comb(i, j) * left ** (i - j)
                                           * right ** j * comb(degree - i, k))
    signs = [coefficient > 0 for coefficient in transformed if coefficient]
    return sum(a != b for a, b in zip(signs, signs[1:]))


def real_negative_roots(poly, split):
    # All original coefficients are positive, so every real root is negative.
    assert all(c > 0 for c in poly)
    reflected = [(-1) ** i * coefficient for i, coefficient in enumerate(poly)]
    points = [0, *split]
    values = [evaluate(reflected, point) for point in points]
    assert all(values)
    upper = [positive_root_bound(reflected, a, b)
             for a, b in zip(points, [*split, None])]
    signs = [value > 0 for value in values]
    signs.append(reflected[-1] > 0)
    lower = [int(a != b) for a, b in zip(signs, signs[1:])]
    assert lower == upper
    return sum(upper)


if __name__ == "__main__":
    first, second = coefficients(4, 0), coefficients(5, 0)
    assert first == [2, 3] and second == [5, 8, 1]
    assert second[1] ** 2 - 4 * second[0] * second[2] == 44
    assert evaluate(second, Fraction(-2, 3)) == Fraction(1, 9)
    drop = coefficients(16, 5, strict_drop=True)
    full = coefficients(16, 5)
    assert drop == [19791, 75285, 96525, 46635, 6795, 126]
    assert full == [66255, 207069, 211053, 78755, 8775, 126]
    drop_cuts = [Fraction(1, 2), Fraction(5, 8), Fraction(11, 16),
                 Fraction(3, 4), 1, 2, 6, 64]
    assert real_negative_roots(drop, drop_cuts) == 3
    assert real_negative_roots(full, [Fraction(4, 5), Fraction(3, 2), 3, 10, 64]) == 5
    print("Dyck-step coefficients and exact Descartes root counts verified.")
