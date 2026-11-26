"""Show that a strict factor-four proof cannot cover all common-cap arrays."""
from collections import Counter
from fractions import Fraction
from itertools import product
from math import comb


def labeled_row_count(n, k):
    rows = [r for r in product((0, 1), repeat=3) if sum(r) <= 2]
    counts = {(0, 0, 0): 1}
    for _ in range(n):
        new = Counter()
        for sums, ways in counts.items():
            for row in rows:
                dest = tuple(x + y for x, y in zip(sums, row))
                if max(dest) <= k:
                    new[dest] += ways
        counts = new
    return counts[(k, k, k)]


def exclude_full_rows(n, k):
    return sum((-1)**j * comb(n, j) * comb(n-j, k-j)**3 for j in range(k+1))


if __name__ == "__main__":
    n = 12
    degrees = range(9)
    coefficients = [labeled_row_count(n, k) for k in degrees]
    assert coefficients == [exclude_full_rows(n, k) for k in degrees]
    a, b, c = coefficients[2:5]
    ratio = Fraction(b*b, a*c)
    assert ratio == Fraction(87225632, 22830843) < 4
    # Rational probes isolate a full degree of negative roots independently.
    signs = [1]
    probes = []
    for exponent in range(-64, 65):
        x = -Fraction(2)**exponent
        value = sum(Fraction(v)*x**j for j, v in enumerate(coefficients))
        sign = (value > 0) - (value < 0)
        if sign and sign != signs[-1]:
            probes.append(str(x))
            signs.append(sign)
    assert len(signs)-1 == 8
    print("12 rows, three columns, cap two:", coefficients)
    print("Central second quotient at k=3:", ratio, "< 4")
    print("Successive opposite-sign probes after zero:", ", ".join(probes))
