"""Reconstruct the four-row marginal by enumerating columns and multiplying row polynomials."""
from collections import Counter
from itertools import product

BOUNDS = ((0, 1), (1, 3), (2, 2), (2, 2))


def by_columns():
    counts = Counter()
    for a, b, c in product(range(16), repeat=3):
        if b.bit_count() != 2 or c.bit_count() != 3:
            continue
        row_sizes = [sum((mask >> i) & 1 for mask in (a, b, c)) for i in range(4)]
        if all(lo <= x <= hi for x, (lo, hi) in zip(row_sizes, BOUNDS)):
            counts[a.bit_count()] += 1
    return [counts[k] for k in range(5)]


def by_row_polynomials():
    table = {(0, 0, 0): 1}
    for lo, hi in BOUNDS:
        updated = Counter()
        for row in product((0, 1), repeat=3):
            if lo <= sum(row) <= hi:
                for profile, coefficient in table.items():
                    destination = tuple(x + y for x, y in zip(profile, row))
                    updated[destination] += coefficient
        table = updated
    return [table[k, 2, 3] for k in range(5)]


if __name__ == "__main__":
    coeff = by_columns()
    assert coeff == by_row_polynomials() == [1, 11, 14, 5, 0]
    d, c, b, a, _ = coeff
    disc = b*b*c*c - 4*a*c**3 - 4*b**3*d - 27*a*a*d*d + 18*a*b*c*d
    assert disc == -695
    print(f"Two independent counts give {coeff}. Cubic discriminant {disc}.")
