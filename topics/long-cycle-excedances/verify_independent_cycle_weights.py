"""Exact Wronskian obstruction to independent cycle weights, standard library only."""

from fractions import Fraction
from math import comb


def eulerian_rows(n):
    rows = [[1]]
    for size in range(1, n + 1):
        old = rows[-1]
        row = [0] * size
        for k, a in enumerate(old):
            row[k] += (k + 1) * a
            if k + 1 < size:
                row[k + 1] += (size - k - 1) * a
        via_differences = [sum((-1) ** j * comb(size + 1, j) * (k + 1 - j) ** size
                               for j in range(k + 1)) for k in range(size)]
        if row != via_differences:
            raise ValueError(f"Eulerian mismatch at size {size}")
        rows.append(row)
    return rows


def add_shifted_product(target, first, second, scale):
    for i, a in enumerate(first):
        for j, b in enumerate(second):
            target[i + j + 1] += scale * a * b


def value_and_derivative(poly, x):
    value = derivative = Fraction(0)
    for coefficient in reversed(poly):
        derivative = derivative * x + value
        value = value * x + coefficient
    return value, derivative


def main():
    n, k = 48, 21
    a = eulerian_rows(n)
    p = a[n - 1]
    q = a[n].copy()
    for size in range(k, n + 2 - k):
        add_shifted_product(q, a[size - 1], a[n - size], comb(n, size - 1))

    rows = {k: a[k - 1]}
    for j in range(k, n + 1):
        new = [0] * j
        for i, v in enumerate(rows[j]):
            new[i] += (i + 1) * v
            new[i + 1] += (j - i - 1) * v
        if j + 1 - k >= k:
            add_shifted_product(new, a[k - 1], rows[j + 1 - k], comb(j, k - 1))
        rows[j + 1] = new
    if rows[n + 1] != q:
        raise ValueError("The original new row differs between the two cycle counts")
    x = Fraction(-1, 2 ** 26)
    pv, pd = value_and_derivative(p, x)
    qv, qd = value_and_derivative(q, x)
    w = qd * pv - qv * pd
    if pv <= 0 or not -2 ** 62 < w < -2 ** 61:
        raise ValueError("The negative Wronskian certificate failed")
    print(f"Two exact constructions agree. The Wronskian floor at -2^-26 is {w.__floor__()}.")


if __name__ == "__main__":
    main()
