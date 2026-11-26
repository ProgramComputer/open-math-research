"""Independent corank-two counts and exact rational sign probes."""
import argparse
from fractions import Fraction
import json
from math import comb, isqrt
from pathlib import Path


def binomial(n, k):
    return comb(n, k) if 0 <= k <= n else 0


def specified_bad(n, d, k, ell):
    """Count assignments when a fixed ell rows each omit at most one column."""
    choices = [binomial(n - ell, k - ell + b) for b in range(ell + 1)]
    used = [1] + [0] * ell
    for _ in range(d):
        used = [sum(comb(h, b) * choices[b] * used[h - b] for b in range(h + 1))
                for h in range(ell + 1)]
    return sum(comb(ell, h) * used[h] for h in range(ell + 1))


def coefficients(n, d):
    cap = d - 2
    return [sum((-1)**ell * comb(n, ell) * specified_bad(n, d, k, ell)
                for ell in range(min(n, d * k // (d - 1)) + 1))
            for k in range(n * cap // d + 1)]


def rational_node(square):
    # A dyadic remainder on this fixed grid is negligible at these nodes.
    scale = 2**256
    value = isqrt(scale**2 * square.numerator // square.denominator)
    return Fraction(value, scale)


def evaluate(poly, value):
    result = Fraction(0)
    for coefficient in reversed(poly):
        result = result * value + coefficient
    return result


def verify(n, r, d, poly):
    degree = len(poly) - 1
    assert degree == n*r//d and poly[0] == 1 and all(a > 0 for a in poly)
    probes = [rational_node(Fraction(poly[k-1], poly[k+1])) for k in range(1, degree)]
    assert 0 < probes[0] and all(a < b for a, b in zip(probes, probes[1:]))
    assert all((-1)**k * evaluate(poly, -point) > 0 for k, point in enumerate(probes, 1))
    print(f"({n},{r},{d}): {len(probes)} exact finite signs, {degree} simple negative roots")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archives", type=Path, nargs="*")
    args = parser.parse_args()
    if not args.archives:
        for d in (12, 11):
            verify(36, d-2, d, coefficients(36, d))
    for path in args.archives:
        rows = [json.loads(line) for line in path.read_text().splitlines()]
        n, r, d = (rows[0][field] for field in ("n", "r", "d"))
        assert all((row["n"], row["r"], row["d"], row["k"]) == (n, r, d, k)
                   and row["lower"] == row["upper"]
                   for k, row in enumerate(rows))
        verify(n, r, d, [row["lower"] for row in rows])
