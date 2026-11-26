"""Replay the cycle-marked resultants from largest-label insertion using SymPy."""

import json
from fractions import Fraction
from math import comb
from pathlib import Path

import sympy as sp


def eulerian_step(poly, degree, y):
    return sp.expand((1 + 2 * degree * y) * poly + y * (1 - 4 * y) * sp.diff(poly, y))


def main():
    u, y = sp.symbols("u y")
    records = json.loads(Path(__file__).with_name("marked-resultants.json").read_text())
    expected = {(row["old_n"], row["k"]): row for row in records}
    expected_domain = {(n, k) for n in range(3, 16) for k in range(3, n + 1)}
    if len(records) != len(expected_domain) or set(expected) != expected_domain:
        raise ValueError("Archive does not cover exactly the declared 91 pairs")

    eulerian = {1: sp.Integer(1)}
    for size in range(2, 16):
        eulerian[size] = eulerian_step(eulerian[size - 1], size - 2, y)

    for k in range(3, 16):
        rows = {k: eulerian[k - 1]}
        for n in range(k, 16):
            new = eulerian_step(rows[n], n - 2, y)
            if n + 1 - k >= k:
                new += comb(n, k - 1) * u * y * eulerian[k - 1] * rows[n + 1 - k]
            rows[n + 1] = sp.expand(new)
            if k == 3 and n + 1 == 6:
                point = {y: sp.I / 8, u: (-11 + 3 * sp.I) / 5}
                if sp.expand(rows[6].subs(point)) != 0:
                    raise ValueError("The upper-half-plane obstruction failed")
            res = sp.Poly(sp.resultant(rows[n], rows[n + 1], y), u)
            if res.eval(0) == 0:
                raise ValueError(f"Common gamma root at the Eulerian endpoint for {(n, k)}")
            sign = int(sp.sign(res.eval(0)))
            degree = res.degree()
            coefficients = [sign * int(res.nth(j)) for j in range(degree + 1)]
            bernstein = [
                sum(Fraction(comb(i, j), comb(degree, j)) * coefficients[j] for j in range(i + 1))
                for i in range(degree + 1)
            ]
            row = expected[n, k]
            if (coefficients != row["normalized_resultant"]
                    or list(map(str, bernstein)) != row["bernstein"]
                    or min(bernstein) <= 0 or row["all_bernstein_positive"] is not True):
                raise ValueError(f"Failed exact Bernstein comparison for {(n, k)}")
    print(f"All {len(records)} cycle-marked resultants and Bernstein vectors agree.")


if __name__ == "__main__":
    main()
