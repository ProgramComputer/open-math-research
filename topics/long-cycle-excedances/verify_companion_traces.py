"""Check reciprocal-orbit moments through an integral companion matrix."""

import argparse
import gzip
import json
from functools import cache
from math import comb
from pathlib import Path

from flint import fmpq, fmpz_mat, fmpz_poly as Poly

X = Poly([0, 1])


@cache
def eulerian(m):
    return Poly([sum((-1)**i * comb(m+1, i) * (j+1-i)**m
                     for i in range(j+1)) for j in range(m)])


def reciprocal_transform(poly, degree):
    """Remove t+1 when needed, then write the centered Laurent sum in w=t+1/t."""
    quotient_degree = degree // 2
    if degree % 2:
        poly, rest = divmod(poly, 1 + X)
        if rest:
            raise ArithmeticError("An odd reciprocal polynomial must vanish at -1")
    coefficients = [poly[i] for i in range(2 * quotient_degree + 1)]
    if coefficients != coefficients[::-1]:
        raise ArithmeticError("Wrong reciprocal coefficients")
    value = Poly([coefficients[quotient_degree]])
    previous, current = Poly([2]), X
    for coefficient in coefficients[quotient_degree + 1:]:
        value += coefficient * current
        previous, current = current, X * current - previous
    return value


def multiplication_matrix(poly, modulus):
    degree = modulus.degree()
    matrix = fmpz_mat(degree, degree)
    column = poly % modulus
    for j in range(degree):
        for i in range(degree):
            matrix[i, j] = column[i]
        column = (X * column) % modulus
    return matrix


def orbit_trace(old, lag):
    degree = old.degree()
    derivative = X * (1 - X) * old.derivative()
    center = fmpq(lag(-1), derivative(-1)) if degree % 2 else fmpq(0)

    modulus = reciprocal_transform(old, degree)
    numerator = reciprocal_transform(lag, degree + 1)
    factor = 4 - X**2 if degree % 2 else 2 - X
    denominator = factor * modulus.derivative()

    # The multiplication operator for denominator at the companion matrix is
    # invertible. Solve against the first column of numerator at that matrix,
    # then regenerate the remaining columns by multiplying by the indeterminate.
    matrix = multiplication_matrix(denominator, modulus)
    quotient_degree = modulus.degree()
    numerator %= modulus
    rhs = fmpz_mat(quotient_degree, 1, [numerator[i] for i in range(quotient_degree)])
    column, scale = matrix.solve(rhs).numer_denom()
    operator = multiplication_matrix(Poly([column[i, 0] for i in range(quotient_degree)]),
                                     modulus)
    squared_trace = sum(operator[i, j] * operator[j, i]
                        for i in range(quotient_degree) for j in range(quotient_degree))
    return fmpq(squared_trace, scale**2) + center**2


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("rows", type=Path, help="insertion-lag.jsonl.gz")
    parser.add_argument("fixture", type=Path, help="squared-traces.jsonl.gz")
    args = parser.parse_args()

    with gzip.open(args.rows, "rt", encoding="ascii") as stream:
        rows = {(r["n"], r["k"]): Poly(r["coefficients"]) for r in map(json.loads, stream)}
    with gzip.open(args.fixture, "rt", encoding="ascii") as stream:
        fixture = {(r["n"], r["k"]): fmpq(r["sum"]) for r in map(json.loads, stream)}

    values = {}
    for n in range(5, 46):
        for k in range(3, (n + 1) // 2 + 1):
            old = rows[n, k] // X
            lag = comb(n, k-1) * eulerian(k-1) * rows[n+1-k, k]
            value = orbit_trace(old, lag)
            if value != fixture[n, k]:
                raise ArithmeticError(f"Trace mismatch at {(n, k)}")
            values[n, k] = value
    if values.keys() != fixture.keys() or len(values) != 441:
        raise ArithmeticError("Wrong set of pairs")
    maximum = max(values.values())
    maximizers = [pair for pair, value in values.items() if value == maximum]
    if maximum != fmpq(25, 36) or maximizers != [(5, 3)]:
        raise ArithmeticError(f"Unexpected maximum {maximum} at {maximizers}")
    print(f"Matched {len(values)} reciprocal-orbit moments. Maximum {maximum} at {maximizers}.")


if __name__ == "__main__":
    main()
