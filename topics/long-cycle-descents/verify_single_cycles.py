"""Independent standard-library verification of the finite part of the single-cycle theorem."""

import argparse
import json
from pathlib import Path
from functools import cache
from math import comb, factorial, gcd


@cache
def primitive_words(n, alphabet):
    # A word is a repetition of one primitive word of some divisor length.
    return alphabet**n - sum(primitive_words(d, alphabet) for d in range(1, n) if n % d == 0)


def single_cycle_coefficients(n):
    necklace_counts = []
    for q in range(1, n + 2):
        count, rem = divmod(primitive_words(n, q), n)
        if rem:
            raise ArithmeticError("Rotation orbits of primitive words must have size n")
        necklace_counts.append(count)
    row = [sum((-1)**j * comb(n + 1, j) * necklace_counts[i - j] for j in range(i + 1))
           for i in range(n + 1)]
    while row and row[-1] == 0:
        row.pop()
    if not row or min(row) < 0 or sum(row) != factorial(n - 1):
        raise ArithmeticError(f"Invalid descent counts at n={n}")
    return row


def numerator_at_negative_dyadic(coefficients, numerator, denominator):
    value = coefficients[-1]
    scale = 1
    for c in reversed(coefficients[:-1]):
        scale *= denominator
        value = c * scale - numerator * value
    return value


def verify_size(n, row):
    if n in (1, 5):
        expected = [1] if n == 1 else [0, 6, 12, 6]
        if row != expected:
            raise ArithmeticError((n, row))
        return
    if row[0] != 0 or row[1] <= 0:
        raise ArithmeticError(f"Expected a simple root at zero for n={n}")
    reduced = row[1:]
    degree = len(reduced) - 1
    # Scan strictly left from 0 through each binary interval, then to minus infinity.
    # Opposite nonzero signs force a distinct real zero in each disjoint open interval.
    previous, changes = 1, 0
    for exponent in range(-n, n + 1):
        for mantissa in range(16, 32):
            numerator = mantissa << max(exponent, 0)
            denominator = 16 << max(-exponent, 0)
            common = gcd(numerator, denominator)
            v = numerator_at_negative_dyadic(reduced, numerator // common, denominator // common)
            if v:
                sign = 1 if v > 0 else -1
                changes += sign != previous
                previous = sign
    changes += previous != (-1)**degree
    if changes != degree:
        raise ArithmeticError(f"n={n}: found {changes} disjoint sign changes for degree {degree}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-archive", type=Path, help="also compare the saved coefficients and real-root counts")
    archive = parser.parse_args().check_archive
    saved = [json.loads(line) for line in archive.read_text().splitlines()] if archive else None
    if saved is not None and len(saved) != 79:
        raise ArithmeticError("Expected exactly 79 stored polynomials")
    for size in range(1, 80):
        row = single_cycle_coefficients(size)
        verify_size(size, row)
        if saved is not None:
            record = saved[size - 1]
            distinct = len(row) - 1 - (size == 5)
            if (record["n"] != size or record["coefficients"] != row or not record["real_rooted"]
                    or record["degree"] != len(row) - 1 or record["distinct_real_roots"] != distinct):
                raise ArithmeticError(f"Archive mismatch for size {size}")
    print("Verified all 79 single-cycle polynomials by exact integer signs, including the double root at n=5.")
