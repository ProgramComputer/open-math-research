"""Exact finite checks for the Mehler reduction of balanced four-column arrays."""
from argparse import ArgumentParser
from functools import cache
from math import comb, factorial, gcd
import json
import sys


@cache
def pair_count(rows, quota):
    if not 0 <= 2 * quota <= rows:
        return 0
    return comb(rows, 2 * quota) * comb(2 * quota, quota)


def array_count(n, k):
    """Independent array count by splitting columns into pairs."""
    total = 0
    for a in range(k + 1):
        for b in range(k + 1):
            residual = n - a - b
            total += (
                comb(n, a) * comb(n - a, b)
                * pair_count(residual, k - a) * pair_count(residual, k - b)
            )
    return total


def kernel_count(n, k):
    """Positive finite coefficient formula (2) in the accompanying note."""
    defect = n - 2 * k
    total = 0
    weight = 1
    for j in range(k + 1):
        h = k - j
        m = defect + j
        inner = sum(
            comb(m, s) ** 2 * comb(defect + 2 * j + h - s, h - s)
            for s in range(min(m, h) + 1)
        )
        total += weight * inner
        weight, remainder = divmod(weight * (4 * defect + 4 * j + 2), j + 1)
        if remainder:
            raise ArithmeticError("Unexpected nonintegral kernel weight")
    return total


def primitive(polynomial):
    while polynomial and polynomial[-1] == 0:
        polynomial.pop()
    if polynomial:
        content = gcd(*polynomial)
        if content > 1:
            polynomial = [c // content for c in polynomial]
    return polynomial


def remainder(left, right):
    """An integer polynomial positively proportional to the rational remainder."""
    result = left.copy()
    while len(result) >= len(right):
        offset = len(result) - len(right)
        lead = right[-1]
        multiplier = result[-1] * (1 if lead > 0 else -1)
        result = [abs(lead) * c for c in result]
        for j, c in enumerate(right):
            result[offset + j] -= multiplier * c
        result = primitive(result)
    return result


def derivative(polynomial):
    return [power * coefficient for power, coefficient in enumerate(polynomial) if power]


def sign(value):
    return (value > 0) - (value < 0)


def variations(values):
    nonzero = [value for value in values if value]
    return sum(a != b for a, b in zip(nonzero, nonzero[1:]))


def endpoint_variations(p, q):
    """Signed Euclidean sequence and variations at minus infinity and zero."""
    chain = [p]
    q = remainder(q, p)
    while q:
        chain.append(q)
        p, q = q, [-c for c in remainder(p, q)]
    left = variations([sign(f[-1]) * (-1) ** (len(f) - 1) for f in chain])
    right = variations([sign(f[0]) for f in chain])
    return left, right, len(chain[-1]) - 1


def check(last_n, archive):
    previous = [1]
    coefficients = 0
    for n in range(last_n + 1):
        degree = n // 2
        row = [kernel_count(n, k) for k in range(degree + 1)]
        original = [array_count(n, k) for k in range(degree + 1)]
        for k, (kernel, actual) in enumerate(zip(row, original)):
            if kernel <= 0 or kernel * factorial(n) != actual * factorial(k)**2 * factorial(n-2*k):
                raise ArithmeticError(f"Coefficient mismatch at {n=}, {k=}")
        roots = endpoint_variations(row, derivative(row))
        left, right, gcd_degree = roots
        if left - right != degree or gcd_degree != 0:
            raise ArithmeticError(f"Simple negative root count failed at {n=}")
        previous_degree = len(previous) - 1
        pair = endpoint_variations(previous, row)
        left, right, gcd_degree = pair
        # The Cauchy index sums the signs of the residues of row/previous on
        # the negative real line. At the jth old root from the right, the
        # required sign of row is (-1)^j, opposite to previous'.
        if left - right != -previous_degree or gcd_degree != 0:
            raise ArithmeticError(f"Oriented consecutive check failed at {n=}")
        if archive:
            print(json.dumps({
                "n": n,
                "a": original,
                "H": row,
                "sturm": roots,
                "cauchy_index": pair if n else None,
            }, separators=(",", ":")))
        coefficients += len(row)
        previous = row
    print(
        f"Verified {last_n + 1} Mehler rows, {last_n} consecutive pairs, "
        f"and {coefficients} coefficient identities.",
        file=sys.stderr,
    )


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--through", type=int, default=30)
    parser.add_argument("--jsonl", action="store_true")
    args = parser.parse_args()
    if args.through < 0:
        parser.error("--through must be nonnegative")
    check(args.through, args.jsonl)


if __name__ == "__main__":
    main()
