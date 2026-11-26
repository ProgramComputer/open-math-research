"""Verify the 20 exceptional rows of the three-column sign proof.

This script uses integer counts and exact rational Sturm division. Coefficients
are stored in ascending order throughout. It writes one JSON record per row.
"""

from collections import defaultdict
from fractions import Fraction
from itertools import product
import json
from math import comb


PREFIX_END = 19
ROW_TYPES = tuple(row for row in product(range(2), repeat=3) if sum(row) <= 2)


def normalized_coefficients(n):
    """Count the first two columns after fixing the third by inclusion-exclusion."""
    return [
        sum(
            (-1) ** j * comb(k, j) * comb(n - j, k - j) ** 2
            for j in range(k + 1)
        )
        for k in range(n + 1)
    ]


def row_transfer():
    """Generate original diagonal coefficients from the seven binary row types."""
    states = {(0, 0, 0): 1}
    for n in range(PREFIX_END + 1):
        yield [states.get((k, k, k), 0) for k in range(n + 1)]
        if n == PREFIX_END:
            return
        next_states = defaultdict(int)
        for (i, j, k), count in states.items():
            for a, b, c in ROW_TYPES:
                next_states[i + a, j + b, k + c] += count
        states = next_states


def negative_remainder(dividend, divisor):
    remainder = dividend[:]
    while remainder and len(remainder) >= len(divisor):
        quotient = remainder[-1] / divisor[-1]
        shift = len(remainder) - len(divisor)
        for degree, coeff in enumerate(divisor):
            remainder[degree + shift] -= quotient * coeff
        while remainder and remainder[-1] == 0:
            remainder.pop()
    return [-coeff for coeff in remainder]


def sign(value):
    return (value > 0) - (value < 0)


def variations(signs):
    nonzero_signs = [s for s in signs if s]
    return sum(a != b for a, b in zip(nonzero_signs, nonzero_signs[1:]))


def sturm_signature(coefficients):
    """Return the exact signed endpoints, degree sequence and root count."""
    polynomial = list(map(Fraction, coefficients))
    if polynomial[0] <= 0 or polynomial[-1] <= 0:
        raise ValueError("Expected positive constant and leading coefficients")
    chain = [polynomial]
    derivative = [i * polynomial[i] for i in range(1, len(polynomial))]
    if derivative:
        chain.append(derivative)
        while remainder := negative_remainder(chain[-2], chain[-1]):
            chain.append(remainder)
    degrees = [len(term) - 1 for term in chain]
    minus_infinity = [(-1) ** degree * sign(term[-1])
                      for degree, term in zip(degrees, chain)]
    zero = [sign(term[0]) for term in chain]
    return {
        "chain_degrees": degrees,
        "signs_minus_infinity": minus_infinity,
        "signs_at_zero": zero,
        "squarefree": degrees[-1] == 0,
        "negative_roots": variations(minus_infinity) - variations(zero),
    }


def main():
    for n, original in enumerate(row_transfer()):
        normalized = normalized_coefficients(n)
        if original != [value * comb(n, k) for k, value in enumerate(normalized)]:
            raise ValueError(f"The independent counts disagree for n={n}")
        degree = 2 * n // 3
        if any(normalized[degree + 1:]) or any(value <= 0 for value in normalized[:degree + 1]):
            raise ValueError(f"Unexpected support for n={n}")
        original = original[:degree + 1]
        normalized = normalized[:degree + 1]
        checks = [sturm_signature(coeffs) for coeffs in (original, normalized)]
        if any(not check["squarefree"] or check["negative_roots"] != degree
               for check in checks):
            raise ValueError(f"The negative simple root count failed for n={n}")
        print(json.dumps({
            "n": n,
            "degree": degree,
            "original_coefficients": original,
            "normalized_coefficients": normalized,
            "original_sturm": checks[0],
            "normalized_sturm": checks[1],
        }, separators=(",", ":")))


if __name__ == "__main__":
    main()
