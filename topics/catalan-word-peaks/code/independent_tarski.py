"""Independent exact check of strict-peak Catalan words.

Usage: python3 -I topics/catalan-word-peaks/code/independent_tarski.py --through 151
Needs Python 3.9 or later and no third-party libraries.
"""
from argparse import ArgumentParser
from math import comb, gcd
from typing import NamedTuple


class State(NamedTuple):
    height: int
    last_ascent: bool
    peaks: int


def counted_rows(last_n):
    """Count 1-step up followed by a strict descent directly on the words."""
    yield [1]  # Empty word.
    if last_n == 0:
        return
    states = {State(0, False, 0): 1}  # The first letter is 0.
    for n in range(1, last_n + 1):
        row = [0] * ((n - 1) // 2 + 1)
        for state, count in states.items():
            row[state.peaks] += count
        yield row
        if n == last_n:
            break
        next_states = {}
        for (height, last_ascent, peaks), count in states.items():
            for next_height in range(height + 2):
                state = State(
                    next_height,
                    next_height == height + 1,
                    peaks + (last_ascent and next_height < height),
                )
                next_states[state] = next_states.get(state, 0) + count
        states = next_states


def binomial_row(n):
    """Evaluate the shifted binomial formula at u=t-1."""
    if n == 0:
        return [1]
    degree = (n - 1) // 2
    row = [0] * (degree + 1)
    for k in range(degree + 1):
        numerator = comb(n - k, k) * comb(2 * n - 3 * k, n - 2 * k - 1)
        coefficient, remainder = divmod(numerator, n - k)
        if remainder:
            raise ArithmeticError(f"Nonintegral binomial count at {n=}, {k=}")
        for j in range(k + 1):
            row[j] += coefficient * comb(k, j) * (-1) ** (k - j)
    return row


def primitive(poly):
    """Strip trailing zeros and rescale by a positive factor."""
    while poly and not poly[-1]:
        poly.pop()
    if poly:
        content = gcd(*poly)
        if content > 1:
            poly = [c // content for c in poly]
    return poly


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


def derivative(poly):
    return [k * c for k, c in enumerate(poly) if k]


def sign(value):
    return (value > 0) - (value < 0)


def variations(values):
    nonzero = [value for value in values if value]
    return sum(a != b for a, b in zip(nonzero, nonzero[1:]))


def sturm_variation_drop(p, q):
    """Signed Euclidean chain for (p,q) and endpoint variation difference."""
    chain = [p]
    q = remainder(q, p)
    while q:
        chain.append(q)
        p, q = q, [-c for c in remainder(p, q)]
    left = variations([sign(f[-1]) * (-1) ** (len(f) - 1) for f in chain])
    right = variations([sign(f[0]) for f in chain])
    return left - right, len(chain[-1]) - 1


def check(last_n):
    coefficients = 0
    previous = [1]
    for n, row in enumerate(counted_rows(last_n)):
        if row != binomial_row(n) or min(row) <= 0:
            raise ArithmeticError(f"Count mismatch or nonpositive coefficient at {n=}")
        degree = len(row) - 1
        if sturm_variation_drop(row, derivative(row)) != (degree, 0):
            raise ArithmeticError(f"Simple negative-root count failed at {n=}")
        prior_degree = len(previous) - 1
        if n > 0 and degree - prior_degree not in (0, 1):
            raise ArithmeticError(f"Unexpected degree change at {n=}")
        if prior_degree:
            # At the jth prior root from the right, the derivative sign is
            # (-1)^(j-1). The claimed orientation is new-row sign (-1)^j.
            # The residue of row/previous is row(alpha)/previous'(alpha),
            # whose sign equals row(alpha)*previous'(alpha). Its exact Cauchy
            # index therefore gives the desired Sturm–Tarski query. Degree
            # reduction of the numerator only removes a polynomial part.
            if sturm_variation_drop(previous, row) != (-prior_degree, 0):
                raise ArithmeticError(f"Strict consecutive orientation failed at {n=}")
        coefficients += len(row)
        previous = row
    print(f"Verified {last_n + 1} Catalan rows, {last_n} pairs, and {coefficients} coefficients.")


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--through", type=int, default=151)
    arguments = parser.parse_args()
    if arguments.through < 0:
        parser.error("--through must be nonnegative")
    check(arguments.through)


if __name__ == "__main__":
    main()
