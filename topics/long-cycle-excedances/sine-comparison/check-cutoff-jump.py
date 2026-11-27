"""Reproduce the joined cutoff-jump bound for each of the nine aspect intervals."""

from fractions import Fraction
from math import ceil, factorial, isqrt
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
REGULAR = runpy.run_path(str(HERE / "check-regular.py"))
COMMON = REGULAR["COMMON"]
PAIRED = COMMON["PAIRED"]
SCALE = COMMON["BIN_SCALE"]
ANGLE_THRESHOLD = Fraction(6, 5)


def rounded_pole_weights(shape):
    return {
        q: ceil(SCALE / (1 + shape * ((2*q + 1)**2 - 1))**96)
        for q in range(-32, 32)
    }


def half_tail(shape):
    assert 3 * shape * 63**2 >= 1
    first = ceil(SCALE / (190 * shape * (1 + shape * (63**2 - 1))**95))
    mass = (first + 62) // 63
    return (mass + 1) // 2


def single_cost(lower, upper, radius):
    cutoff = 10000 // upper
    outer = Fraction(1, 160*upper)
    inner = (lower - 1 - Fraction(1, cutoff)) * outer
    mass = sum(rounded_pole_weights(outer).values()) + 2*half_tail(outer)
    inner_weights = rounded_pole_weights(inner)
    head = max(
        sum((value + 2*abs(a-q)-1) // (2*abs(a-q)) for q, value in inner_weights.items() if q != a)
        for a in range(-33, 33)
    )
    star = head + half_tail(inner)
    return Fraction(mass*star, SCALE**2 * 2 * factorial(lower - 1)) / radius**2


def multiple_cost(lower, upper, radius, counts):
    cutoff = 10000 // upper
    lattice = PAIRED["prev"]
    linear = {}
    for i, degree, mass in lattice.degree_masses(cutoff, 60):
        shape = (degree - Fraction(1, cutoff)) * ANGLE_THRESHOLD / (192*upper)
        linear[i] = PAIRED["up"](mass*lattice.stars(shape)[0] / radius)
    result = Fraction(0)
    for b in range(4*(lower - 1) + 1, 5*(upper - 1) + 1):
        gap = counts[b] - linear.get(b, 0)
        assert gap >= 0
        shape = max(Fraction(1, upper), 1 - Fraction(b, 4*lower)) / 160
        result += Fraction(gap, SCALE) * radius * upper / ANGLE_THRESHOLD * REGULAR["zeroth_moment_upper"](shape)
    return result


def main():
    for line in (HERE / "carrier-output.txt").read_text().splitlines():
        lower, upper, _, _, _, _, _, reviewed, _ = map(int, line.split())
        radius = Fraction(isqrt(192000) // upper, 4)
        counts, _ = PAIRED["coefficients"](10000 // upper, lower, upper, radius, 240)
        one = single_cost(lower, upper, radius)
        multiple = multiple_cost(lower, upper, radius, counts)
        cap = ceil(10**6 * (one + multiple))
        assert cap <= reviewed
        print(lower, upper, "single", ceil(10**6 * one), "multiple", ceil(10**6 * multiple),
              "combined", cap, "reviewed", reviewed)


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run with assertions enabled")
    main()
