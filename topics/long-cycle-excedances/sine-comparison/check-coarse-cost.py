"""Standalone rational check of a small arithmetic certificate for the signed determinant."""

from fractions import Fraction
from functools import cache
from math import ceil, factorial, floor, isqrt


PRODUCT_SCALE = 2**32
POLE_SCALE = 2**56
TOP = 240
SLABS = (4, 6, 10, 16, 22, 28, 34, 40, 44, 48)
SHAPES = tuple(Fraction(1, d) for d in (48, 24, 12, 6, 3, 2)) + (Fraction(3, 4), Fraction(1))
ODDS = tuple(range(-63, 64, 2))
CENTERS = range(-65, 66, 2)


@cache
def pole_data(shape):
    """Round each signed weight and both discrete tails outward at 2^56."""
    assert 3 * shape * 63**2 >= 1
    weights = {p: ceil(POLE_SCALE / (1 + shape * (p * p - 1))**96) for p in ODDS}
    tail1 = ceil(POLE_SCALE / (190 * shape * (1 + shape * (63**2 - 1))**95))
    tail0 = ceil(Fraction(tail1, 63))
    half_tail = ceil(Fraction(tail0, 2))
    return weights, tail1, half_tail


def star_numerator(upper, k_floor):
    shape = (1 - Fraction(1, k_floor)) / (160 * upper)
    weights, _, half = pole_data(shape)
    head = max(
        sum(ceil(Fraction(w, abs(p - a))) for p, w in weights.items() if p != a)
        for a in CENTERS
    )
    return ceil(Fraction(256 * (head + half), POLE_SCALE))


@cache
def moments(y):
    assert y in SHAPES
    weights, tail1, half = pole_data(y / 160)
    zeroth = Fraction(sum(weights.values()) + 2 * half, POLE_SCALE)
    first = Fraction(sum(abs(p) * w for p, w in weights.items() if abs(p) > 1) + tail1, POLE_SCALE)
    return zeroth, first


def round_shape(y):
    return max(value for value in SHAPES if value <= y)


def degree_mass(i, k_floor):
    if i < 4:
        return Fraction(0)
    if i == 4:
        return Fraction(1)
    if i <= 8:
        left = Fraction(i - 1, 4) - Fraction(1, k_floor)
        extra = Fraction(1, 4 * k_floor) if i == 8 else Fraction(0)
        return 1/left - Fraction(4, i) + extra
    return (Fraction(1, 4) + Fraction(1, k_floor)) / (2 * factorial((i - 1) // 4))


def rounded_counts(lower, upper, radius, star):
    k_floor = 10000 // upper
    masses = [degree_mass(i, k_floor) for i in range(TOP + 1)]
    upper_linear = [ceil(PRODUCT_SCALE * mass * star / radius) for mass in masses]
    lower_linear = [
        floor(PRODUCT_SCALE * mass * Fraction(3, 4) / radius) if lower == 4 else 0 for mass in masses
    ]
    counts = [PRODUCT_SCALE]
    for b in range(1, TOP + 1):
        numerator = sum(i * upper_linear[i] * counts[b - i] for i in range(4, b + 1))
        counts.append(ceil(Fraction(numerator, b * PRODUCT_SCALE)))
    return counts, lower_linear


def principal_error(block):
    if block == 0:
        return Fraction(4, 7)
    if block == 1:
        return Fraction(453, 1000)
    offset = Fraction(1, 2) if block == 2 else Fraction(547, 1000)
    return min(Fraction(4, 7) - offset, Fraction(block + 1, 2 * block * factorial(block)))


def slab_cost(lower, upper):
    radius = Fraction(isqrt(192000) // upper, 4)
    star_num = star_numerator(upper, 10000 // upper)
    star = Fraction(star_num, 256)
    counts, lower_linear = rounded_counts(lower, upper, radius, star)
    principal = Fraction(1, 10000)
    other = regular = multiple = Fraction(0)
    for b, count in enumerate(counts):
        mass = Fraction(count, PRODUCT_SCALE)
        block = max(0, lower - (b + 3) // 4)
        principal += 2 * principal_error(min(40, block)) * mass
        if b > 5 * (upper - 1):
            continue
        y = round_shape(max(Fraction(1, upper), 1 - Fraction(b, 4 * lower)))
        zeroth, first = moments(y)
        other += mass * first * (Fraction(4, 7) if b + 8 <= 4 * lower else 1)
        factorial_weight = Fraction(1, 2 * factorial(block)) if block >= 2 else Fraction(1)
        regular += mass * factorial_weight * zeroth / radius
        if b > 4 * (lower - 1):
            gap = count - lower_linear[b]
            assert gap >= 0
            multiple += Fraction(gap, PRODUCT_SCALE) * radius * upper * Fraction(5, 6) * zeroth
    outer, _ = moments(round_shape(Fraction(1, upper)))
    single = outer * star / (2 * factorial(lower - 1) * radius**2)
    carrier = Fraction(54, 55) if upper <= 10 else Fraction(6000, 12243)
    costs = (principal, other, regular, multiple + single)
    return star_num, costs, carrier


def main():
    for lower, upper in zip(SLABS, SLABS[1:]):
        numerator, costs, carrier = slab_cost(lower, upper)
        caps = [ceil(10**6 * cost) for cost in costs]
        margin = carrier - sum(costs)
        rounded = carrier - Fraction(sum(caps), 10**6)
        assert margin >= rounded > Fraction(93, 1000)
        print(
            lower, upper, "star/256", numerator, "costs in upward millionths", *caps,
            "rounded margin floor", floor(10**6 * rounded),
            "unrounded margin floor", floor(10**6 * margin),
        )


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run with assertions enabled")
    main()
