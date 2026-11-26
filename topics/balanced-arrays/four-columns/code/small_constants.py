"""Exact rational enclosure for the small-t saddle error at n*t = 40."""

from fractions import Fraction as Q
from math import factorial, isqrt


def sqrt_bounds(x):
    scale = 10**6
    lower = isqrt(x.numerator * scale**2 // x.denominator)
    return Q(lower, scale), Q(lower + 1, scale)


def pow_three_halves_upper(x):
    return x * sqrt_bounds(x)[1]


def exp_negative_upper(x):
    return 1 / sum(x**j / factorial(j) for j in range(21))


def gaussian_tail_upper(m, x):
    if x == 0:
        return Q(1)
    below, above = sqrt_bounds(x)
    bound = 1 / below
    rising = Q(1)
    for j in range(1, m + 1):
        rising *= Q(2 * j - 1, 2)
        bound += x ** (j - 1) * above / rising
    return Q(3, 5) * bound * exp_negative_upper(x)


for u, ratio in ((Q(1, 4), Q(37, 50)), (Q(1, 2), Q(3, 5)), (Q(1), Q(1, 3))):
    d1 = Q(1, 2) - u / 8 - sqrt_bounds(u / 27)[1]
    d2 = 1 - 2 * u / 3
    d3 = 1 - u / 3 + (Q(3, 2) - u) * d1
    d4 = (3 - u) * (1 - u / 3)
    for bound, leading in zip((d1, d2, d3, d4), (Q(1, 2), Q(1), Q(7, 4), Q(3))):
        assert bound >= ratio * leading

T = 40


def local_error(alpha, q0):
    x = Q(99, 100) * alpha * T * q0
    return (
        Q(100, 99) ** 5
        * pow_three_halves_upper(2 / alpha)
        / T
        * (
            Q(15, 4) * Q(26, 45) / alpha**2 * gaussian_tail_upper(3, x)
            + gaussian_tail_upper(4, x) / alpha**3
        )
    )


error = (
    local_error(Q(37, 40), Q(0))
    + local_error(Q(3, 4), Q(1, 4))
    + pow_three_halves_upper(Q(24, 5)) * gaussian_tail_upper(1, Q(5 * T, 24))
    + pow_three_halves_upper(Q(8)) * gaussian_tail_upper(1, Q(T, 4))
    + pow_three_halves_upper(Q(8, 5)) * gaussian_tail_upper(1, Q(5 * T, 8))
    + pow_three_halves_upper(2 * Q(22, 7) * T) * exp_negative_upper(Q(T, 2))
)
assert error < Q(2, 5)
print("Normalized saddle error is less than 2/5 for 0 < t <= 1/5 and n*t >= 40.")
