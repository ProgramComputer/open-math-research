"""Rational bounds for the occupied-pole estimate through old size 4k-1."""
from fractions import Fraction as Q
from itertools import combinations
from math import factorial, prod

beta = Q(1, 160)
poles = tuple(range(-9, 10, 2))


def kernel(p):
    return 1 + beta * (p * p - 1)


def envelope(exponent):
    weights = {p: kernel(p) ** (-exponent) for p in poles}
    assert (2 * exponent - 1) * beta * 9**2 > 1 - beta
    moment_tail = kernel(9) ** (1 - exponent) / (2 * beta * (exponent - 1))
    return weights, moment_tail / 9, moment_tail


weights, mass_tail, moment_tail = envelope(23)
mass = sum(weights.values()) + mass_tail
moment = sum(abs(p) * weights[p] for p in poles) + moment_tail
assert mass < Q(11, 4)

for h, mass_bound, derivative_bound in (
    (2, Q(212, 100), Q(457, 100)),
    (3, Q(43, 100), Q(14, 10)),
):
    value = Q()
    derivative = Q()
    for chosen in combinations(poles, h):
        weight = prod(weights[p] for p in chosen)
        factors = sum(
            prod(Q(1, abs(p - q)) for q in chosen if q != p)
            for p in chosen
        )
        term = weight * factors
        value += term
        derivative += term * max(map(abs, chosen))
    divisor = factorial(h - 1) * 2 ** (h - 1)
    value += h * mass_tail * mass ** (h - 1) / divisor
    derivative += (
        h * moment_tail * mass ** (h - 1)
        + h * (h - 1) * mass_tail * moment * mass ** (h - 2)
    ) / divisor
    assert value < mass_bound
    assert derivative < derivative_bound
    print(f"h={h}: U_h < {mass_bound}, V_h < {derivative_bound}")

weights, mass_tail, moment_tail = envelope(96)
assert sum(weights[p] for p in poles if abs(p) > 1) + mass_tail < Q(1, 50)
assert sum(abs(p) * weights[p] for p in poles if abs(p) > 1) + moment_tail < Q(1, 16)
weights, mass_tail, _ = envelope(64)
assert sum(weights.values()) + mass_tail < Q(21, 10)

a = 27
ns = Q(29, 10) * a
value_error = 4 * Q(212, 100) / a + 8 * Q(43, 100) / a**2
power_derivative = 4 * Q(457, 100) / a + 8 * Q(14, 10) / a**2
assert value_error < Q(8, 25)
assert power_derivative < Q(7, 10)
assert 2 * value_error / ns < Q(9, 1000)
assert 1 - (Q(8, 25) + Q(1, 50)) ** 2 > Q(47, 50) ** 2
assert Q(47, 50) - Q(1, 16) - Q(7, 10) - Q(9, 1000) > Q(4, 25)
assert Q(11, 4) * (Q(21, 10) + Q(8, 25)) / ns < Q(9, 100)
assert Q(6, 5) * 10_000 >= (4 * a) ** 2
print("Principal and residual pole bounds pass.")
print("Uniform central derivative margin > 4/25 and insertion upper bound < 9/100.")
