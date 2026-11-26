"""Exact scalar checks for the three-cycle band beginning at n=2200."""
from fractions import Fraction as Q
from itertools import combinations
from math import factorial, prod


def exp_lower(x, order=35):
    return sum(x**j / factorial(j) for j in range(order + 1))


# Front coefficient envelopes, including small run weights.
for p in range(1, 25):
    a = (p + 5) // 6
    pair = sum(Q(1, j) for j in range(a, p - a + 1))
    triple = sum(
        Q(1, 2 * j * l)
        for j in range(a, p - 2 * a + 1)
        for l in range(a, p - a - j + 1)
    )
    assert pair <= Q(23, 10) and triple <= Q(19, 10)
assert exp_lower(Q(5, 3)) > 5 and exp_lower(Q(7, 5)) > 4
assert Q(6, 25) + Q(5, 3) < Q(23, 10)
assert (Q(6, 25) + Q(7, 5)) ** 2 / 2 < Q(19, 10)
assert exp_lower(Q(3)) > 20
assert Q(1000, 20**4) < Q(1, 100)
assert 1 + Q(23, 10) + Q(19, 10) + Q(1, 100) < Q(21, 4)

# Three Rouché contours and the lower derivative.
M0 = 2199
rank_bound = Q(103, 250)
R = Q(16, 3)
assert (rank_bound - Q(39, 100)) ** 2 * M0 > 1
assert exp_lower(1 / rank_bound**2) > 360
assert Q(21, 4) / Q(99, 100) < R
s = Q(1, 50)
radii_tail = Q(9, 200)
assert Q(4, 3) * R / 360 < s
assert 3 * R / 360 < radii_tail
assert R * Q(9, 4) * s / (1 - s) < Q(1, 4)
assert R * Q(3, 2) * radii_tail / (1 - radii_tail) < Q(1, 2)
assert R * 4 * radii_tail / (1 - radii_tail) < 2
assert 1 - R * (Q(9, 4) * s / (1 - s)**2 + s / (1 - s)) > Q(63, 100)

# Lag and overlap at the first middle sample.
assert (Q(1, 4) - Q(3, 4*M0)) > Q(249, 1000)
assert Q(249, 1000) * Q(751, 1000) > Q(18, 100)
assert (1 / (1 - Q(1, 12*M0)))**2 < Q(95, 100)**2 * 2 * Q(157, 50) * Q(18, 100)
assert Q(22, 7) / 2 < Q(63, 50)**2
assert Q(63, 50)**2 < Q(3, 100)**2 * M0
run_weight_sum = Q(100, 99) * (
    Q(9, 4) * (1 + Q(63, 50)*rank_bound) / (1 - s)
    + Q(5, 4)*Q(3, 100)*s/(1-s)**2
)
assert run_weight_sum < Q(18, 5)
lag_numerator = Q(3, 2) * Q(95, 100) * Q(21, 4) * Q(18, 5)
assert lag_numerator**2 < Q(58, 100)**2 * M0
assert 1 / (2*rank_bound**2) - Q(1, 2) > 2
assert exp_lower(Q(2)) > Q(5, 4) * R
assert (Q(39, 100) * Q(22, 7))**2 < 2
c = Q(149, 100)
assert (Q(39, 100) * Q(157, 50))**2 * Q(2199, 2200) * (1-Q(2, 6*2200))**2 > c
print("Front contours, derivative > 63/100, lag < 58/100, and overlap > 149/100.")

# Center envelopes for n sin^2(theta) >= 149/100.
beta = c / 192
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

A = 14
assert c*2200 >= (4*A)**2
ns = Q(29, 10) * A
value_error = derivative_error = Q()
for h, variation in ((2, Q(7, 4)), (3, Q(3, 2))):
    value = derivative = Q()
    for chosen in combinations(poles, h):
        weight = prod(weights[p] for p in chosen)
        factors = sum(
            prod(Q(1, abs(p - q)) for q in chosen if q != p)
            for p in chosen
        )
        term = weight * factors
        value += term
        speed = Q(1, 2) if chosen == (-1, 1) else max(map(abs, chosen))
        derivative += term * speed
    divisor = factorial(h - 1) * 2 ** (h - 1)
    value += h * mass_tail * mass ** (h - 1) / divisor
    derivative += (
        h * moment_tail * mass ** (h - 1)
        + h * (h - 1) * mass_tail * moment * mass ** (h - 2)
    ) / divisor
    multiplier = variation**h / A**(h-1)
    value_error += multiplier * value
    derivative_error += multiplier * (derivative + (h-1)*value/ns)
weights, mass_tail, moment_tail = envelope(96)
old_value = sum(weights[p] for p in poles if abs(p)>1) + mass_tail
old_derivative = sum(abs(p)*weights[p] for p in poles if abs(p)>1) + moment_tail
weights, mass_tail, _ = envelope(64)
residual = sum(weights.values()) + mass_tail
assert 1 - (value_error + old_value)**2 > (Q(19, 100) + derivative_error + old_derivative)**2
assert mass * (residual + value_error) / ns < Q(16, 100)
print("Center derivative > 19/100 and lag < 16/100.")
