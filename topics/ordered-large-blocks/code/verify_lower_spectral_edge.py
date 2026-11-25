"""Verify the rational comparisons in the all-threshold lower-edge proof."""

from fractions import Fraction as Q
from math import factorial


def exp_lower(x):
    return sum(x**s / factorial(s) for s in range(7))


def exp_upper(x):
    return exp_lower(x) + x**7 / (factorial(7) * (1 - x/8))


def tail_upper(j, x):
    return x/j + x**2 / (j*(j+1) * (1 - x/(j+2)))


def verify():
    lower_six = Q(83, 100)
    upper = {4: Q(19, 20), 5: Q(89, 100), 6: Q(17, 20), 7: Q(5, 6)}
    if not exp_upper(Q(1)) - 2 < 2*(Q(1, 3) + Q(1, 12)):
        raise ArithmeticError("failed lower bound on the j=3 critical radius")
    if not exp_upper(lower_six) - 2 < 2*(lower_six/6 + lower_six**2/42):
        raise ArithmeticError("failed lower bound on the j=6 critical radius")
    for j, x in upper.items():
        if not exp_lower(x) - 2 > 2*tail_upper(j, x):
            raise ArithmeticError(f"failed upper bound on the j={j} critical radius")

    radius = upper[7]
    if not (radius**2 - radius + 1)*exp_upper(radius) < 2:
        raise ArithmeticError("failed infinite negative moment bound for j>=7")

    leading_long = Q(4, 5) * (sum(lower_six**s/factorial(s) for s in range(4)) - 2)
    for j in (4, 5, 6):
        x = upper[j]
        weights = [x**s/factorial(s) for s in range(2, j)]
        small_angle = sum(a*k*k for k, a in enumerate(weights, start=1)) - leading_long
        large_angle = sum(a*c for a, c in zip(weights, (1, Q(7, 2), Q(25, 4), 16)))
        if max(small_angle, large_angle) >= 1:
            raise ArithmeticError(f"failed trigonometric bound at j={j}")
    print("All rational lower-edge comparisons verified.")


if __name__ == "__main__":
    verify()
