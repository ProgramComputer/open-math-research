"""Exact homogeneous-substitution check for the finite angular comparisons."""

from collections import defaultdict
from fractions import Fraction
from math import comb, factorial


def chebyshev_polynomials(limit):
    rows = [[1], [0, 1]]
    for k in range(2, limit + 1):
        row = [0] + [2 * coefficient for coefficient in rows[k - 1]]
        for power, coefficient in enumerate(rows[k - 2]):
            row[power] -= coefficient
        rows.append(row)
    return rows


def divided_difference(chebyshev, endpoint):
    # (T_k(endpoint) - T_k(u)) / (endpoint-u).
    return [
        sum(coefficient * endpoint ** (power - 1 - u_power)
            for power, coefficient in enumerate(chebyshev) if power > u_power)
        for u_power in range(len(chebyshev) - 1)
    ]


def comparison_polynomial(threshold):
    endpoint = Fraction(7, 10) if threshold == 4 else Fraction(4, 5)
    chebyshev = chebyshev_polynomials(threshold - 1)
    result = defaultdict(Fraction)
    for k in range(1, threshold):
        angle = divided_difference(chebyshev[k], endpoint)
        # These are the coefficients of the autocorrelation difference divided by r.
        radial = [(k - 1, Fraction(1, factorial(k)))] + [
            (2 * s + k - 1, Fraction(-1, factorial(s) * factorial(s + k)))
            for s in range(1, threshold - k)
        ]
        for r_power, coefficient in radial:
            for u_power, value in enumerate(angle):
                result[r_power, u_power] += coefficient * value
    return {powers: value for powers, value in result.items() if value}


def convolve(left, right):
    out = [Fraction()] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            out[i + j] += a * b
    return out


def positive_rectangle_bound(polynomial, low, high):
    radial_degree = max(i for i, _ in polynomial)
    angular_degree = max(j for _, j in polynomial)
    # Homogenize after r=x/(1+x) and u=(low+high*y)/(1+y).
    radial_basis = [
        [0] * i + [comb(radial_degree - i, k) for k in range(radial_degree - i + 1)]
        for i in range(radial_degree + 1)
    ]
    angular_basis = [
        convolve(
            [comb(j, k) * low**(j - k) * high**k for k in range(j + 1)],
            [comb(angular_degree - j, k) for k in range(angular_degree - j + 1)],
        )
        for j in range(angular_degree + 1)
    ]
    bound = min(
        sum(value * radial_basis[i][k] * angular_basis[j][l]
            for (i, j), value in polynomial.items())
        / (comb(radial_degree, k) * comb(angular_degree, l))
        for k in range(radial_degree + 1)
        for l in range(angular_degree + 1)
    )
    return bound


def main():
    cuts = [Fraction(-1), Fraction(-1, 2), Fraction(0), Fraction(1, 2)]
    print("threshold  exact minimum lower bound on the three rectangles")
    for threshold in range(4, 13):
        polynomial = comparison_polynomial(threshold)
        bounds = [
            positive_rectangle_bound(polynomial, lo, hi)
            for lo, hi in zip(cuts, cuts[1:])
        ]
        if min(bounds) <= Fraction(19, 100):
            raise ArithmeticError(f"angular positivity bound too small at j={threshold}")
        print(threshold, *(str(bound) for bound in bounds), sep="  ")


if __name__ == "__main__":
    main()
