"""Check scalar margins in the front and separated-pole arguments.

Run with python3. Every comparison uses integers or Fraction. The review
gives the analytic monotonicity arguments that reduce to these comparisons.
"""

from fractions import Fraction as Q


def exp_lower(x, degree=40):
    """A lower bound on exp(x) for positive rational x."""
    term = total = Q(1)
    for index in range(1, degree + 1):
        term *= x / index
        total += term
    return total


def atan_partial(x, terms):
    """An alternating arctangent sum, lower for even terms."""
    return sum((-1) ** index * x ** (2 * index + 1) / (2 * index + 1)
               for index in range(terms))


def pi_bounds():
    # Machin's identity and alternating-series enclosures.
    x, y = Q(1, 5), Q(1, 239)
    tangent_double = 2 * x / (1 - x * x)
    tangent_quadruple = 2 * tangent_double / (1 - tangent_double ** 2)
    assert (tangent_quadruple - y) / (1 + tangent_quadruple * y) == 1
    pi_lower = Q(333, 106)
    pi_upper = Q(22, 7)
    assert pi_lower < 16 * atan_partial(x, 4) - 4 * atan_partial(y, 3)
    assert 16 * atan_partial(x, 3) - 4 * atan_partial(y, 2) < pi_upper
    return pi_lower, pi_upper


def check_envelopes(pi_lower):
    size = 10_000
    sqrt_size = 100
    half_word_exponent = Q(size - 1, sqrt_size)
    binomial_exponent = Q(25, 4)

    # Lower acceptance envelope and the small-k lag regime.
    geometric_tail = 1 / (exp_lower(binomial_exponent) - 1)
    assert geometric_tail < Q(1, 500)
    assert 2 * geometric_tail < Q(1, 250)
    assert size / exp_lower(half_word_exponent) < Q(1, 1000)
    assert Q(1, 250) + Q(1, 1000) < Q(1, 100)
    assert Q(99, 100) / (1 + Q(8, 3) * Q(3, 4)) == Q(33, 100)
    assert Q(1, 500) / Q(33, 100) < Q(8, 25)

    # The four-term alternating log(1+x) lower bound at x=1/2.
    log_three_halves_lower = sum((-1) ** (index + 1) * Q(1, 2) ** index / index
                                 for index in range(1, 5))
    assert log_three_halves_lower - Q(1, 3) > Q(1, 15)
    assert exp_lower(Q(4)) > 50
    assert Q(3, 2) * 5 / exp_lower(Q(10)) < Q(1, 100)

    # Maximum of the local residual/old coefficient ratio and the remote tail.
    assert Q(100, 99) * (1 + Q(8, 3) * Q(151, 80)) < Q(61, 10)
    assert Q(100, 99) * (Q(1, 2 * sqrt_size) + Q(2, 3)) < 1
    assert size / exp_lower(Q(size, 50)) < Q(1, 10_000)

    # Squared Stirling bound with exp(x) <= 1/(1-x) for x in [0,1).
    peak_upper_squared = 1 / ((1 - Q(1, 12 * size)) ** 2 * 150 * pi_lower)
    assert peak_upper_squared < Q(47, 1000) ** 2
    assert Q(sqrt_size, 2 * (size + 1)) < Q(1, 200)
    assert Q(61, 10) * (Q(47, 1000) + Q(1, 200)) + Q(1, 10_000) < Q(8, 25)
    assert 2 * size * sqrt_size / exp_lower(half_word_exponent) < Q(1, 100)
    assert Q(8, 25) + Q(1, 100) == Q(33, 100)


def check_front(pi_lower, pi_upper):
    ratio = Q(51, 10)
    assert Q(100, 99) * (1 + Q(8, 3) * Q(151, 100)) < ratio
    assert ratio * Q(7, 6) < 6
    assert exp_lower(1 / Q(9, 25) ** 2) > 2200
    assert 2 * ratio / exp_lower(Q(10_000, 36)) < Q(6, 2200)
    assert Q(7, 20) + Q(1, 100) == Q(9, 25)
    assert Q(1, 2) - Q(9, 25) == Q(7, 50)
    assert Q(7, 50) * 100 == 14
    assert Q(18, 7) + 1 < 4
    assert Q(100, 99) < 8
    assert Q(100, 99) * Q(8, 3) * Q(18, 7) < 8

    def tail_sum(s):
        return 1 / (1 - s) ** 2 - 1

    offset_radius = Q(1, 8)
    for z_min, z_max, s, error in (
        (1 - offset_radius, 1 + offset_radius, Q(1, 300), Q(1, 10)),
        (Q(1, 2), Q(1, 2), Q(3, 500), Q(1, 2)),
        (Q(3), Q(3), Q(9, 1000), Q(2)),
    ):
        assert Q(6, 2200) * max(z_max, 1 / z_min) < s
        assert (ratio + 8 * z_max) * tail_sum(s) < error

    s = Q(1, 300)
    derivative_error = ratio * ((1 + s) / (1 - s) ** 3 - 1) + 18 * s / (1 - s) ** 3
    assert derivative_error < Q(3, 20)
    # The ratio of successive ell(ell+1)s^ell is at most (16/14)s for ell >= 14.
    tail_gain = 36 * 14 * 15 * s ** 14 / (1 - Q(16, 14) * s)
    assert tail_gain < Q(1, 1000)
    assert Q(8, 25) * (1 + Q(9, 8) + Q(1, 10)) + Q(1, 1000) < Q(18, 25)
    assert Q(18, 25) < 1 - Q(3, 20)

    assert Q(7, 8) * Q(83, 117) > Q(1, 2)
    assert Q(9, 8) * Q(117, 83) * Q(3, 2) < 3
    assert Q(7, 8) * Q(83, 100) * 2 > Q(1, 2)
    assert Q(9, 8) * Q(117, 100) * 2 < 3

    assert exp_lower(1 / (2 * Q(9, 25) ** 2)) > Q(9, 8) * Q(51, 5)
    angle_coefficient_lower = Q(7, 20) * pi_lower
    angle_coefficient_upper = Q(7, 20) * pi_upper
    assert angle_coefficient_lower ** 2 * (1 - angle_coefficient_upper ** 2 / 60_000) ** 2 > Q(6, 5)


def check_separated_poles(pi_upper):
    # Spacing-two comparison with half the weighted tail integral from nine.
    def kernel(index):
        return 1 + Q(index * index - 1, 100)

    weighted_finite_tail = sum(index / kernel(index) ** 50 for index in (3, 5, 7, 9))
    weighted_integral_tail = kernel(9) ** (-49) / (4 * Q(1, 100) * 49)
    assert 99 * Q(9 ** 2, 100) > Q(99, 100)
    assert weighted_finite_tail + weighted_integral_tail < Q(1, 10)

    # The integral estimates for w_p and V_h and the resulting remainder margins.
    assert 32 // 3 - 1 >= 8
    assert Q(9, 32) * pi_upper ** 2 * Q(96, 29) < 4 ** 2
    assert Q(9, 8) * pi_upper < 4
    eta = Q(1, 1000)
    assert 12 * 4 * eta / (1 - 4 * eta) < Q(1, 20)
    assert 30 * 8 * eta / (1 - 8 * eta) < Q(1, 4)

    value_error = Q(1, 15) + Q(1, 20)
    derivative_error = Q(1, 5) + Q(1, 4)
    assert value_error == Q(7, 60)
    assert 1 - value_error ** 2 > Q(19, 20) ** 2
    assert Q(19, 20) - derivative_error == Q(1, 2)
    assert (Q(3, 8) * pi_upper) ** 2 * 3 < (Q(41, 10) - 2) ** 2
    assert Q(41, 10) + Q(1, 20) < 5
    assert (3 * pi_upper / 4) ** 2 < 4000 * (Q(1, 10) - Q(2, 2000)) ** 2

    # Optional extension to residual m sin(theta)^2 >= 1/2.
    assert (3 * pi_upper / 4) ** 2 * 3 < 5 ** 2
    assert 2 + 3 * pi_upper / 4 < Q(22, 5)
    assert Q(22, 5) + Q(1, 20) < 5


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run this checker with assertions enabled (omit -O).")
    lower, upper = pi_bounds()
    check_envelopes(lower)
    check_front(lower, upper)
    check_separated_poles(upper)
    print("All rational bounds passed.")
