"""Independent rational checks for the explicit uniform cutoff."""

from fractions import Fraction as Q


def exp_lower(x):
    term = total = Q(1)
    for index in range(1, 31):
        term *= x / index
        total += term
    return total


def atan_partial(x, terms):
    return sum((-1) ** index * x ** (2 * index + 1) / (2 * index + 1)
               for index in range(terms))


def check_uniform_cutoff():
    sqrt_cutoff = 10 ** 10
    assert exp_lower(Q(6, 5)) > 3
    assert exp_lower(Q(7, 3)) > 10
    # exp(1)<3 from its series gives exp(2)<9<10.
    log_size_upper = 20 * Q(7, 3)
    log_factor = 30 * log_size_upper + 20
    assert Q(sqrt_cutoff, 200) > log_factor
    assert 400_000 * (3 + Q(6, 5) + log_size_upper / 4) * log_factor < sqrt_cutoff
    assert Q(1, 2) - 2 * Q(1, 40) > 0


def check_contours(pi_lo, pi_hi):
    sqrt_size = 1000
    size = sqrt_size ** 2
    min_k = 3
    assert 2 + (100 + pi_lo ** 2) / (2 * pi_lo ** 2) < 8
    assert (100 + pi_hi ** 2) * (1 + Q(1, 50 * min_k)) ** 2 < 12 ** 2
    assert 8 / (1 - Q(1, 50)) < 10
    assert Q(5, 8) + Q(1, 20) < 1
    assert Q(5, 100) + Q(1, 40 * min_k) < Q(3, 50) < Q(1, 14)
    assert 1 / (exp_lower(Q(10, 16)) - 1) < 2
    assert 100 * pi_lo ** 2 / (16 * (100 + pi_lo ** 2)) > Q(1, 2)
    assert 2 + 3 * pi_hi / 4 < 5
    assert 5 / (1 - Q(1, 50)) < 6

    assert pi_hi ** 2 < 10
    assert (100 + Q(10, min_k)) * (Q(1, 25) + Q(1, 2500 * min_k)) < 5
    assert pi_lo * size > 100
    assert (8 * pi_lo ** 2 - 5) * size * sqrt_size > 4 * pi_hi
    assert pi_lo * sqrt_size > 100 * 20
    # Vertical distance case: sin(y)>=2y/pi for y<=pi/2 and exp(-1/4)>=3/4.
    assert 3 * Q(3, 4) ** 2 / pi_hi ** 2 > Q(1, 4) ** 2
    # The contour estimate is 2*pi*exp(-8)*n^(-15/2), simplified below.
    assert 2 * pi_hi < size ** 5


def check_residues_and_phase(pi_lo, pi_hi):
    sqrt_size = 1000
    size = sqrt_size ** 2
    min_k = 3
    phase_margin = Q(12, 25)
    assert Q(1, 20) + Q(1, 50) == Q(7, 100)
    exp_ratio_upper = 1 / (1 - Q(7, 100))
    assert Q(37, 10) ** 2 < 14
    assert 26 * pi_lo > 9 ** 2
    assert pi_hi * exp_ratio_upper * (Q(1, 37) + Q(1, 9)) < phase_margin
    assert 100 * min_k > 17 ** 2
    assert 100 > 4 * 13
    assert pi_hi * exp_ratio_upper / (exp_lower(Q(17, 8)) - 1) < phase_margin

    assert Q(1, 25) + Q(1, 2500 * min_k) < Q(1, 20)
    assert 1 / (2 * (1 + Q(1, 20 * min_k))) > Q(49, 100)
    assert Q(49, 100) * 8 - phase_margin * 4 == 2
    assert Q(49, 100) - phase_margin / 4 == Q(37, 100)
    exponent = Q(37, 100)
    assert 2 * exponent * 25 > 1  # p exp(-exponent*(p^2-1)) decreases for p>=5.
    weighted_tail = 3 / exp_lower(Q(2)) + (5 + 1 / (4 * exponent)) / exp_lower(24 * exponent)
    assert weighted_tail < Q(21, 50)
    assert Q(21, 50) + 2 / Q(size * sqrt_size) < Q(1, 2)

    angle_upper_coefficient = Q(9, 25) * pi_hi
    angle_lower_coefficient = Q(17, 50) * pi_lo
    assert Q(7, 20) - Q(1, 6 * sqrt_size) > Q(17, 50)
    assert Q(7, 20) + Q(1, sqrt_size) < Q(9, 25)
    assert angle_upper_coefficient / sqrt_size < Q(1, 100)
    assert angle_lower_coefficient * (1 - angle_upper_coefficient ** 2 / (6 * size)) > 1
    assert 1 - angle_upper_coefficient ** 2 / (2 * size) > Q(18, 25)
    assert 200 * 20 > 25
    assert Q(1, 3) - 1 / (36 * (8 + Q(5, 6))) > Q(33, 100)
    assert Q(33, 100) / Q(9, 25) ** 2 > Q(5, 2)
    assert exp_lower(Q(5, 2)) > Q(9, 8) * Q(51, 5)
    assert phase_margin + Q(1, 100) < pi_lo / 6


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run this checker with assertions enabled (omit -O).")
    lower, upper = Q(333, 106), Q(22, 7)
    x, y = Q(1, 5), Q(1, 239)
    # Machin's identity with alternating-series bounds.
    assert lower < 16 * atan_partial(x, 4) - 4 * atan_partial(y, 3)
    assert 16 * atan_partial(x, 3) - 4 * atan_partial(y, 2) < upper
    check_uniform_cutoff()
    check_contours(lower, upper)
    check_residues_and_phase(lower, upper)
    print("All uniform-cutoff scalar bounds passed.")
