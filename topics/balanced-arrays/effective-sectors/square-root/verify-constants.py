"""Replay the rational estimates of the square-root dimension proof."""
from fractions import Fraction as Q
from math import factorial


def exp_lower(x, degree):
    return sum(x**k / factorial(k) for k in range(degree + 1))


def check():
    min_d = 16384
    min_N = Q(2, 5) * min_d
    assert Q(min_d, min_d + 1) > Q(19, 20)
    assert exp_lower(Q(19, 20), 3) > Q(5, 2)
    ratio = Q(2, 5)
    assert 1 + 3 / (1 - ratio) + 2 * ratio / (1 - ratio)**2 == Q(74, 9)
    assert Q(74, 9) < 9
    assert 18 * (1 + Q(1, min_d)) < 19
    assert 5**2 > 19 and 5 + 2 * 19 == 43
    assert (1 + 43 / min_N) / (1 - Q(43, min_d)) < Q(6, 5)
    assert 19 * (Q(5, 2) + Q(6, 5)) < 72
    assert Q(72, min_d) < Q(1, 192) and Q(144, min_d) < Q(1, 100)
    # Near the midpoint, e < 3 follows from the factorial series.
    # n >= 64 implies (4n)^3 <= n^4 < (n+1)^4.
    assert 4**3 == 64
    assert Q(2) * (1 + Q(3, 8)) / (1 - Q(3, 8)) < 8
    assert exp_lower(Q(1), 4) > Q(8, 3)
    bernstein = Q(9, 100)**2 / (2 * (Q(1, 192) + Q(3, 100)))
    chernoff = (Q(9, 10) - Q(5, 8))**2 / (2 * Q(9, 10))
    assert bernstein > Q(1, 10)
    assert chernoff == Q(121, 2880) and chernoff > Q(1, 24)
    assert (Q(min_d, 24) - 8 * 72) * Q(2, 5) > 1
    assert Q(min_d) / (Q(2, 5) * min_d + 1) > Q(12, 5)
    assert exp_lower(Q(12, 5), 4) > 9
    assert Q(3, 20) * min_d - 2 > 1

    # Constants for the wider corank range (Theorem 4).
    def mode_fraction(upper):
        return (upper + Q(43, min_d)) / (1 - Q(43, min_d))

    def bernstein_rate(deficit, variance):
        return deficit**2 / (2 * (variance + deficit / 3))

    def row_rate(fraction, cap):
        return (fraction - cap)**2 / (2 * fraction)

    assert mode_fraction(Q(7, 10)) + Q(2, min_d) < Q(5, 7)
    assert mode_fraction(Q(9, 10)) + Q(2, min_d) < 1
    assert exp_lower(Q(7, 5), 6) > 4 and exp_lower(Q(1), 3) > Q(5, 2)
    bands = [
        (Q(5,8), Q(1,4), Q(20,9), Q(1,4000), Q(99,100), Q(19,2000), 100, 520),
        (Q(7,10), Q(2,5), Q(35,9), Q(1,2500), Q(99,100), Q(9,1000), 100, 100),
    ]
    for lower, ratio, variance, relative, fraction, deficit, A, B in bands:
        assert (1 + ratio) / (1 - ratio)**2 == variance
        assert variance / (lower * min_d) < relative
        assert 1 - 2 * relative - fraction >= deficit
        assert bernstein_rate(deficit, relative) > Q(1, A)
        assert row_rate(fraction, Q(29,50) / lower) > Q(1, B)
        assert Q(min_d, B) * lower > 8 * variance + 1 and A <= B
    assert row_rate(Q(9,10), Q(29,45)) > Q(1,28)
    assert (Q(min_d,28) - 576) * Q(9,10) > 1
    assert (Q(5,8) - Q(29,50)) * min_d - 2 > 1
    assert 1 / (Q(5,8) + Q(2,min_d)) > Q(159,100)
    assert exp_lower(Q(159,200), 4) > Q(1000,453)
    assert exp_lower(Q(159,100), 6) > Q(1000,205)
    tau, step = Q(453,1000), Q(205,1000)
    assert 1 - tau * step - 2 * tau == Q(227,200000)

    m = 10**6
    n, d, c = m**3, m**2, m // 4
    # e^44 > (8/3)^44 verifies an upper bound on the logarithm.
    assert Q(8, 3)**44 > n + 1
    assert d*d >= 16384 * n * 44 and d*d == 4*n*c
    assert n*(d-c)//d == 999999750000000000
    print("All rational comparisons passed. Example degree:", n*(d-c)//d)


if __name__ == "__main__":
    check()
