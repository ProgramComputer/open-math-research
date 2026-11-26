"""Rational bounds for the finite-aspect theorem and two million-row disks."""
from fractions import Fraction as Q
from math import factorial

SCALE = 2**128


def exp_lower(x, degree):
    return sum(x**j / factorial(j) for j in range(degree + 1))


def rounded_power(value, power):
    """Enclose a positive rational power by fixed-denominator integers."""
    def ceil_div(a, b):
        return (a + b - 1) // b

    def mul(a, b):
        return a[0] * b[0] // SCALE, ceil_div(a[1] * b[1], SCALE)

    x = value * SCALE
    factor = x.numerator // x.denominator, ceil_div(x.numerator, x.denominator)
    result = (SCALE, SCALE)
    while power:
        if power % 2:
            result = mul(result, factor)
        power //= 2
        if power:
            factor = mul(factor, factor)
    return tuple(Q(v, SCALE) for v in result)


def local_terms(n, d, k, w):
    terms = {0: (Q(1), Q(1))}
    left = right = Q(1)
    for j in range(1, 4):
        left *= Q(k - j + 1, n - k + j) / w
        right *= Q(n - k - j + 1, k + j) * w
        terms[-j] = rounded_power(left, d)
        terms[j] = rounded_power(right, d)
    return terms


def certify_disk(n, d, r, k, w):
    terms = local_terms(n, d, k, w)
    lower = [terms[-j][0] + terms[j][0] for j in range(1, 4)]
    upper = [terms[-j][1] + terms[j][1] for j in range(1, 4)]
    # Cubic real projection increases in cos(theta).
    assert lower[0] > 4 * upper[1] + 3 * upper[2]
    min_seven = 1 - upper[0] + lower[1] - upper[2]
    tail = Q(0)
    for direction in (-1, 1):
        endpoint = terms[3 * direction][1]
        ratio = endpoint / terms[2 * direction][0]
        assert 0 < ratio < 1
        tail += endpoint * ratio / (1 - ratio)
    # Upper bound for the expected number of overflowing rows for |j| <= 3.
    gap = Q(r, d) - Q(k + 3, n)
    assert gap > 0 and 2 * d * gap**2 > 30
    assert exp_lower(Q(30), 43) > n * 10**6
    cap_loss = Q(1, 10**6) * (1 + sum(upper))
    assert min_seven - tail - cap_loss > Q(1, 100)
    print(f"Exactly {k} roots strictly inside ({w})^{d}; no boundary roots.")


def main():
    n, d, r = 10**6, 250000, 127000
    assert exp_lower(Q(6070**2, 2*n), 55) > 100*n
    assert n*r//d - 6070 - 4 == 501926
    assert Q(d, n//8+1) + Q(d,n+1) > Q(11,5)
    assert exp_lower(Q(11,5), 9) > 9
    assert exp_lower(Q(3,2), 6) > Q(40,9)
    assert exp_lower(Q(4), 6) > 30
    assert exp_lower(Q(1,2), 4) > 1/Q(607,1000)
    assert exp_lower(Q(2), 7) > 1/Q(136,1000)
    assert exp_lower(Q(9,2), 10) > 1/Q(12,1000)
    assert sum(Q(2)**j/factorial(j) for j in range(9)) + Q(2**9,factorial(9))*Q(5,4) < 1/Q(135,1000)
    assert 1 - 2*Q(607,1000) + 2*Q(135,1000) - 2*Q(12,1000) == Q(32,1000)
    assert 1 + 2*(Q(607,1000)+Q(136,1000)+Q(12,1000)) == Q(251,100)
    assert Q(32,1000)-Q(251,100)*Q(11,1000)-Q(3,1000) > Q(1,1000)
    assert exp_lower(Q(2498,1000), 5) > 1/Q(9,100)
    assert 2*Q(13,1000)*Q(9,100)/(1-Q(9,100)) < Q(3,1000)
    certify_disk(n, d, r, n//3, Q(1,2))
    certify_disk(n, d, r, n//2, Q(1))
    print("At least 501926 of 508000 roots are simple and negative.")


if __name__ == "__main__":
    main()
