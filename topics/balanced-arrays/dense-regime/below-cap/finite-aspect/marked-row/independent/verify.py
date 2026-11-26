"""Portable exact replay of the checked million-row sign extension.

Run with python3 -IB verify.py and keep tilt-witnesses.csv beside it.
All quantities are integers. The tilt numerators are untrusted witnesses;
each is tested against the target truncated mean.
"""

import csv
from pathlib import Path

N, D, R = 10**6, 250000, 127000
Z = 1 << 44
E = 1 << 56
B = 1 << 48


def ceil_div(numerator, denominator):
    return (numerator + denominator - 1) // denominator


def cap_atom(tilt):
    if not 0 < tilt < Z:
        raise ValueError("tilt must lie strictly between zero and one")
    # Binomial weights relative to the cap atom, in units of 1/B.
    lower = upper = lower_sum = upper_sum = B
    fraction = Z - tilt
    for j in range(R, 0, -1):
        num = j * fraction
        den = (D-j+1) * tilt
        if upper <= 1 << 16 and num < den:
            upper_sum += ceil_div(upper*num, den-num)
            break
        lower = lower*num//den
        upper = ceil_div(upper*num, den)
        lower_sum += lower
        upper_sum += upper
    return E*B//upper_sum, ceil_div(E*B, lower_sum)


def lower_loss(k):
    loss = 0
    for level in range(4, -1, -1):
        n, quota = N-level, k-level
        tilt = quota*E*Z//(n*E-(n-quota)*loss)
        atom, _ = cap_atom(tilt)
        loss = atom*(D-R)*n//(D*(n-quota))
    return loss


def upper_loss(k, tilt):
    _, atom = cap_atom(tilt)
    assert D*(tilt*N-k*Z)*E >= tilt*(D-R)*atom*N, (k, tilt)
    return ceil_div(atom*(D-R)*N, D*(N-k))


def interval_ratio(num, den):
    return num*B//den, ceil_div(num*B, den)


def product(first, second):
    return first[0]*second[0]//B, ceil_div(first[1]*second[1], B)


def power(base, exponent):
    value = B, B
    while exponent:
        if exponent % 2:
            value = product(value, base)
        exponent //= 2
        if exponent:
            base = product(base, base)
    return value


def binomial_term_base(k, j):
    value = B, B
    for i in range(1, j+1):
        value = product(value, interval_ratio(
            (N-k-i+1)**2*k*(k+1), (k+i)**2*(N-k)*(N-k+1)))
    return value


def signed_margin(k, low, high):
    first = power(binomial_term_base(k, 1), D//2)[1]
    even = power(product(binomial_term_base(k, 2),
                         binomial_term_base(N-k, 2)), D//4)
    penalty = power(interval_ratio(E-high, E-low), D//2)
    third = power(binomial_term_base(k, 3), D//2)[1]
    third_reflected = power(binomial_term_base(N-k, 3), D//2)[1]
    return B - 2*first + 2*product(even, penalty)[0] - third - third_reflected


def verify():
    expected = 504159
    standard_end = 505610
    signed_end = 505661
    standard_blocks = signed_count = 0
    standard_min = E
    signed_min = B
    path = Path(__file__).with_name("tilt-witnesses.csv")
    with path.open(newline="") as stream:
        reader = csv.DictReader(stream)
        assert reader.fieldnames == ["first", "last", "upper_z"]
        for row in reader:
            first, last, tilt = (int(row[key]) for key in reader.fieldnames)
            assert first == expected <= last <= signed_end
            low = lower_loss(first-2)
            high = upper_loss(last+2, tilt)
            assert 0 <= low <= high < E
            if first <= standard_end:
                assert last <= standard_end
                margin = E-(4*D+1)*high+4*D*low
                assert margin > 0, (first, last, margin)
                standard_blocks += 1
                standard_min = min(standard_min, margin)
            else:
                assert first == last
                margin = signed_margin(first, low, high)
                assert margin > 0, (first, margin)
                signed_count += 1
                signed_min = min(signed_min, margin)
            expected = last+1
    assert expected == signed_end+1
    assert standard_blocks == 229 and signed_count == 51
    print(f"229 standard blocks cover 504159..505610; minimum margin {standard_min}/{E}")
    print(f"51 exact signed points cover 505611..505661; minimum margin {signed_min}/{B}")


if __name__ == "__main__":
    verify()
