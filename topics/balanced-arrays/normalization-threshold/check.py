"""Exact small witnesses for alternative normalizations of genuine capped arrays."""
from fractions import Fraction
from itertools import product
from math import comb


def array_coefficients(n, d, cap):
    supports = [m for m in range(1 << d) if m.bit_count() <= cap]
    result = [0]*(n*cap//d+1)
    for rows in product(supports, repeat=n):
        quotas = [sum((m >> j) & 1 for m in rows) for j in range(d)]
        if len(set(quotas)) == 1:
            result[quotas[0]] += 1
    return result


def quadratic_discriminant(coefficients):
    a, b, c = coefficients
    return b*b-4*a*c


def main():
    a = array_coefficients(5, 2, 1)
    assert a == [1, 20, 30]
    native = [Fraction(v, comb(len(a)-1, k)) for k, v in enumerate(a)]
    assert quadratic_discriminant(native) == -20
    print("native once", a, [str(x) for x in native], "-20")

    a = array_coefficients(4, 2, 1)
    assert a == [1, 12, 6]
    twice = [Fraction(12*v, comb(4, k)**2) for k, v in enumerate(a)]
    assert quadratic_discriminant(twice) == -15
    print("source twice", a, [str(x) for x in twice], "-15")

    a = array_coefficients(5, 4, 2)
    assert a == [1, 540, 2490]
    validity = [Fraction(1000*v, comb(5, k)**4) for k, v in enumerate(a)]
    assert quadratic_discriminant(validity) == -249504
    print("validity probability", a, [str(x) for x in validity], "-249504")

    truncate = [comb(4, k) for k in range(3)]
    assert quadratic_discriminant(truncate) == -8
    print("degree-corrected recovery symbol", truncate, "-8")


if __name__ == "__main__":
    main()
