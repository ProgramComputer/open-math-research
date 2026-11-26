"""Independent pair-of-columns enumeration for the remote row test symbols."""
from fractions import Fraction
from functools import cache
from math import comb, factorial, lcm

from flint import fmpq_poly, fmpz_poly


def choose(n, k):
    return comb(n, k) if 0 <= k <= n else 0


@cache
def count(n, k):
    total = 0
    for i in range(k + 1):
        first = choose(n, i) * choose(n-i, k-i) * choose(n-k, k-i)
        if not first:
            continue
        for j in range(k + 1):
            second = choose(n-2*k+i, j) * choose(n-i-j, k-j) * choose(n-i-k, k-j)
            total += first * second
    return total


def quota_polynomial(k):
    x = fmpq_poly([0, 1])
    values = [count(n, k) for n in range(4*k+1)]
    basis, polynomial = fmpq_poly([1]), fmpq_poly([])
    for j in range(4*k+1):
        polynomial += values[0] * basis
        basis = basis * (x-j) / (j+1)
        values = [b-a for a, b in zip(values, values[1:])]
    assert polynomial.degree() == 4*k
    assert all(polynomial(n) == count(n, k) for n in range(4*k+1, 8*k+1))
    return polynomial


def fourth(e):
    # Newton identities for the roots of the reversed monic symbol.
    c = [1] + [(-1)**k * value for k, value in enumerate(e, 1)]
    p = [0]
    for k in range(1, 5):
        p.append(-k*c[k] - sum(c[j]*p[k-j] for j in range(1, k)))
    return p[4]


def real_count(coefficients):
    ints = [int(c*lcm(*(x.denominator for x in coefficients))) for c in coefficients]
    poly = fmpz_poly(ints)
    poly = poly // poly.gcd(poly.derivative())
    a, b = fmpq_poly(poly), fmpq_poly(poly.derivative())
    minus, plus = [], []
    while a:
        sign = 1 if a.leading_coefficient() > 0 else -1
        plus.append(sign)
        minus.append((-1)**a.degree()*sign)
        if not b:
            break
        a, b = b, -(a % b)
        if b:
            b /= abs(b.leading_coefficient())
    changes = lambda signs: sum(x != y for x, y in zip(signs, signs[1:]))
    return changes(minus)-changes(plus), poly.degree()


def main():
    x = fmpq_poly([0, 1])
    quota = [quota_polynomial(k) for k in range(1, 5)]
    ns = [quota[k-1] for k in range(1, 5)]
    for k, term in enumerate(ns, 1):
        for j in range(k):
            term *= x-j
        ns[k-1] = term
    ds = [factorial(k)*quota[k-1](2*x) for k in range(1, 5)]
    a, b, c, d = ns
    A, B, C, D = ds
    # Compute the cleared Newton sum from separately cleared elementary monomials.
    numerator = (a**4*B**2*C*D - 4*a**2*b*A**2*B*C*D + 2*b**2*A**4*C*D
                 + 4*a*c*A**3*B**2*D - 4*d*A**4*B**2*C)
    assert numerator.degree() == 61 and all(z < 0 for z in numerator(x+33))
    for n in range(33):
        symbol = [Fraction(comb(n, k)*count(n, k), count(2*n, k))
                  for k in range(n//2+1)]
        roots, degree = real_count(symbol)
        assert degree == n // 2
        assert roots == degree - (0 if n <= 10 else 2 if n <= 23 else 4)
        if n >= 8:
            assert numerator(n) / (A**4*B**2*C*D)(n) == as_flint(fourth(symbol[1:5]))
        print(n, roots, degree)
    weighted = [quota[k-1]*factorial(k)**3 for k in range(1, 5)]
    assert fourth(weighted).degree() == 13
    assert all(c < 0 for c in fourth(weighted)(x+76))
    for n in range(76):
        symbol = [Fraction(factorial(k)**3*count(n, k)) for k in range(n//2+1)]
        roots, degree = real_count(symbol)
        assert (roots == degree) == (n <= 15), (n, roots, degree)
    print("verified: both infinite tails and the cubic-factorial prefix")


def as_flint(fraction):
    from flint import fmpq
    return fmpq(fraction.numerator, fraction.denominator)


if __name__ == "__main__":
    main()
