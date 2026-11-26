"""Exact regression checks for the geometric-circle sign and disk criteria.

Run with python3 -IB verify.py. To test another rational coefficient vector,
pass --sign K A0 A1 ... AD. Coefficients are in ascending order and may
be integers or fractions such as 3/5.
"""

from argparse import REMAINDER, ArgumentParser
from fractions import Fraction
from math import factorial, gcd


Q = Fraction


def sign(value):
    return (value > 0) - (value < 0)


def horner(coefficients, x):
    total = Q(0)
    for coefficient in reversed(coefficients):
        total = x * total + coefficient
    return total


def geometric_sign(coefficients, k):
    """Return the sign at minus the geometric radius, without approximations."""
    a = tuple(map(Q, coefficients))
    if not 0 < k < len(a) - 1 or a[-1] == 0:
        raise ValueError("k must be internal to the given polynomial degree")
    if not a[k + 1] or a[k - 1] / a[k + 1] <= 0:
        raise ValueError("the squared geometric radius must be positive")
    radius_squared = a[k - 1] / a[k + 1]
    even = horner(a[::2], radius_squared)
    odd = horner(a[1::2], radius_squared)
    # P(-sqrt(radius_squared)) = even - sqrt(radius_squared)*odd.
    if not even:
        return -sign(odd)
    if not odd or sign(even) != sign(odd):
        return sign(even)
    return sign(even) * sign(even * even - radius_squared * odd * odd)


def quotient(a, k):
    return Q(a[k])**2 / (Q(a[k - 1]) * Q(a[k + 1]))


def tests_sign():
    assert geometric_sign((1, 1, 1), 1) == 1
    assert geometric_sign((1, 3, 1), 1) == -1
    assert geometric_sign((1, 2, 1), 1) == 0
    # The squared radius is 1/2, so neither of these tests uses a rational radius.
    assert geometric_sign((1, 2, 2), 1) == 1
    assert geometric_sign((1, 3, 2), 1) == -1
    # (q^2-2)(q^2+q+1) gives even=odd=0 at squared radius 2.
    assert geometric_sign((-2, -2, -1, 1, 1), 1) == 0
    assert geometric_sign((-1, -3, -2), 1) == 1
    assert geometric_sign((-1, 2, -2), 1) == -1


def tests_thresholds():
    # Let B^3=16. At j=1, square 2*B^(-3/2).
    j_one_squared = Q(4, 16)
    assert j_one_squared == Q(1, 4)
    # At j=2, square (3/2)*B^(-5/2) and use B>5/2.
    assert Q(5, 2)**3 < 16
    j_two_squared_bound = Q(9, 4) / Q(5, 2)**5
    assert j_two_squared_bound < Q(1, 4)
    # For j >= 2, both (j+1)/j and B^(-j-1/2) are decreasing.
    # The optional earlier tail estimate majorizes the j=4,6,... sum.
    first = 16 * Q(2, 5)**3 * Q(2, 3)
    ratio = Q(9, 4) * Q(2, 5)**10
    assert ratio < Q(1, 4) and first / (1 - ratio) < 1
    # The radius-one-half finite geometric sums have a nonnegative numerator
    # bound equal to zero at m=1 and already positive at m=2.
    assert Q(3, 4) - 3 * Q(1, 2)**2 == 0
    assert Q(3, 4) - 3 * Q(1, 2)**3 > 0


def tests_one_root_error_constants():
    # The sharp count threshold is 9/4. On the right interval the first
    # two terms have positive derivative and dominate the remaining terms.
    s = Q(2, 3)
    assert s**-2 == Q(9, 4) and s**3 == Q(8, 27)
    assert (4 * s**3)**2 < 2
    assert Q(8, 9) < (1 - Q(2, 35))**2
    right_tail = 2 * s**9 / (1 - s**7)
    assert right_tail == Q(1024, 18531) < Q(2, 35)

    # The cubic multiplier on the left is (8*y^4-6*y^2+3)/(4*y).
    # Its numerator and the derivative in y^2 are minimized at y^2=1/2.
    left_endpoint_squared = Q(1, 2)
    assert 8 * left_endpoint_squared**2 - 6 * left_endpoint_squared + 3 == 2
    assert 16 * left_endpoint_squared - 6 > 0
    assert Q(2, 4) == Q(1, 2)
    # For j=4,5,... the multiplier ratio is bounded by its j=4 value,
    # and the exponent increment 2*j+1 is at least nine.
    ratio = (1 + Q(25, 4)) / (1 + Q(16, 4)) * s**9
    assert ratio == Q(29, 20) * s**9 < Q(1, 8)
    left_tail = 5 * s**7 / (1 - Q(1, 8))
    assert left_tail == Q(5120, 15309) < Q(1, 2)


def tests_quartic():
    for root_b in (Q(3, 2), Q(8, 5)):
        b = root_b**2
        a = (1/b**2, 1/root_b, Q(1), 1/root_b, 1/b**2)
        assert all(quotient(a, k) == b for k in (1, 2, 3))
        assert a[1] / a[3] == 1

        def projection(x):
            return 1 + 2*x/root_b + 2*(2*x*x - 1)/b**2

        vertex = -(root_b**3)/4
        derivative_at_minus_one = 2/root_b - 8/b**2
        if root_b == Q(3, 2):
            assert root_b**3 < 4
            assert -1 < vertex < 1 and derivative_at_minus_one < 0
            assert projection(vertex) < projection(-1)
        else:
            assert root_b**3 > 4
            assert vertex < -1 and derivative_at_minus_one > 0
            # A positive derivative at -1 and positive second derivative
            # give the strict minimum at -1 on [-1,1].
            assert 8/b**2 > 0

    # Below the threshold, even a positive sign at -1 can coexist with
    # a negative angular projection. This reciprocal quartic has four
    # unit-circle roots by continuity at the two distinct cosine values.
    root_b = Q(7, 5)
    b = root_b**2
    a = (1/b**2, 1/root_b, Q(1), 1/root_b, 1/b**2)
    vertex = -root_b**3/4
    assert -1 < vertex < 1 and geometric_sign(a, 2) == 1
    assert 1 + 2*vertex/root_b + 2*(2*vertex**2-1)/b**2 < 0
    assert 1 + 2/root_b + 2/b**2 > 0


def integer_disk_count(coefficients, radius):
    """Strict Schur recursion. Return None if the recursion encounters a tie."""
    radius = Q(radius)
    a = tuple(coefficients)
    degree = len(a) - 1
    p = [c * radius.numerator**j * radius.denominator**(degree-j)
         for j, c in enumerate(a)]
    count = 0
    while len(p) > 1:
        low, high = p[0], p[-1]
        if abs(low) == abs(high):
            return None
        if abs(low) < abs(high):
            # high*P-low*P* counts the same roots and has a forced zero.
            p = [high*x-low*y for x,y in zip(p[1:], p[-2::-1])]
            count += 1
        else:
            # low*P-high*P* counts the same roots and cancels the top degree.
            p = [low*x-high*y for x,y in zip(p[:-1], p[:0:-1])]
        divisor = gcd(*p)
        p = [c//divisor for c in p]
    assert p[0]
    return count


def tests_disk():
    # (1+21q)(3+5q+3q^2) has a nonreal conjugate pair, since 25<36.
    # The geometric radius at k=1 is 1/6, exactly.
    a = (3, 68, 108, 63)
    assert a == (3, 3*21+5, 5*21+3, 3*21)
    assert 5**2-4*3*3 < 0
    assert all(quotient(a, k)**3 > 16 for k in (1, 2))
    assert Q(a[0], a[2]) == Q(1, 36)
    assert geometric_sign(a, 1) == -1
    assert integer_disk_count(a, Q(1, 6)) == 1
    assert integer_disk_count(a, Q(2)) == 3

    # The local factor-four equality at degree >=3 also gives a strict disk count.
    # At degree two, (1+q)^2 has its double root on the circle.
    equal = (4, 8, 4, 1)
    assert quotient(equal, 1) == 4 and quotient(equal, 2) > 1
    assert geometric_sign(equal, 1) == -1
    assert integer_disk_count(equal, Q(1)) == 1
    assert integer_disk_count((1, 2, 1), Q(1)) is None


def tests_sharp_count_threshold():
    check_radii = (Q(1023, 1024), Q(1025, 1024))
    fourth_power = (1, 4, 6, 4, 1)
    assert min(quotient(fourth_power, k) for k in (1, 2, 3)) == Q(9, 4)
    assert fourth_power[1] == fourth_power[3]
    assert geometric_sign(fourth_power, 2) == 0
    # (1+q)^4 has four roots at -1, including multiplicity.
    assert [integer_disk_count(fourth_power, t) for t in check_radii] == [0, 4]

    # Product of two distinct quadratics 1+A*q+q^2 and 1+B*q+q^2.
    # Negative discriminants and product of roots one give two unit roots
    # per factor. Distinct A,B and nonzero roots exclude any shared root.
    a, b = Q(19999, 10000), Q(9999, 5000)
    assert a != b and 0 < a < 2 and 0 < b < 2
    quartic = (Q(1), a+b, a*b+2, a+b, Q(1))
    assert min(quotient(quartic, k) for k in (1, 2, 3)) > Q(2249, 1000)
    assert quotient(quartic, 2) < Q(9, 4)
    assert quartic[1] == quartic[3]
    assert horner(quartic, -1) == (2-a)*(2-b) > 0
    assert geometric_sign(quartic, 2) == 1
    # Product denominators divide this common positive scalar.
    scaled = tuple(int(coefficient*10**8) for coefficient in quartic)
    assert tuple(Q(coefficient, 10**8) for coefficient in scaled) == quartic
    assert [integer_disk_count(scaled, t) for t in check_radii] == [0, 4]


def tests_neighboring_counts():
    # Both quotients exceed 9/4 and the normalized sign is negative. At
    # k=1, Im F(e^{i*theta}) has the sign of sin(2*theta); the real
    # projection is positive at pi/2 and negative at pi. Thus the upper
    # crossing is below the axis. Reversal gives the opposite crossing.
    lower = (15, 25, 15, 3)
    higher = lower[::-1]
    assert all(quotient(lower, k) > Q(9, 4) for k in (1, 2))
    assert lower[0] == lower[2] and higher[1] == higher[3]
    assert Q(1) - Q(3, 25) > 0
    assert geometric_sign(lower, 1) == 1
    assert geometric_sign(higher, 2) == -1
    assert integer_disk_count(lower, Q(1)) == 0  # k-1
    assert integer_disk_count(higher, Q(1)) == 3  # k+1

    # The zero-imaginary-part crossing is a simple conjugate boundary pair.
    pair = (3, 5, 3)
    assert quotient(pair, 1) == Q(25, 9) > Q(9, 4)
    assert geometric_sign(pair, 1) == 1
    assert 5**2 - 4*3*3 < 0 and pair[0] == pair[-1]
    assert [integer_disk_count(pair, t) for t in (Q(7, 8), Q(9, 8))] == [0, 2]


def lower_curvature(n, d, r, k):
    assert 1 <= k < n*r//d
    e = n*r-d*k
    m = e+d
    bulk = n-m
    assert bulk > 0 and bulk*min(r, d-r) >= 2*m*d
    return Q(2*d*d*(n-1), (n+m-1)*(2*e+d)) - Q(24*d*m, bulk)


def tests_balanced_application():
    n, d, r = 10**8, 100, 50
    degree = n*r//d
    first = degree-64
    assert first == 49999936
    bounds = [lower_curvature(n, d, r, k) for k in range(first, degree)]
    assert bounds[0] == Q(1199077934275800, 859999987767059)
    assert all(left < right for left, right in zip(bounds, bounds[1:]))
    threshold = Q(139, 100)
    assert lower_curvature(n, d, r, first-1) <= threshold < min(bounds)
    # e^(139/200)>2 implies exp(139/100)>4 exactly.
    assert sum((Q(139, 200)**j / factorial(j) for j in range(6)), Q(0)) > 2
    assert len(bounds) == 64


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--sign", metavar="VALUE", nargs=REMAINDER)
    args = parser.parse_args()
    if args.sign is not None:
        if len(args.sign) < 4:
            parser.error("--sign requires K and at least three coefficients")
        k, *coefficients = args.sign
        print(geometric_sign(coefficients, int(k)))
        return
    tests_sign()
    tests_thresholds()
    tests_one_root_error_constants()
    tests_quartic()
    tests_disk()
    tests_sharp_count_threshold()
    tests_neighboring_counts()
    tests_balanced_application()
    print("Exact signs, both sharp thresholds, Schur counts, and 64 curvature bounds passed.")


if __name__ == "__main__":
    main()
