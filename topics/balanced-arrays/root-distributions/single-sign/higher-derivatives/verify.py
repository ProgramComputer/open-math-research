"""Exact checks for the all-order geometric-circle theorem.

Run with python3 -IB verify.py. This replay uses only integer and rational
arithmetic. The final lines report sufficient bounds, not exact disk counts.

Lower witness for the Jensen bound. At k=m, (1+z)^(2m) has radius one,
open count zero and closed count 2m. The minimum second quotient is
Q=(1+1/m)^2 because i(2m-i) is largest at i=m. Applying
x/(1+x) <= log(1+x) <= x at x=1/m gives
2m/(m+1) <= m*log(Q) <= 2, so m*log(Q) tends to two.
"""

from fractions import Fraction as Q
from functools import lru_cache
from math import comb, factorial


def chebyshev_polynomials(degree):
    """Return T_0 through T_degree as ascending integer coefficient tuples."""
    polynomials = [(1,)]
    if degree:
        polynomials.append((0, 1))
    for n in range(1, degree):
        candidate = [0] + [2 * value for value in polynomials[n]]
        for j, value in enumerate(polynomials[n - 1]):
            candidate[j] -= value
        polynomials.append(tuple(candidate))
    return polynomials


def taylor_at(poly, j, point):
    """Coefficient of y^j in poly(point+y), or zero beyond the degree."""
    return sum(poly[i] * comb(i, j) * point**(i-j)
               for i in range(j, len(poly)))


def verify_chebyshev_ratios():
    polynomials = chebyshev_polynomials(32)
    comparisons = 0
    for j in range(1, 17):
        for ell in range(16):
            n = j + ell
            denominator = taylor_at(polynomials[n], j, 1)
            numerator = taylor_at(polynomials[n + 1], j, 1)
            # The factor j! in both derivatives cancels in their ratio.
            assert denominator > 0
            expected = 2**(j-1) * factorial(j-1) * n * comb(2*j+ell-1, ell)
            assert denominator * factorial(j) == expected
            assert Q(numerator, denominator) == Q(n + 1, n) * Q(2*j + ell, ell + 1)
            assert taylor_at(polynomials[n], j, -1) == (-1)**ell * denominator
            comparisons += 1
    return comparisons


def bracket_root(m):
    """Strict dyadic bracket for (2m+2)^(1/(2m+1))."""
    denominator = 1024
    lo, hi = denominator, 2 * denominator
    power = 2*m + 1
    target = 2 * (m + 1) * denominator**power
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if mid**power < target:
            lo = mid
        else:
            hi = mid
    assert lo**power < target < hi**power
    return Q(lo, denominator), Q(hi, denominator)


def real_projection(coefficients, k, chebyshev):
    """Real part on |z|=1 after division by a_k*z^k, in x=Re(z)."""
    assert coefficients[k-1] == coefficients[k+1]
    max_distance = max(k, len(coefficients)-1-k)
    projection = [Q(0)] * (max_distance + 1)
    for i, coefficient in enumerate(coefficients):
        for power, value in enumerate(chebyshev[abs(i-k)]):
            projection[power] += coefficient / coefficients[k] * value
    return projection


def verify_quotients(coefficients, target):
    assert all(coefficients[j]**2 >= target * coefficients[j-1] * coefficients[j+1]
               for j in range(1, len(coefficients)-1))


def verify_sharp_examples():
    chebyshev = chebyshev_polynomials(18)
    for m in range(1, 9):
        below, above = bracket_root(m)
        k = m + 1
        for square_root in (below, above):
            q = square_root**2
            a = [square_root**(-(i-k)**2) for i in range(2*k+1)]
            assert all(a[i]**2 == q * a[i-1] * a[i+1] for i in range(1, 2*k))
            projection = real_projection(a, k, chebyshev)
            first = taylor_at(projection, m, -1)
            # This is A^(m)(-1)/m!. Its sign changes at the threshold.
            if square_root == below:
                assert first < 0
            else:
                assert first > 0 and taylor_at(projection, m+1, -1) > 0

        # An asymmetric longer example checks the nonnegative Taylor
        # coefficients for every j >= m, with unequal lengths of the tails.
        k = m + 3
        degree = 2*m + 8
        a = []
        for i in range(degree + 1):
            offset = i - k
            extra = Q(2, 3)**(offset*(offset-1)//2) if offset > 0 else Q(1)
            a.append(extra * above**(-offset**2))
        verify_quotients(a, above**2)
        projection = real_projection(a, k, chebyshev)
        assert taylor_at(projection, m, -1) > 0
        for j in range(m, len(projection)):
            assert taylor_at(projection, j, -1) >= 0

    # The relevant Q_j decrease. Test their exact cross-power comparisons
    # alongside the polynomial expansion checks above.
    for j in range(1, 32):
        assert (2*(j+2))**(2*j+1) < (2*(j+1))**(2*j+3)


def verify_boundary_example():
    # At k=2, (1+z)^4 has geometric radius one, all four roots at -1,
    # and hence open/closed counts zero and four. This attains both m=2
    # errors relative to k; the stronger threshold for m=1 does not apply.
    a = tuple(Q(comb(4, i)) for i in range(5))
    minimum = min(a[k]**2 / (a[k-1]*a[k+1]) for k in (1, 2, 3))
    assert minimum**5 > (2*3)**2 and minimum**3 < (2*2)**2
    projection = real_projection(a, 2, chebyshev_polynomials(2))
    assert projection == [Q(2, 3), Q(4, 3), Q(2, 3)]
    assert taylor_at(projection, 2, -1) == Q(2, 3)


@lru_cache(maxsize=None)
def log_on_unit_interval(x, terms):
    """Rational enclosure of log(x) for 1 <= x <= 2."""
    assert 1 <= x <= 2
    u = (x-1)/(x+1)
    power = u
    lower = Q(0)
    for j in range(terms):
        lower += 2*power/(2*j+1)
        power *= u*u
    error = 2*power / ((2*terms+1)*(1-u*u))
    return lower, lower + error


def log_integer(value, terms):
    shift = value.bit_length() - 1
    y = Q(value, 2**shift)
    low, high = log_on_unit_interval(y, terms)
    low_two, high_two = log_on_unit_interval(Q(2), terms)
    return low + shift*low_two, high + shift*high_two


def sufficient(n, d, m):
    left = Q(2*d*(2*m+1), n+2)
    for terms in (12, 24, 48):
        low, high = log_integer(2*m+2, terms)
        if left >= high:
            return True
        if left < low:
            return False
    raise ArithmeticError(f"log enclosure did not decide m={m}")


def minimal_order(n, d):
    m = 1
    while not sufficient(n, d, m):
        m += 1
    return m


def arctan_bounds(x, pairs=8):
    # Alternating Taylor sums of even/odd ending index enclose arctan(x).
    lower = sum(((-1)**j*x**(2*j+1)/(2*j+1) for j in range(2*pairs)), Q(0))
    return lower, lower + x**(4*pairs+1)/(4*pairs+1)


def verify_jensen_bound():
    # Machin's formula pi = 16 arctan(1/5) - 4 arctan(1/239).
    a_low, a_high = arctan_bounds(Q(1, 5))
    b_low, b_high = arctan_bounds(Q(1, 239))
    pi_low, pi_high = 16*a_low - 4*b_high, 16*a_high - 4*b_low
    assert Q(31415, 10000) < pi_low < pi_high < Q(3142, 1000)

    e_low = sum((Q(1, factorial(j)) for j in range(8)), Q(0))
    e_high = e_low + Q(1, factorial(8)) / (1 - Q(1, 9))
    assert Q(2718, 1000) < e_low < e_high < Q(2719, 1000)

    n, d = 10**6, 1000
    low = Q(2718, 1000) * Q(31415, 10000)**2 * Q(n+2, 32*d)
    high = Q(2719, 1000) * Q(3142, 1000)**2 * Q(n+2, 32*d)
    assert 838 < low < high < 839

    # Replay the exact curvature of the binomial lower witnesses.
    for m in range(1, 17):
        a = [comb(2*m, i) for i in range(2*m+1)]
        curvature = min(Q(a[i]**2, a[i-1]*a[i+1]) for i in range(1, 2*m))
        assert curvature == Q(m+1, m)**2
    return high.numerator // high.denominator


def main():
    comparisons = verify_chebyshev_ratios()
    verify_sharp_examples()
    verify_boundary_example()
    print(f"{comparisons} Chebyshev derivative ratios and sharp examples at m=1..8 passed")
    n = 10**6
    for d in (100000, 125000, 1000):
        m = minimal_order(n, d)
        assert sufficient(n, d, m)
        assert m == 1 or not sufficient(n, d, m-1)
        print(f"n={n}, d={d}: minimal sufficient m={m}; both disk counts within {m} of k")
    print(f"n={n}, d=1000: the Jensen test puts both disk counts within {verify_jensen_bound()} of k")


if __name__ == "__main__":
    main()
