"""Rational enclosures for the inequalities in radial-taylor.md (standard library)."""
from fractions import Fraction as F


def exp_bounds(x, terms=96):
    """Positive Taylor sum and geometric upper bound for the remaining series."""
    x = F(x)
    if x < 0 or x >= terms + 2:
        raise ValueError("argument outside enclosure")
    term = total = F(1)
    for degree in range(1, terms + 1):
        term *= x / degree
        total += term
    tail = term * x / (terms + 1) / (1 - x / (terms + 2))
    return total, total + tail


def verify():
    pi_hi, pi_lo = F(22, 7), F(314, 100)
    e_lo, e_hi = exp_bounds(1)
    k = 400
    # Paired pole mass, contracted radius, and the low-s Taylor error.
    assert pi_hi**2 / 2 < F(9, 4)**2 and 3 < F(9, 4)**2
    u = F(129, 100)
    assert 16 + pi_hi**2/k < (u * pi_lo)**2
    assert 1/(e_lo*(1 - F(1, 2*k))) < F(38, 100)
    assert F(12, k) + (e_hi + 1)*(2 + F(9, 2)*u) + F(76, 100)*(2 + F(9, 4)*u) < 34
    # High-s Poisson bounds for the difference between the two radii.
    ratio = F(1001, 1000)
    assert 1 + pi_hi**2/(16*k) < ratio**2
    assert pi_hi**2/32 < F(31, 100)
    assert ratio + F(31, 100) < F(132, 100)
    assert 2*ratio*F(5, 4)*exp_bounds(F(33, 20))[1] < F(27, 2)
    assert ratio*F(5, 4)*exp_bounds(F(31, 80))[1] < 2
    assert F(1, 50) - F(132, 100*k) > F(1, 60)
    assert 120*ratio/k < F(31, 100)
    assert exp_bounds(F(2, 3))[1] < 2
    # 1+log k <= k; k exp(-k/6) decreases for k >= 400.
    assert exp_bounds(F(k, 6), terms=170)[0] > 10*k
    assert 2*ratio/F(69, 100) < 3
    assert F(27, 2) + 2 + 2*F(31, 100) + 2*(3 + F(1, 10)) < 34
    assert 1 + exp_bounds(pi_hi)[1] < 25
    # Separation of contour from neighboring poles, Cauchy error, phase.
    assert 8*pi_lo**2 / (2*(1 + F(1, k) + 1/pi_lo**2)) > 2
    assert F(9, 10) - F(9, 10)**2/(2*k) > F(89, 100)
    assert pi_hi**2 < 10 and exp_bounds(13)[0] > 130000
    assert (16*k+pi_hi**2)*(F(2, k)+F(1, k**2)) < 33 < 8*pi_lo**2
    assert 1 + pi_hi**2/32 < F(132, 100)
    assert 50**2 < 2*pi_lo*(k-1)
    assert pi_hi*exp_bounds(F(132, 100))[1]*(F(1, 80) + F(1, 50)) < F(12, 25)
    limit = F(6, 1000)
    assert (1 + F(1, k))**2 - 1 < limit
    assert 1 - limit/2 > F(98, 100)
    assert F(21, 50) + F(2, 100) < F(1, 2)
    # Uniform crossover for all k; the derivatives are with respect to log(n).
    height = 250000**2
    assert exp_bounds(F(25, 2))[0] > 250000
    assert F(89*250000, 100*2000) > 47 + F(5, 2)*25
    assert F(89*250000, 2*100*2000) > F(5, 2)
    assert F(height, 200*400) > 30*25 + 20
    print("Taylor, Poisson, pole-separation and phase bounds passed.")
    print(f"Combined sufficient height for all minimum cycle lengths: {height:,}.")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O so every bound is checked.")
    verify()
