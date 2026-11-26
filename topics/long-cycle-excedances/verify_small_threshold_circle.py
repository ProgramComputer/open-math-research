"""Run as documented without Python optimization."""
from fractions import Fraction as F
from verify_radial_taylor import exp_bounds


def verify():
    k = 11
    pi_high, pi_low = F(22, 7), F(314, 100)
    assert exp_bounds(14)[0] > 10**6 and 500 > 30*14 + 20
    assert exp_bounds(6)[0] > 400 and exp_bounds(F(1, 5))[1]*66 < 82
    assert F(3, 20) - F(3, 20)**2/(2*k) > F(148, 1000)
    assert F(148*10**6, 1000*400) > 164 + 10 + F(3, 2)*14
    assert exp_bounds(10)[0] > 18000
    assert (81*k + pi_high**2)*(F(2, 5*k) + F(1, 25*k*k)) < 34
    assert F(1, 5) + pi_high**2/162 < F(262, 1000)
    assert 9**2*21 > 41**2 and 40*pi_low > 11**2
    fac = pi_high*exp_bounds(F(262, 1000))[1]
    assert fac*(F(1, 41)+F(1, 11)) < F(12, 25)
    assert 9**2*11 > 29**2 and 81*20 > 4*(20-1)**2
    assert fac/(exp_bounds(F(29, 8))[0]-1) < F(12, 25)
    assert (1+F(1, 5*k))**2-1 < F(38, 1000)
    assert 1-F(38, 2000) > F(98, 100)
    assert 4*10**6 > 81*400
    print("Small thresholds 3 through 399: every scalar bound passed at n >= 1,000,000.")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O so every bound is checked.")
    verify()
