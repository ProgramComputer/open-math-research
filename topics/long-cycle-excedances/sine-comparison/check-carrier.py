"""Exact single-carrier determinant bounds over every bounded-aspect middle angle."""
from fractions import Fraction as F
from math import ceil, factorial, isqrt
from pathlib import Path
import runpy

prior = runpy.run_path(str(Path(__file__).with_name("check-bounds.py")))
paired = prior["paired"]
lattice = paired.prev
U = prior["U"]


def margin(lower, upper):
    K = 10000 // upper
    A = F(isqrt(192000) // upper, 4)
    assert K >= 208 and A >= F(9, 4) and A*A*upper*upper <= 12000
    c = (1-F(1, K))*U/(192*upper)
    weights, tail, _ = lattice.lattice(c)
    pole_sum = sum(F(w, abs(a-1)*paired.G) for a, w in zip(paired.poles, weights) if a != 1)
    eta = (pole_sum + F(tail, 2*paired.G))*K/((K-1)*A)
    assert eta < F(81, 100)
    carrier = F(12, 11)/paired.exp_upper(eta)

    q, _ = paired.coefficients(K, lower, upper, A, 240)
    linear = {i: paired.up(mass*lattice.stars((g-F(1, K))*U/(192*upper))[0]/A)
              for i, g, mass in lattice.degree_masses(K, 60)}
    c_exact = (lower-1-F(1, K))*U/(192*upper)
    atom = lattice.stars(c_exact)[0]*lattice.mass(U/(192*upper))/(2*factorial(lower-1)*A*A)
    principal = F(1, 10000)
    other = regular = F(0)
    for b, count in enumerate(q):
        qb = F(count, paired.G)
        h = F(b, 4)
        g = max(1, F(b, 5)) if b else F(0)
        principal += 2*paired.eps(lower-h)*qb
        c = max(F(1, upper), 1-h/lower)*U/192
        if b <= 5*upper and g+1 <= upper:
            weight = F(4, 7) if lower-h >= 2 else F(1)
            other += weight*lattice.first_nonprincipal(c)*qb
        if b < 5*upper and g+1 <= upper+F(1, K):
            regular += prior["regular_numerator"](max(1, lower-h))*lattice.mass(c)*qb/A
            if b > 4*(lower-1):
                multiple = qb-F(linear.get(b, 0), paired.G)
                assert multiple >= 0
                atom += A*upper/U*lattice.mass(c)*multiple
    return eta, carrier, principal, other, regular, atom


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run with assertions enabled")
    paired.global_bounds()
    assert paired.exp_upper(F(1)) < F(11, 4)
    assert F(8, 7)*paired.exp_upper(F(14))*F(9, 8)**(-240) < F(1, 10000)
    for lower, upper in prior["SLABS"]:
        eta, carrier, *costs = margin(lower, upper)
        bound = carrier - sum(costs)
        assert bound > F(322338, 10**6)
        print(lower, upper, ceil(10**6*eta), int(10**6*carrier),
              *(ceil(10**6*cost) for cost in costs), int(10**6*bound))
