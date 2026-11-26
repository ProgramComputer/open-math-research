"""Exact uniform bounds for the mixed Eulerian pole terms of a two-cycle row."""
from fractions import Fraction as Q
from functools import cache

N = 192
C = Q(6, 5)
GRID = 48


@cache
def tails(fraction):
    """Upper bounds for sum |z_p|^m and sum p|z_p|^m on positive odd p>=3."""
    h = N * fraction / 2
    if h.denominator != 1 or h <= 1:
        raise ValueError("The mesh must give positive integral exponents")
    beta = C / N
    def base(p):
        return 1 + beta * (p*p - 1)
    odds = range(3, 10, 2)
    # Beyond nine the sum is bounded by half of the integral from nine to infinity.
    integral = base(9)**(1-h.numerator) / (4*beta*(h-1))
    raw = sum(1 / base(p)**h.numerator for p in odds) + integral/9
    weighted = sum(p / base(p)**h.numerator for p in odds) + integral
    return raw, weighted


def mixed_bounds(low, high):
    short, short_deriv = tails(low)
    long, long_deriv = tails(1-high)
    value = 1 + 2*(short + long + short*long)
    derivative = (1-2*low) + 2*(
        high*(long + short_deriv*(1+long)) +
        (1-low)*(short + long_deriv*(1+short))
    )
    return value, derivative


def check():
    base_error, base_deriv = tails(Q(1))
    largest = Q(0)
    for i in range(16, 24):
        q, r = Q(i, GRID), Q(i+1, GRID)
        h_max = min(Q(7,10), (1-2*q+Q(1,N))/q)
        bounds = [mixed_bounds(Q(j, GRID), Q(j+1, GRID)) for j in range(i,24)]
        a = max(pair[0] for pair in bounds)
        b = max(pair[1] for pair in bounds)
        # sqrt(N*C)>15, and (n+1-k)/n >= 1-r.
        lag = 2*(1+tails(q)[0])*(1+tails(1-r)[0]) / (15*(1-r))
        for mass in (0, h_max):
            error = (base_error + mass*a)**2 + (base_deriv + mass*b + lag)**2
            largest = max(largest, error/(1+mass)**2)
    if largest >= Q(99,100):
        raise ArithmeticError("Insufficient uniform derivative margin")
    # Join using 333/106 < pi < 22/7 and sin(u) >= u-u^3/6.
    join = (Q(7,20)*Q(333,106))**2 * Q(191,192) * (1-Q(121,100)/(6*N))**2
    if join <= C:
        raise ArithmeticError("Phase samples miss the cutoff")
    print("All 16 rational endpoint bounds are below 99/100. The front join exceeds 6/5.")


if __name__ == "__main__":
    check()
