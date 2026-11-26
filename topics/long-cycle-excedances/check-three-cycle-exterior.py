"""Certify the fixed-rank exterior brackets of the finite three-cycle band."""
from argparse import ArgumentParser
from fractions import Fraction as Q
from functools import lru_cache
from hashlib import sha256
from math import comb

from flint import arb, arb_poly, ctx, fmpz_poly

KEEP = 48
GRID = 1 << 24
T = fmpz_poly([0, 1])
ctx.prec = 160


def check_middle_join():
    max_angle = 20 * Q(22, 7) / 192
    sine_factor = 1 - max_angle**2 / 6
    assert 5 * Q(157, 50) * sine_factor > 14
    assert (20 * Q(157, 50) * sine_factor)**2 / 2199 > Q(149, 100)


def next_e(e, n, lag):
    return (T * (1-T) * e.derivative() + n*T*e + lag).truncate(KEEP+1)


def eulerian(last):
    rows = [fmpz_poly(1), T]
    for n in range(1, last):
        rows.append(next_e(rows[-1], n+1, fmpz_poly()))
    return rows


@lru_cache(maxsize=100_000)
def modulus(n, phase):
    if phase == 0:
        return arb(0)
    pi = arb.pi()
    return (-pi * (pi*phase/(n*GRID)).cot()).exp()


@lru_cache(maxsize=4096)
def tail_factors(n):
    return arb(KEEP+1)**(n+1), (arb(KEEP+2)/(KEEP+1))**(n+1)


@lru_cache(maxsize=200_000)
def endpoint(n, phase):
    x = modulus(n, phase)
    if phase == 0:
        return -x, x
    prefactor, ratio = tail_factors(n)
    denominator = 1-x*ratio
    if not denominator > 0:
        raise ArithmeticError(f"tail ratio at {(n, phase)}")
    return -x, x**KEEP*prefactor/denominator


def sign(poly, t, error):
    v = poly(t)
    if v > error:
        return 1
    if v < -error:
        return -1
    return 0


def check_exterior(n, k, e, actual, inverse, digest):
    polys = tuple(arb_poly(poly.right_shift(1)) for poly in (e, actual, inverse))
    old, plus, minus = polys
    bound = 0

    def old_sign(phase):
        return sign(old, *endpoint(n, phase))

    def both(phase, target):
        args = endpoint(n, phase)
        return sign(plus, *args) == target and sign(minus, *args) == target

    left = 0
    previous_right = 0
    for rank in range(1, 20):
        goal = (-1)**rank
        right = (rank+1)*GRID
        if old_sign(right) != goal:
            raise ArithmeticError(f"failed checkpoint at {(n, k, rank)}")
        left_correct = both(left, goal)
        right_correct = both(right, goal)
        while not (left_correct and right_correct) or left <= previous_right:
            midpoint = (left + right) // 2
            if not left < midpoint < right:
                raise ArithmeticError(f"grid exhausted at {(n, k, rank)}")
            found = old_sign(midpoint)
            if found == 0:
                raise ArithmeticError(f"undecided midpoint at {(n, k, rank)}")
            if found == goal:
                right = midpoint
                right_correct = both(right, goal)
            else:
                left = midpoint
                left_correct = both(left, goal)
            bound += 1
        digest.update(f"{n},{k},{rank},{left},{right}\n".encode("ascii"))
        previous_right = right
        # Carry the original integer phase endpoint to the next rank.
        left = (rank+1)*GRID
    return bound


def run(args):
    A = eulerian(args.last_k-1)
    checked = subdivisions = 0
    for k in range(args.first_k, args.last_k+1):
        lo = max(3*k-1, 192, args.min_old)
        hi = min(4*k-1, args.max_old)
        if lo > hi:
            continue
        rows = [fmpz_poly(1)] + [fmpz_poly() for _ in range(k-1)]
        pairs = 0
        digest = sha256()
        for n in range(k-1, hi+1):
            lag = comb(n, k-1)*(A[k-1]*rows[n+1-k]).truncate(KEEP+1)
            actual = next_e(rows[n], n, lag)
            rows.append(actual)
            if lo <= n:
                inverse = actual-2*lag
                subdivisions += check_exterior(n, k, rows[n], actual, inverse, digest)
                pairs += 1
        checked += pairs
        print(f"k={k}: {pairs} pairs; cumulative {checked}, subdivisions {subdivisions}, "
              f"bracket digest {digest.hexdigest()}", flush=True)
    expected = sum(
        max(0, min(4*k-1,args.max_old)-max(3*k-1,192,args.min_old)+1)
        for k in range(args.first_k,args.last_k+1)
    )
    if checked != expected:
        raise ArithmeticError(("pair coverage",checked,expected))


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--first-k", type=int, default=49)
    parser.add_argument("--last-k", type=int, default=733)
    parser.add_argument("--min-old", type=int, default=192)
    parser.add_argument("--max-old", type=int, default=2199)
    args = parser.parse_args()
    if not 3 <= args.first_k <= args.last_k or not 192 <= args.min_old <= args.max_old <= 2199:
        parser.error("require k >= 3 and 192 <= min-old <= max-old <= 2199")
    check_middle_join()
    run(args)
