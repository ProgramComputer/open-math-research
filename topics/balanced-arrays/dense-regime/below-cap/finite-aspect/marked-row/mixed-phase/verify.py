"""Directed integer intervals for the mixed-phase comparison.

The optional --make-tilts step uses floating point to propose upper-tilt
witnesses. The ordinary replay uses integer and Fraction arithmetic only.
"""
from fractions import Fraction as Q
from functools import lru_cache
from math import ceil, factorial
from pathlib import Path
import argparse
import json

N, D, R = 10**6, 250000, 127000
UNIT = 2**88
GRID = 10**14
DEPTH = 18
BINS = 16
FIRST, LAST = 505662, 506470
TABLE = Path(__file__).with_name("tilts.json")


def floor_scaled(x, scale=UNIT):
    return x.numerator * scale // x.denominator


def ceil_scaled(x, scale=UNIT):
    return -floor_scaled(-x, scale)


@lru_cache(maxsize=2048)
def top(d, odds):
    inverse = 1 / odds
    a, b = inverse.numerator, inverse.denominator
    low = high = sum_low = sum_high = UNIT
    for j in range(R, 0, -1):
        numerator, denominator = j * a, (d - j + 1) * b
        low = low * numerator // denominator
        high = (high * numerator + denominator - 1) // denominator
        sum_low += low
        sum_high += high
        if numerator <= denominator and high <= 4096:
            sum_high += (j - 1) * high
            break
    return Q(UNIT, sum_high), Q(UNIT, sum_low)


def alpha(n, k):
    return Q((D - R) * n, D * (n - k))


def odds(n, k):
    return Q(k, n - k)


def residual_lower(n, k):
    loss = Q(0)
    for j in reversed(range(DEPTH)):
        assert 0 < k-j < n-j and D*(k-j+1) <= (n-j)*R
        shifted_odds = odds(n-j, k-j) / (1-loss)
        loss = Q(floor_scaled(alpha(n-j, k-j) * top(D, shifted_odds)[0], GRID), GRID)
    return loss


def residual_upper(n, k, z_int):
    p, z = Q(k, n), Q(z_int, GRID)
    assert p <= z < 1
    cap_probability = top(D, z / (1-z))[1]
    assert D * (z-p) >= z * (D-R) * cap_probability
    return alpha(n,k) * cap_probability


def loss_log(x):
    assert 0 <= x < Q(1,10)
    lower = sum(x**j/j for j in range(1,8))
    return floor_scaled(lower), ceil_scaled(lower + x**8/(8*(1-x)))


def phase_bounds(k, tilt):
    assert 0 < k-1 and k+2 < N and D*(k+2) <= (N-1)*R
    lower = residual_lower(N-1, k-1)
    upper = residual_upper(N-1, k+1, tilt)
    assert 0 <= lower <= upper < 1
    w = odds(N,k)
    ratio = odds(N,k+1)/w
    c = R*(ratio-1)**2/8
    assert 0 <= c < 1
    max_odds = w*ratio/(1-upper)
    gap = R - (D-1)*max_odds/(1+max_odds)
    if gap > 0 and 4*gap**2 >= D-1:
        center_harmonic = 2*w/(1+1/ratio)
        loss_low = (1-c)*top(D-1,center_harmonic/(1-lower))[0]
        left = top(D-1,w/(1-upper))[1]/(1-c)
        right = top(D-1,max_odds)[1]/(1-c)
        return (Q(D*loss_log(loss_low)[0],UNIT),
            Q(D*(loss_log(left)[1]+loss_log(right)[1]),2*UNIT))
    sum_low = sum_high = 0
    for i in range(BINS):
        a, b = i*D//BINS, (i+1)*D//BINS-1
        a_frac, b_frac = Q(a,D-1), Q(b,D-1)
        harmonic = w / ((1-a_frac)+a_frac/ratio)
        arithmetic = w * ((1-b_frac)+b_frac*ratio)
        loss_low = (1-c) * top(D-1, harmonic/(1-lower))[0]
        loss_high = top(D-1, arithmetic/(1-upper))[1] / (1-c)
        sum_low += (b-a+1)*loss_log(loss_low)[0]
        sum_high += (b-a+1)*loss_log(loss_high)[1]
    return Q(sum_low,UNIT), Q(sum_high,UNIT)


def rounded_power(base, exponent):
    lo, hi = floor_scaled(base), ceil_scaled(base)
    out_lo = out_hi = UNIT
    while exponent:
        if exponent % 2:
            out_lo = out_lo * lo // UNIT
            out_hi = (out_hi * hi + UNIT - 1) // UNIT
        exponent //= 2
        if exponent:
            lo = lo*lo // UNIT
            hi = (hi*hi + UNIT - 1) // UNIT
    return Q(out_lo,UNIT), Q(out_hi,UNIT)


def exp_negative(x):
    assert 0 <= x < 8
    degree=38
    e_low = sum(x**j/factorial(j) for j in range(degree+1))
    e_high = e_low + x**(degree+1)/factorial(degree+1) / (1-x/(degree+2))
    return 1/e_high, 1/e_low


def parity(k, intervals):
    for i in range(-3,2):
        assert intervals[k+i][1] < intervals[k+i+1][0], (k, i, 'ordering')
    s = {i: intervals[k+i][i % 2] for i in range(-3,3)}
    shifts = {
        1: (s[0]-s[-1])/2,
        -2: s[0]-s[-2],
        2: s[1]-s[-1],
        -3: (3*s[0]+s[-1])/2-s[-2]-s[-3],
        3: s[1]+s[2]-(s[0]+3*s[-1])/2,
    }
    center = Q(k*(k+1),(N-k)*(N-k+1))
    ratios = {0: Q(1)}
    for j in range(1,4):
        ratios[j] = ratios[j-1] * Q(N-k-j+1,k+j)
        ratios[-j] = ratios[1-j] * Q(k-j+1,N-k+j)
    def term(i, endpoint):
        unrestricted = rounded_power(ratios[i]**2*center**i,D//2)[endpoint]
        cap = exp_negative(shifts[i])[endpoint]
        return unrestricted * cap
    return 1-2*term(1,1) + term(-2,0) + term(2,0) - term(-3,1) - term(3,1)


def proposed(n,k):
    def approximate_mass(z):
        total = weight = 1.0
        inverse_odds = (1-z)/z
        for j in range(R,0,-1):
            weight *= j*inverse_odds/(D-j+1)
            total += weight
            if weight < 1e-16:
                break
        return 1/total

    p = k/n
    a,b = p, min(0.9999,p+0.02)
    for _ in range(38):
        z = (a+b)/2
        if D*(z-p) < z*(D-R)*approximate_mass(z):
            a=z
        else:
            b=z
    result = ceil(GRID*b)+100
    residual_upper(n,k,result)
    return result


def verify_obstruction():
    k = 507000
    tilt = (50751351987237,50751559109376,50751766471673,50751974074797,
            50752181919425,50752390006225)
    slopes = (Q(514),Q(5143,10),Q(1033,2),Q(1033,2),Q(5189,10),Q(519))
    for q, z, value in zip(range(k-3,k+3),tilt,slopes):
        lower,upper = phase_bounds(q,z)
        assert lower < value < upper
    assert list(slopes) == sorted(slopes)
    assert slopes[2] == slopes[3]
    center = Q(k*(k+1),(N-k)*(N-k+1))
    first = rounded_power(Q(N-k,k+1)**2*center,D//2)
    assert first[0] > Q(3,5)
    baseline = Q(N,N+2)
    assert exp_negative(2*baseline)[1] < Q(7,50)
    assert exp_negative(slopes[3]-slopes[1])[1] < Q(1,8)
    assert exp_negative(slopes[4]-slopes[2])[1] < Q(1,8)
    assert 1-2*Q(3,5)+2*Q(7,50)/8 == -Q(33,200)
    print("At quota 507000 the six independent intervals admit a monotone synthetic slope vector with parity below -33/200.")

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--make-tilts', action='store_true')
    parser.add_argument('--obstruction-only', action='store_true')
    parser.add_argument('--first', type=int, default=FIRST)
    parser.add_argument('--last', type=int, default=LAST)
    args = parser.parse_args()
    if args.obstruction_only:
        verify_obstruction()
        return
    if args.make_tilts:
        values = json.loads(TABLE.read_text()) if TABLE.exists() else {}
        for k in range(args.first-3,args.last+3):
            if str(k) not in values:
                values[str(k)] = proposed(N-1,k+1)
        TABLE.write_text(json.dumps(values,separators=(',',':'))+'\n')
    table = json.loads(TABLE.read_text())
    intervals = {
        k: phase_bounds(k,table[str(k)])
        for k in range(args.first-3,args.last+3)
    }
    minimum = min((parity(k,intervals),k) for k in range(args.first,args.last+1))
    assert minimum[0] > Q(1,1000), (minimum[1],float(minimum[0]))
    print(f"All {args.last-args.first+1} quotas {args.first} through {args.last}: signed seven-term lower bound greater than 1/1000.")
    print(f"Minimum lower bound at quota {minimum[1]}; low decimal display {floor_scaled(minimum[0],10**8)}/100000000.")
    center=506000
    if center in intervals and center-1 in intervals:
        a,b = intervals[center]
        x,y = intervals[center-1]
        print(f"S_{center} bracket on 10^6 grid: {floor_scaled(a,10**6)} to {ceil_scaled(b,10**6)}.")
        print(f"Cap curvature bracket on 10^6 grid: {floor_scaled(a-y,10**6)} to {ceil_scaled(b-x,10**6)}.")
    verify_obstruction()


if __name__ == '__main__':
    main()
