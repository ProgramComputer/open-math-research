"""Independent integer replay for the mixed-phase balanced-array signs."""
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import json

N, D, R = 1_000_000, 250_000, 127_000
FIRST, LAST = 505662, 506470
PROB, MASS, ROUND = 2**52, 2**68, 2**58
C = Q(1, 3_000_000)


def up(a, b):
    return (a + b - 1) // b


def grid(x, scale, upper=False):
    numerator = x.numerator * scale
    return up(numerator, x.denominator) if upper else numerator // x.denominator


@lru_cache(maxsize=1000)
def cap_atom(trials, p):
    """Bounds for the cap atom at dyadic probability p/PROB."""
    a, b = PROB - p, p
    lower = upper = total_l = total_u = MASS
    for j in range(R, 0, -1):
        num, den = j * a, (trials + 1 - j) * b
        lower = lower * num // den
        upper = up(upper * num, den)
        total_l += lower
        total_u += upper
        if num < den and upper < 1 << 20:
            # Every unvisited consecutive ratio is at most num/den.
            total_u += up(upper * num, den - num)
            break
    return Q(MASS, total_u), Q(MASS, total_l)


def atom(trials, odds, upper=False):
    p = grid(odds / (1 + odds), PROB, upper)
    return cap_atom(trials, p)[upper]


def loss_factor(height, quota):
    return Q((D-R)*height, D*(height-quota))


def residual(n, k, upper_witness):
    loss = Q(0)
    for j in range(17, -1, -1):
        h, l = n-j, k-2-j
        assert 0 < l and l+1 < h and D*(l+1) <= h*R
        odds = Q(l, h-l) / (1-loss)
        loss = Q(grid(loss_factor(h, l)*atom(D, odds), ROUND), ROUND)
    p = grid(Q(upper_witness, 10**14), PROB, True)
    z = Q(p, PROB)
    q = cap_atom(D, p)[1]
    assert Q(k, n) < z < 1
    assert D*(z-Q(k, n)) >= z*(D-R)*q
    return loss, loss_factor(n, k)*q


def log_loss(loss, upper=False):
    assert 0 <= loss < Q(1, 100)
    value = sum(loss**j / j for j in range(1, 6))
    if upper:
        value += loss**6 / (6*(1-loss))
    return Q(grid(value, ROUND, upper), ROUND)


def phase(k, witness, force_bins=False):
    assert k >= 2 and k+2 < N and D*(k+2) <= (N-1)*R
    lo, hi = residual(N-1, k+1, witness)
    assert 0 <= lo <= hi < 1
    a, b = Q(k,N-k), Q(k+1,N-k-1)
    assert R*((b-a)/a)**2 / 8 <= C

    def harmonic(x):
        return 1 / ((1-x)/a + x/b)

    def arith(x):
        return (1-x)*a + x*b

    def low(w):
        return log_loss((1-C)*atom(D-1, w/(1-lo)))

    def high(w):
        return log_loss(atom(D-1, w/(1-hi), True)/(1-C), True)

    maximum = b/(1-hi)
    gap = R - (D-1)*maximum/(1+maximum)
    # The exact variance bound sharpens m/4 whenever p differs from 1/2.
    # Use m/4 unconditionally here so it covers both lo and hi endpoints.
    if not force_bins and gap > 0 and 4*gap**2 >= D-1:
        return (D*low(harmonic(Q(1,2))), D*(high(a)+high(b))/2), True
    sums = [Q(0), Q(0)]
    for i in range(32):
        j0, j1 = i*D//32, (i+1)*D//32-1
        count = j1-j0+1
        sums[0] += count*low(harmonic(Q(j0,D-1)))
        sums[1] += count*high(arith(Q(j1,D-1)))
    return tuple(sums), False


def power(base, n, upper):
    def rounded_product(x, y):
        return up(x*y, ROUND) if upper else x*y // ROUND

    a, out = grid(base, ROUND, upper), ROUND
    while n:
        if n % 2:
            out = rounded_product(out,a)
        n //= 2
        if n:
            a = rounded_product(a,a)
    return Q(out, ROUND)


def exp_minus(x, upper):
    assert 0 <= x <= 16
    z = x / 16
    total = term = Q(1)
    # Alternating Taylor bounds at z <= 1, then fix the scale by powering.
    for j in range(1, 17 if upper else 16):
        term *= -z/j
        total += term
    return power(total, 16, upper)


def mag(k, j, upper):
    c = Q(k*(k+1),(N-k)*(N-k+1))
    rel = Q(1)
    for h in range(1, abs(j)+1):
        rel *= Q(N-k+1-h,k+h) if j > 0 else Q(k+1-h,N-k+h)
    return power(rel**2 * c**j, D//2, upper)


def parity(k, bracket):
    for i in range(k-3,k+2):
        assert bracket[i][1] < bracket[i+1][0], (k, i)
    s = {i: bracket[k+i][i % 2] for i in range(-3,3)}
    # Cap contribution at the true geometric node: multiply P_{k+j}/P_k
    # by (P_{k-1}/P_{k+1})^(j/2), treating s_i as -log(P_{k+i+1}/P_{k+i}).
    drift = (s[-1]+s[0])/2
    parity_bound = Q(1)
    for j in (-3,-2,-1,1,2,3):
        attenuation = (sum(s[i] for i in range(j))-j*drift if j > 0 else
                      -sum(s[i] for i in range(j,0))-j*drift)
        upper = j % 2 == 1
        value = mag(k,j,upper)*exp_minus(attenuation,upper)
        parity_bound += -value if upper else value
    return parity_bound


def main():
    table = json.loads((Path(__file__).parent.parent/"tilts.json").read_text())
    bracket, convex = {}, 0
    for k in range(FIRST-3,LAST+3):
        bracket[k], used = phase(k, table[str(k)])
        convex += used
    assert len(bracket) == 814
    minimum, index = min((parity(k,bracket),k) for k in range(FIRST,LAST+1))
    assert minimum > Q(1,1000)
    print(f"{LAST-FIRST+1} quotas {FIRST}..{LAST}; {convex} convex enclosures among {len(bracket)} phase sums.")
    print(f"Minimum lower bound at {index} exceeds {grid(minimum,10**8)}/10^8.")
    for k in (FIRST,506000,LAST):
        binned, _ = phase(k, table[str(k)], True)
        lo, hi = bracket[k]
        assert binned[0] <= hi and lo <= binned[1]
    print("Three independent 32-block enclosures overlap the convex enclosures.")
    k = 507000
    witnesses = (50751351987237,50751559109376,50751766471673,50751974074797,
                 50752181919425,50752390006225)
    slopes = (Q(514),Q(5143,10),Q(1033,2),Q(1033,2),Q(5189,10),Q(519))
    for i, (witness, slope) in enumerate(zip(witnesses,slopes), k-3):
        (lo,hi), _ = phase(i,witness)
        assert lo < slope < hi, (i, lo, hi)
    assert tuple(sorted(slopes)) == slopes and slopes[2] == slopes[3]
    assert mag(k, 1, False) > Q(3,5)
    for j, shift in ((-2,slopes[3]-slopes[1]),(2,slopes[4]-slopes[2])):
        assert mag(k,j,True) < Q(7,50)
        assert exp_minus(shift,True) < Q(1,8)
    assert 1 - 2*Q(3,5) + 2*Q(7,50)/8 == -Q(33,200)
    baseline = Q(N,N+2)
    assert exp_minus(baseline, True) < Q(4,9)
    print("Synthetic obstruction replayed at 507000, with all six slopes strictly feasible.")
    print("Unrestricted curvature floor exp(n/(n+2)) exceeds 9/4.")


if __name__ == "__main__":
    main()
