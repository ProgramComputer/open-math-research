"""Exact integer/rational enclosures for the joint value and derivative comparison."""
from fractions import Fraction as F
from functools import lru_cache
from math import factorial, isqrt

G = 1 << 56
B = 4
P = 63
POLES = tuple(range(-P, P + 1, 2))
GAPS = tuple((a, [(i, abs(q-a)) for i, q in enumerate(POLES) if q != a])
             for a in (1, *range(3, P+3, 2)))
U = F(6, 5)
SMALL = F(547, 1000)
LARGE = F(4, 7)


def ceildiv(a, b):
    return -(-a // b)


def up(x):
    return ceildiv(x.numerator * G, x.denominator)


@lru_cache(None)
def lattice(c):
    """Dyadic upper masses for kernel (1+c(p²−1))^−96 and its tails."""
    assert c > 0 and 191*c*P*P > 1-c
    v = {p: up((1+c*(p*p-1))**(-96)) for p in range(1, P+1, 2)}
    # Two odd tails after +/- P, one half-integral per tail.
    tail1 = up((1+c*(P*P-1))**(-95)/(190*c))
    tail0 = ceildiv(tail1, P)
    return tuple(v[abs(p)] for p in POLES), tail0, tail1


@lru_cache(None)
def stars(c):
    w, tail0, tail1 = lattice(c)
    return (F(max(sum(ceildiv(w[i], gap) for i, gap in row)
                  for _, row in GAPS) + ceildiv(tail0, 2), G),
            F(max(sum(ceildiv(abs(POLES[i])*w[i], gap) for i, gap in row)
                  for _, row in GAPS) + ceildiv(tail1, 2), G))


def mass(c):
    w, tail0, _ = lattice(c)
    return F(sum(w) + tail0, G)


@lru_cache(None)
def first_nonprincipal(c):
    w, _, tail1 = lattice(c)
    return F(sum(abs(p)*v for p, v in zip(POLES, w) if abs(p) > 1) + tail1, G)


def degree_masses(K, X):
    """Yield upper bin, lower degree/k, and upper k times |b|-mass."""
    yield B, F(1), F(1)
    for j in range(1, X):
        for h in range(1, B+1):
            lo = F(j*B+h-1, B)
            hi = lo + F(1, B)
            if j == 1:
                value = 1/(lo-F(1,K)) - 1/hi
                if h == B:
                    value += F(1, 4*K)
            else:
                value = (F(1,B)+F(1,K))/(2*factorial(j))
            yield j*B+h, lo, value


def product(K, low, X, A):
    """Outward integer coefficients for exp(L)-1 and exp(L)J."""
    top = (B+1)*X
    L = [0]*(top+1)
    J = [0]*(top+1)
    for i, lo, variation in degree_masses(K, X):
        s0, s1 = stars((lo-F(1,K))*U/(192*X))
        L[i] += up(variation*s0/A)
        J[i] += up(variation*(s1*F(i, B)/(low*A) + s0/(K*U)))
    Q = [G]
    for b in range(1, top+1):
        Q.append(ceildiv(sum(i*L[i]*Q[b-i] for i in range(B,min(b,B*X)+1)), b*G))
    D = [ceildiv(sum(J[i]*Q[b-i] for i in range(B,min(b,B*X)+1)), G)
         for b in range(top+1)]
    Q[0] = 0
    return Q, D


def joint(K, low, X, A):
    Q, D = product(K,low,X,A)
    vector = derivative = residual = F(0)
    for b in range(B, len(Q)):
        hi = F(b,B)
        lo = max(F(1), F(b,B+1))
        # Terms with distinguished degree less than k are absent.
        if lo+1 > X:
            continue
        ymax = 1-lo/X
        yn = max(F(1,X), 1-hi/low)
        ym = max(F(1,X), 1-(hi+1)/low)
        weight = LARGE if low-hi >= 2 else F(1)
        weight_m = LARGE if low-1-hi >= 2 else F(1)
        c = yn*U/192
        poles, _, tail1 = lattice(c)
        diagonal = (sum(v*max(F(1),ymax*abs(p)) for p,v in zip(POLES,poles))+tail1)/G
        off_diagonal = first_nonprincipal(c/2)/isqrt(K*low)
        vector += F(Q[b],G)*weight*(diagonal+off_diagonal)
        derivative += F(D[b],G)*weight*mass(c)
        residual += F(Q[b],G)*weight_m*mass(ym*U/192)
    lag = mass(U/(192*X))*(LARGE*mass((1-F(1,low))*U/192)+residual)/(A*low)
    # Single-pole tails (real value 1/50 and angular derivative 1/16).
    assert (F(38,1000)/LARGE)**2 > F(1,50)**2 + F(1,16)**2
    return 2*SMALL - (F(38,1000)+vector+derivative+lag)


def exp_lower(x, count=64):
    value = term = F(1)
    for j in range(1,count+1):
        term *= x/j
        value += term
    return value


def verify():
    # Bounds used for d_r. The log 2 lower bound follows from 2*atanh(1/3).
    assert 2*(F(1,3)+F(1,81)) > F(69,100)
    assert exp_lower(F(347,500)) > 2
    assert exp_lower(LARGE-F(1,100)) > F(7,4)
    assert 1+F(347,500)+(1+LARGE)/100 < 3*LARGE
    assert F(1,2)+(F(69,100)-F(1,2))/4 > SMALL
    assert 1+F(69,100)+F(1,2) > 4*SMALL
    # Each row is (least row size, lower and upper aspect, sufficient k sin(theta)).
    rows = [(100000,4,6,F(10)),(100000,6,10,F(10)),(100000,10,16,F(10)),
            (100000,16,25,F(10)),(100000,25,34,F(9)),(100000,34,42,F(8)),
            (100000,42,50,F(27,4)),(100000,50,62,F(7)),
            (100000,62,75,F(7)),(100000,75,86,F(27,4)),
            (120000,86,96,F(7))]
    for least,low,X,A in rows:
        K = least//X
        assert K >= 1000
        if X <= 50:
            assert A**2 * X**2 <= U*least
        else:
            assert A**2*25 <= K and 9*X**2 <= U*least
        slack = joint(K,low,X,A)
        assert slack > 0, (least,low,X,A,slack)
        print(f"n >= {least:6}, {low:2} <= n/k <= {X:2}, A >= {A}, "
              f"joint margin > {int(slack*10**6)}/1000000")
    assert F(89,100)*86 > 47+F(5,2)*F(117,10)
    assert exp_lower(F(117,10)) > 120000
    assert F(89,100)*96 > 47+F(5,2)*F(153,10)
    assert exp_lower(F(153,10)) > 4062720
    print("All joint margins and both outer aspect joins pass.")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O so every inequality is checked.")
    verify()
