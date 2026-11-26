from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations_with_replacement, product
from math import comb, gcd, prod


@lru_cache(maxsize=None)
def rows(d, lo, hi):
    return tuple(
        tuple((mask >> j) & 1 for j in range(d))
        for mask in range(1 << d)
        if lo <= mask.bit_count() <= hi
    )


def margins(d, intervals):
    counts = {(0,) * d: 1}
    for lo, hi in intervals:
        new = defaultdict(int)
        for u, multiplicity in counts.items():
            for row in rows(d, lo, hi):
                v = tuple(x + y for x, y in zip(u, row))
                new[v] += multiplicity
        counts = new
    return counts


def balanced_poly(d, intervals):
    counts = margins(d, intervals)
    coefficients = [counts.get((k,) * d, 0) for k in range(len(intervals) + 1)]
    while coefficients and coefficients[-1] == 0:
        coefficients.pop()
    return tuple(coefficients)


def smoothing_replay():
    profiles = 0
    transfers = 0
    for n, d in ((3, 3), (4, 4), (5, 4), (4, 5), (6, 4)):
        for s in combinations_with_replacement(range(d + 1), n):
            total = sum(s)
            k, rem = divmod(total, d)
            if rem:
                continue
            counts = margins(d, tuple((v, v) for v in s))
            unrestricted = prod(comb(d, v) for v in s)
            assert sum(counts.values()) == unrestricted
            balanced = counts.get((k,) * d, 0)
            budget = min((n + 1) ** d, comb(total + d - 1, d - 1))
            assert balanced == max(counts.values())
            assert balanced * budget >= unrestricted
            for u, number in counts.items():
                for i, j in product(range(d), repeat=2):
                    if u[i] >= u[j] + 2:
                        v = list(u)
                        v[i] -= 1
                        v[j] += 1
                        assert counts.get(tuple(v), 0) >= number
                        transfers += 1
            profiles += 1
    return profiles, transfers


def primitive(p):
    common = gcd(*p)
    return [c // common for c in p]


@lru_cache(maxsize=None)
def disk_count(a, radius):
    # Schur recursion on the unit disk for the integer multiple of A(radius*z).
    # Return None if strict recursion cannot certify a boundary-free circle.
    degree = len(a) - 1
    u, v = radius.numerator, radius.denominator
    p = primitive([c * u**j * v**(degree-j) for j, c in enumerate(a)])
    count = 0
    while len(p) > 1:
        low, high = p[0], p[-1]
        if abs(low) == abs(high):
            return None
        if abs(low) < abs(high):
            p = primitive([high * x - low * y for x, y in zip(p[1:], p[-2::-1])])
            count += 1
        else:
            p = primitive([low * x - high * y for x, y in zip(p[:-1], p[:0:-1])])
    return count


def modulus_brackets(a, depth=40):
    degree = len(a) - 1
    if degree == 0:
        return []
    largest = max((Q(abs(b), abs(a[-1])) for b in a[:-1]), default=Q(0))
    high = Q(largest.numerator // largest.denominator + 2)
    assert disk_count(a, high) == degree
    zero_count = next(i for i, c in enumerate(a) if c)
    brackets = [(Q(0), Q(0))] * zero_count
    for j in range(zero_count + 1, degree + 1):
        lo, hi = Q(0), high
        for _ in range(depth):
            for position in (Q(1, 2), Q(1, 4), Q(3, 4), Q(3, 8), Q(5, 8)):
                candidate = lo + (hi - lo) * position
                count = disk_count(a, candidate)
                if count is not None:
                    break
            else:
                raise ValueError("all dyadic subdivisions gave a Schur tie")
            if count >= j:
                hi = candidate
            else:
                lo = candidate
        brackets.append((lo, hi))
    return brackets


def evaluate(a, x):
    out = 0
    for c in reversed(a):
        out = x * out + c
    return out


def mahler_bracket(a, roots, radius, count):
    if count == 0:
        return Q(abs(a[0])), Q(abs(a[0]))
    if count == len(a) - 1:
        value = abs(a[-1]) * radius**count
        return value, value
    return tuple(
        abs(a[-1]) * prod(max(radius, root[side]) for root in roots)
        for side in (0, 1)
    )


def jensen_replay(name, a):
    roots = modulus_brackets(a)
    radii = (
        Q(1, 128), Q(1, 32), Q(1, 16), Q(1, 8), Q(1, 4), Q(1, 2),
        Q(3, 4), Q(1), Q(3, 2), Q(2), Q(3), Q(4), Q(8), Q(16)
    )
    nchecks = 0
    secants = 0
    crossings = []
    previous = None
    for t in radii:
        count = disk_count(a, t)
        if count is None:
            continue
        lo, hi = mahler_bracket(a, roots, t, count)
        assert lo <= hi <= evaluate(a, t), (name, t, lo, hi)
        for j, b in enumerate(a):
            assert b * t**j <= comb(len(a) - 1, j) * lo, (name, j, t)
            nchecks += 1
        if previous is not None:
            u, low_u, high_u, old = previous
            if old < count:
                z = t/u
                assert z**old < lo/high_u <= hi/low_u < z**count, (name, u, t)
                secants += 1
                crossings.append(f"{u}:{t} carries {count-old}")
        previous = t, lo, hi, count
    return nchecks, secants, ", ".join(crossings)


@lru_cache(maxsize=None)
def log_small(x, terms=24):
    w = (x - 1) / (x + 1)
    assert 0 <= w <= Q(1, 3)
    low = 2 * sum((w**(2*j+1)/(2*j+1) for j in range(terms)), Q(0))
    tail = 2 * w**(2*terms+1) / ((2*terms+1)*(1 - w*w))
    return low, low + tail


@lru_cache(maxsize=None)
def log_bounds(x):
    x = Q(x)
    if x < 1:
        lo, hi = log_bounds(1/x)
        return -hi, -lo
    power = x.numerator.bit_length() - x.denominator.bit_length()
    if x < 2**power:
        power -= 1
    q = x/2**power
    lo, hi = log_small(q)
    lo2, hi2 = log_small(Q(2))
    return lo + power*lo2, hi + power*hi2


def h_bounds(x):
    if x == 0 or x == 1:
        return Q(0), Q(0)
    a = log_bounds(1/x)
    b = log_bounds(1/(1-x))
    return tuple(x*a[j] + (1-x)*b[j] for j in (0, 1))


def e_bounds(n, d, b):
    return tuple(
        h_bounds(Q(1, n))[i] + h_bounds(Q(1, d))[i] + b[i]/n
        + log_bounds(n+1)[i]/n + log_bounds(d+1)[i]/d
        + log_bounds(2)[i]/d
        for i in (0, 1)
    )


def dense_pressure(n, d, cap, w, a):
    x = min(w/(1+w), Q(cap,d))
    v = log_bounds(w)
    phi = tuple(h_bounds(x)[i]+x*v[i] for i in (0, 1))
    b = log_bounds(max(w,1/w))
    offset = e_bounds(n,d,b)
    k = (n*x.numerator)//x.denominator
    t = w**d
    m_lo = Q(a[k], comb(len(a)-1,k))*t**k
    m_hi = evaluate(a,t)
    assert phi[1]-offset[0] <= log_bounds(m_lo)[0]/(n*d)
    assert log_bounds(m_hi)[1]/(n*d) <= phi[0]+log_bounds(n+1)[0]/(n*d)



def dense_estimate(n, d, cap, w, delta, count):
    x = min(w/(1+w), Q(cap,d))
    low_v, high_v = log_bounds(w)
    b_hi = max(-low_v, high_v) + delta
    u_hi = log_bounds(n+1)[1]/(n*d)
    upper = delta/8 + (u_hi + e_bounds(n,d,(b_hi,b_hi))[1])/delta
    assert abs(Q(count,n)-x) <= upper
    return upper


def no_full_rows(n, d, constrained):
    cap_total = n*d-constrained
    return tuple(
        sum((-1)**j * comb(constrained,j) * comb(n-j,k-j)**d
            for j in range(min(k,constrained)+1))
        for k in range(cap_total//d + 1)
    )


def real_dominance_count(a, t):
    # Curvature >9 gives absolute monomial dominance on each geometric circle.
    degree = len(a) - 1
    assert all(a[k]**2 > 9*a[k-1]*a[k+1] for k in range(1, degree))
    below = max((k for k in range(1,degree) if a[k-1] < t*t*a[k+1]), default=0)
    higher = min((k for k in range(1,degree) if a[k-1] > t*t*a[k+1]), default=degree)
    assert higher == below + 1
    p = evaluate(a, -t)
    assert p != 0
    return below if p*(-1)**below > 0 else higher


def main():
    profiles, transfers = smoothing_replay()
    print(f"Smoothing: {profiles} sorted size profiles, {transfers} balancing moves")
    cases = (
        ("homogeneous", 3, ((0,2),)*5),
        ("two caps", 3, ((0,1), (0,2), (0,1), (0,2), (0,2), (0,1), (0,2))),
        ("three caps", 4, ((0,1), (0,2), (0,1), (0,2), (0,3), (0,3)))
    )
    all_cases = []
    for name, d, caps in cases:
        a = balanced_poly(d,caps)
        holes = balanced_poly(d,tuple((d-b,d-a) for a,b in caps))
        assert holes == (0,)*(len(caps)+1-len(a)) + a[::-1]
        all_cases += [(name,a),(name+" holes",holes)]
    all_cases += [("nonreal", (1,2,1,2)), ("repeated moduli", (1,0,2,0,1))]
    nchecks = secants = 0
    for name,a in all_cases:
        c,s,description = jensen_replay(name,a)
        nchecks += c
        secants += s
        print(f"{name}: {a}; {description}")
    print(f"Jensen: {nchecks} coefficient bounds, {secants} strict root-count secants")
    # At the excluded radius 1, (1+q^2)^2 has four boundary roots.
    repeated = (1,0,2,0,1)
    assert disk_count(repeated,Q(1,2)) == 0 and disk_count(repeated,Q(2)) == 4
    assert repeated == tuple(sum(a*b for j,a in enumerate((1,0,1))
                                 for k,b in enumerate((1,0,1)) if j+k==i)
                             for i in range(5))
    assert all(Q(c,comb(4,j))<=1 for j,c in enumerate(repeated))
    print("Exact boundary at radius 1: the product (1+q^2)^2 has left count 0 and right count 4.")

    n=d=64
    cap=d-1
    a=no_full_rows(n,d,n)
    for w in (Q(1,2),Q(1),Q(2)):
        count=real_dominance_count(a,w**d)
        dense_pressure(n,d,cap,w,a)
        top=dense_estimate(n,d,cap,w,Q(3,2),count)
        assert top < Q(42,100)
        if w == 1:
            # v=0 gives a symmetric nonvacuous integer interval for C.
            assert top < Q(203,500)
            assert 7 <= count <= 57
        print(f"Dense finite estimate: n=d={d}, cap={cap}, w={w}, C={count}, rational RHS < {'203/500' if w == 1 else '42/100'}")

    # Apply the theorem to an aspect-four cap-transition case without expanding P.
    n, d, cap = 10**6, 250000, 127000
    delta = Q(1,32)
    B = log_bounds(2)[1] + delta
    upper = delta/8 + (log_bounds(n+1)[1]/(n*d) + e_bounds(n,d,(B,B))[1])/delta
    assert upper < Q(17,2000)
    assert Q(1,3) < Q(cap,d)
    assert (Q(1,3)-Q(17,2000))*n > 324833 and (Q(1,3)+Q(17,2000))*n < 341834
    print("Finite theorem at n=1000000, d=250000, r=127000: radius 2^(-250000), count 324834..341833.")


if __name__ == "__main__":
    main()
