from fractions import Fraction as F
from functools import cache
from math import comb, factorial
from pathlib import Path
import json

lamlo = F(693147180559945309417232121458, 10**30)
lamhi = lamlo + F(1, 10**30)


def principal(p):
    # Invert (1-exp(-w))/w, then raise its truncated series to p.
    base = [F(1)]
    for n in range(1, p):
        base.append(
            -sum(F((-1) ** k, factorial(k + 1)) * base[n - k] for k in range(1, n + 1))
        )
    out = [F(1)] + [F(0)] * (p - 1)
    for _ in range(p):
        out = [sum(base[i] * out[n - i] for i in range(n + 1)) for n in range(p)]
    assert all(x > 0 for x in out)
    return out


L = {p: principal(p) for p in range(1, 9)}
error_multiplier = {}


def prod(items):
    v = F(1)
    for x in items:
        v *= x
    return v


def binom_poly(x, k):
    return prod(x - i for i in range(k)) / factorial(k)


def bounds_constants(d):
    # Coefficients of unrestricted G^p. All finite arithmetic is rational.
    lo = sum(2 * F(1, 3) ** (2 * i + 1) / (2 * i + 1) for i in range(40))
    assert lamlo < lo < lo + 2 * F(1, 3) ** 81 / (81 * (1 - F(1, 9))) < lamhi
    g = [F(1)]
    for n in range(1, 34):
        g.append(sum(g[n - k] / factorial(k) for k in range(1, n + 1)))
    powers = {1: g}
    for p in range(2, d + 2):
        powers[p] = [
            sum(powers[p - 1][i] * g[n - i] for i in range(n + 1)) for n in range(34)
        ]
    for p in range(1, d + 2):
        k = p - 1
        bound = F(1)
        for s in range(-32, 33):
            top = bottom = 0
            for r, v in enumerate(L[p]):
                scale = v * binom_poly(F(s + k - r), k - r)
                u, w = sorted((scale * lamlo**r, scale * lamhi**r))
                bottom += u
                top += w
            if s < 0:
                left = right = 0
            else:
                val = 2**p * powers[p][s]
                left = val * lamlo ** (p + s)
                right = val * lamhi ** (p + s)
            while max(abs(right - bottom), abs(left - top)) > bound * F(2) ** (-s):
                bound *= 2
        assert bound == 1
        error_multiplier[p] = bound
        # For s=-a with a>=32 absolute terms bounded by 2^a via binomial.
        assert (
            sum(
                abs(v) * lamhi**r * F(32) ** (k - r) / factorial(k - r)
                for r, v in enumerate(L[p])
            )
            < 2**32
        )
        assert F(33, 32) ** k < 2
        # |z|=4 analytic remainder <=11^p + sum |principal coefficient|.
        assert 11**p + sum(abs(v) * lamhi**r for r, v in enumerate(L[p])) < 2**32
    c = powers[2]
    for r in range(10):
        assert (r + 1) * (lamlo * c[r + 1] / c[r] - 1) > F(1, 4)


def pmf_moment(k, l, J):
    if not l:
        return F(1)
    q = lamhi / (J + 1)
    return comb(k + l - 1, l) * q**l / (1 - q) ** (k + l)


def coeff_intervals(d, cl, ch, hl, hh, J):
    A = []
    B = []
    for k in range(d + 1):
        p = k + 1
        low = []
        high = []
        for r in range(k + 1):
            # Laurent coefficients after multiplying V^k.
            x = L[p][r] * lamlo**r
            y = L[p][r] * lamhi**r
            for ell in range(1, r + 1):
                b = L[p][r - ell] * lamhi ** (r - ell) * pmf_moment(k, ell, J)
                if ell % 2:
                    x -= b
                else:
                    y += b
            assert x >= 0
            low.append(x)
            high.append(y)
        w, z = cl - k, ch - k
        # s=(c-k)/h; cl>=k for old strips.
        floor_s = int(w / hh)
        q = lamhi / (J + 1)
        moment2 = (1 - 2 * q) ** (-k)
        exp = F(1, 2 ** min(80, max(0, floor_s)))
        for delta, rows in ((0, A), (1, B)):
            if delta and k == 0:
                err = F(2 * J, 2 ** min(80, d * J))
                rows.append((-err, err))
                continue
            a = b = 0
            for r in range(k + 1 - delta):
                f = k - r
                a += (
                    low[r]
                    * hl**r
                    * prod(w + i * hl for i in range(1 + delta, f + 1))
                    / factorial(f - delta)
                )
                b += (
                    high[r]
                    * hh**r
                    * prod(z + i * hh for i in range(1 + delta, f + 1))
                    / factorial(f - delta)
                )
            err = (
                error_multiplier[p]
                * hh ** (k - delta)
                * moment2
                * exp
                * (F(3, 2) if delta else 1)
            )
            rows.append(
                (max(0, a - err), b + err)
                if not delta or k >= 1
                else (a - err, b + err)
            )
    B.append((F(0), (2 * lamhi) ** (d + 2) * hh**d if ch >= d + 1 - hh else F(0)))
    return A, B


def center_roots(A):
    from flint import fmpq_poly, fmpq

    d = len(A) - 1
    out = []
    for side in (0, 1):
        raw = [F(0)] * (d + 1)
        for k in range(d + 1):
            v = A[k][side ^ (k % 2)]
            for ell in range(k, d + 1):
                raw[ell] += (-1) ** ell * comb(d - k, ell - k) * v
        roots = fmpq_poly(
            [fmpq(x.numerator, x.denominator) for x in raw]
        ).complex_roots()
        if len(roots) != d or any(not z.imag.contains(0) for z, _ in roots):
            return []
        out.append(sorted(float(z.real.mid()) for z, _ in roots))
    return [(min(x, y), max(x, y)) for x, y in zip(*out)]


def value(C, a, b):
    d = len(C) - 1
    lo = hi = 0
    for k, (l, r) in enumerate(C):
        v = a**k * (1 - b) ** (d - k)
        w = b**k * (1 - a) ** (d - k)
        x = min(l * v, l * w)
        y = max(r * v, r * w)
        if k % 2:
            lo -= y
            hi -= x
        else:
            lo += x
            hi += y
    return lo, hi


def sign(z, i):
    return z[0] > 0 if i == 1 else z[1] < 0


def seam(A, B, cl, ch, hh, a):
    d = len(A) - 1
    if ch >= d + 1 - hh or a <= 0:
        return False
    w = (1 - a) / a
    h = A[d - 1][0] - sum(A[k][1] * w ** (d - k - 1) for k in range(d - 1))
    K = sum(max(abs(v) for v in B[k]) * w ** (d - 1 - k) for k in range(d))
    return h > 4 * (ch - d + hh) * K


def trybox(A, B, cl, ch, hh):
    d = len(A) - 1
    bounds = center_roots(A)
    if not bounds:
        return None
    out = []
    for i, (l, r) in enumerate(bounds):
        # Use narrow brackets first; each assertion below is exact.
        for e in range(36, 1, -1):
            g = F(1, 2**e)
            a = max(0, F(int(l / g) - 1) * g)
            b = min(1, F(int(r / g) + 2) * g)
            plus = (-1) ** i
            if out and a <= out[-1][1]:
                continue
            if not sign(value(A, a, a), plus):
                continue
            if i == d - 1 and b == 1 and seam(A, B, cl, ch, hh, a):
                out.append((a, b, "seam"))
                break
            if sign(value(A, b, b), -plus) and sign(value(B, a, b), -plus):
                out.append((a, b, "ordinary"))
                break
            if i == d - 1 and seam(A, B, cl, ch, hh, a):
                out.append((a, F(1), "seam"))
                break
        else:
            return None
    return out


def run(d, J):
    stack = [(F(d), F(d + 1), F(0), F(1, J))]
    cells = []
    while stack:
        cl, ch, hl, hh = stack.pop()
        A, B = coeff_intervals(d, cl, ch, hl, hh, J)
        br = trybox(A, B, cl, ch, hh)
        if br:
            cells.append(
                [str(x) for x in (cl, ch, hl, hh)]
                + [[[str(a), str(b), m] for a, b, m in br]]
            )
            continue
        if ch - cl < F(1, 2**16) and hh - hl < F(1, J * 2**12):
            raise ValueError((cl, ch, hl, hh))
        if ch - cl >= 8 * (hh - hl):
            mid = (cl + ch) / 2
            stack += [(mid, ch, hl, hh), (cl, mid, hl, hh)]
        else:
            mid = (hl + hh) / 2
            stack += [(cl, ch, mid, hh), (cl, ch, hl, mid)]
    fn = Path(__file__).parent / f"finite-{d}-{J}.json"
    fn.write_text(json.dumps({"d": d, "J": J, "cells": cells}))
    print("verified analytic boxes:", d, J, len(cells), flush=True)


if not __debug__:
    raise SystemExit("Run the checker with Python assertions enabled.")

if __name__ == "__main__":
    import sys

    d = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    bounds_constants(d)
    run(d, int(sys.argv[1]))
