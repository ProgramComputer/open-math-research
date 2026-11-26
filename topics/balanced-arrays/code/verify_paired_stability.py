"""Certify the stability threshold of the bivariate four-column margin enumerator."""
from collections import defaultdict
from itertools import combinations
from math import comb

from flint import fmpq_poly, fmpz_mpoly_ctx, fmpz_poly


def labeled_margins(through):
    row_types = [subset for size in range(3) for subset in combinations(range(4), size)]
    counts = {(0, 0, 0, 0): 1}
    for n in range(through + 1):
        yield {(a, c): value for (a, b, c, d), value in counts.items() if a == b and c == d}
        if n < through:
            new = defaultdict(int)
            for state, value in counts.items():
                for subset in row_types:
                    margin = list(state)
                    for j in subset:
                        margin[j] += 1
                    new[tuple(margin)] += value
            counts = new


def paired_formula(n, x, y):
    def disjoint_pairs(j, z):
        return sum(comb(j, 2*k) * comb(2*k, k) * z**k for k in range(j//2 + 1))

    return sum(comb(n, h) * (x+y)**h * disjoint_pairs(n-h, x) * disjoint_pairs(n-h, y)
               for h in range(n + 1))


def signs_at_endpoints(poly):
    """Sturm variations at minus infinity, zero and plus infinity."""
    neg, zero, pos = [], [], []
    p, q = fmpq_poly(poly), fmpq_poly(poly.derivative())
    while p:
        leading = 1 if p.leading_coefficient() > 0 else -1
        neg.append(leading * (-1)**p.degree())
        if p[0]:
            zero.append(1 if p[0] > 0 else -1)
        pos.append(leading)
        remainder = -(p % q) if q else q
        if remainder:
            numerator = remainder.numer()
            remainder = fmpq_poly(numerator // numerator.content())
        p, q = q, remainder

    def changes(seq):
        return sum(a != b for a, b in zip(seq, seq[1:]))
    return changes(neg), changes(zero), changes(pos)


def shifted(row, shift):
    z = fmpz_poly([0, 1])
    return sum(value * (z+shift)**i * (z-shift)**j for (i, j), value in row.items())


def main():
    ring = fmpz_mpoly_ctx.get(("t", "s"), "lex")
    t, s = ring.gens()
    prefix = [(0, 0), (0, 0), (1, 1), (2, 2), (4, 4)]
    for n, row in enumerate(labeled_margins(7)):
        formula = paired_formula(n, t, s).to_dict()
        if row != formula:
            raise ValueError(f"Independent labeled row count fails at n={n}")
        if n == 0:
            if row != {(0, 0): 1}:
                raise ValueError("Empty row")
            continue
        if n <= 5:
            f = shifted(row, 0)
            left, _, right = signs_at_endpoints(f)
            line = sum(v * (t+s)**i * (t-s)**j for (i, j), v in row.items())
            disc = line.discriminant(0).to_dict()
            if any(i or j % 2 for i, j in disc):
                raise ValueError("Expected a discriminant polynomial in s squared")
            D = fmpz_poly([disc.get((0, 2*j), 0) for j in range(n*(n-1)//2+1)])
            _, at_zero, at_infinity = signs_at_endpoints(D)
            if left-right != n or D[0] <= 0 or (at_zero, at_infinity) != prefix[n-1]:
                raise ValueError(f"Positive-parameter certificate fails at size {n}")
            print(f"n={n}: {n} roots at shift zero, discriminant variations {at_zero},{at_infinity}")
        else:
            shift = {6: 16, 7: 20}[n]
            f = shifted(row, shift)
            left, _, right = signs_at_endpoints(f)
            if f.degree() != n or f.discriminant() >= 0 or left-right != n-2:
                raise ValueError(f"Obstruction fails at size {n}")
            print(f"n={n}, shift={shift}: {left-right} real roots, negative discriminant")
    for n, x, expected in [(8, -48, -577709571071), (9, -55, 391474884215196)]:
        value = sum(comb(n, i)**2 * x**i for i in range(n+1))
        if value != expected or (-1)**n * value >= 0:
            raise ValueError(f"Legendre endpoint sign fails at size {n}")
        print(f"S_{n}({x}) = {value}")


if __name__ == "__main__":
    main()
