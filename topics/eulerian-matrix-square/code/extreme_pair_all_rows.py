"""Verify the finite prefix and rational tail bounds for the two extreme roots."""

import argparse
import json
from fractions import Fraction
from math import comb
from pathlib import Path

from flint import fmpq_poly, fmpz_poly


def descent_row(n):
    # The explicit alternating coefficient formula, in ascending descent order.
    return fmpz_poly([sum((-1)**j * comb(n+1, j) * (k+1-j)**n for j in range(k+1))
                      for k in range(n)])


def strict_interlacing(left, right):
    """Positive signed Sturm chain, in descending degree, for consecutive monic rows."""
    a, b = right, left
    degrees = []
    if a.degree() != b.degree()+1 or b.degree() < 0:
        raise ValueError('Expected consecutive degrees')
    while b:
        if b.degree() != a.degree()-1 or min(a.leading_coefficient(), b.leading_coefficient()) <= 0:
            raise ArithmeticError('Strict interlacing certificate failed')
        degrees.append(b.degree())
        rem = -(fmpq_poly(a) % fmpq_poly(b)).numer()
        a, b = b, rem // rem.content() if rem else rem
    if a.degree() != 0:
        raise ArithmeticError('Nonconstant common factor')
    return degrees


def records():
    eulerian = [None] + [descent_row(n) for n in range(1, 41)]
    rows = [sum((outer[k-1]*eulerian[k] for k in range(1, n+1)), fmpz_poly([]))
            for n, outer in enumerate(eulerian) if n]
    return [dict(n=n, coefficients=list(map(int, rows[n-1])),
                 next_coefficients=list(map(int, rows[n])),
                 positive_remainder_chain_degrees=strict_interlacing(rows[n-1], rows[n]))
            for n in range(1, 40)]


def tail_bound(n):
    t = 64*Fraction(3,4)**n / (1 - 8*Fraction(2,3)**n)
    return Fraction(16*(n+1)+32*(3*n+1), 2**n) + 18*t + t*t


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('archive', type=Path)
    parser.add_argument('--replay', action='store_true')
    args = parser.parse_args()
    if not 0 < tail_bound(40) < Fraction(1,32):
        raise ArithmeticError('Uniform remainder bound failed')
    probes = [Fraction(1,2),Fraction(3,4),Fraction(13,4),Fraction(7,2)]
    if [1-2*t+t*t/2 for t in probes] != [Fraction(1,8),Fraction(-7,32),Fraction(-7,32),Fraction(1,8)]:
        raise ArithmeticError('Incorrect limiting signs')
    items = records()
    if len(items) != 39:
        raise ArithmeticError('Incomplete finite prefix')
    data = ''.join(json.dumps(item, separators=(',', ':'))+'\n' for item in items)
    if args.replay:
        if args.archive.read_text() != data:
            raise ArithmeticError('Recorded finite certificates disagree')
    else:
        args.archive.write_text(data)
    print('39 consecutive pairs strictly interlace, and the n>=40 tail bound is below 1/32.')


if __name__ == '__main__':
    main()
