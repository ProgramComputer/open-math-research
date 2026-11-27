"""Verify every compact raw-variable bracket against independently counted coefficients."""
import argparse
import gzip
import hashlib
import json
from math import comb
from pathlib import Path

from flint import fmpq, fmpq_poly, fmpz_poly


def rows(cutoff, upper):
    # A distinguished cycle of length ell containing 1 contributes an
    # Eulerian polynomial A_(ell-1) and, if vertices remain, one extra t.
    euler = [fmpz_poly([1])]
    t = fmpz_poly([0, 1])
    for m in range(1, upper):
        previous = euler[-1]
        euler.append((1 + (m-1)*t)*previous + t*(1-t)*previous.derivative())
    table = {}
    for size in range(cutoff, upper+1):
        row = euler[size-1]
        for ell in range(cutoff, size-cutoff+1):
            row += comb(size-1, ell-1)*t*euler[ell-1]*table[size-ell]
        table[size] = row
    return table


def check(certificate, cutoff, first, last):
    if not 2 <= cutoff <= first <= last:
        raise ValueError("invalid size bounds")
    table = rows(cutoff, last+1)
    digest = hashlib.sha256()
    signs = brackets = 0
    with gzip.open(certificate, 'rb') as source:
        for n in range(first, last+1):
            P, Q = [fmpq_poly(table[i]) for i in (n,n+1)]
            for size, poly in [(n, P), (n+1, Q)]:
                coefficients = poly.coeffs()
                if poly.degree() != size-2 or coefficients[0] != 1 or coefficients != coefficients[::-1]:
                    raise ValueError(('shape',cutoff,size))
            left = fmpq(0)
            degree = n-2
            for i in range(degree//2):
                raw = next(source)
                digest.update(raw)
                rn, ri, a, e, b, f = json.loads(raw)
                if (rn, ri) != (n, i) or min(a, b, e, f) < 0:
                    raise ValueError(('indices',n,i))
                lower, upper = fmpq(a, 1 << e), fmpq(b, 1 << f)
                if not left < lower < upper < 1:
                    raise ValueError(('order',n,i))
                sign = (-1)**i
                for polynomial, point, expected in (
                    (P, lower, sign), (P, upper, -sign),
                    (Q, lower, -sign), (Q, upper, -sign),
                ):
                    if polynomial(-point)*expected <= 0:
                        raise ValueError(('invalid endpoint',n,i,point))
                left = upper
                brackets += 1
                signs += 4
            if degree%2:
                if (-1)**(degree//2+1)*Q(-1)<=0:
                    raise ValueError(('center',n))
                signs += 1
        if next(source,None) is not None:
            raise ValueError('trailing certificate records')
    return dict(cutoff=cutoff, lower_size=first, upper_size=last,
                pairs=last-first+1,windows=brackets,strict_signs=signs,
                uncompressed_sha256=digest.hexdigest())


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', type=Path)
    parser.add_argument('k', type=int)
    parser.add_argument('lower', type=int)
    parser.add_argument('upper', type=int)
    a = parser.parse_args()
    print(json.dumps(check(a.certificate, a.k, a.lower, a.upper), sort_keys=True))
