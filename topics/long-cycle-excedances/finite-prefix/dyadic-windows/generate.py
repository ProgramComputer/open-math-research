"""Generate strict dyadic windows in the original reduced polynomial variable."""
import argparse
import gzip
import hashlib
import json
from fractions import Fraction
from math import comb
from pathlib import Path

from flint import fmpz_poly


def insertion_rows(cutoff, upper):
    t = fmpz_poly([0, 1])
    euler = [fmpz_poly([1])]
    for size in range(1, upper):
        prev = euler[-1]
        euler.append(fmpz_poly([
            (j+1)*prev[j] + ((size-j)*prev[j-1] if j else 0)
            for j in range(size)
        ]))
    # Below the cutoff use the single-cycle Eulerian rows only to initialize
    # the bracket search. The first true row is at size cutoff.
    rows = {size: euler[size-1] for size in range(3, cutoff+1)}
    for n in range(cutoff, upper):
        prev = rows[n]
        row = fmpz_poly([
            (j+1)*prev[j] + ((n-j)*prev[j-1] if j else 0)
            for j in range(n)
        ])
        lag = n+1-cutoff
        if lag >= cutoff:
            row += comb(n, cutoff-1)*t*euler[cutoff-1]*rows[lag]
        rows[n+1] = row
    return rows


def exact_sign(coeffs, point):
    """Sign at -point by homogeneous Horner over the integers."""
    exponent = point.denominator.bit_length()-1
    if point.denominator != 1 << exponent:
        raise ValueError('expected a dyadic point')
    value = coeffs[-1]
    for power, coefficient in enumerate(reversed(coeffs[:-1]), 1):
        value = (coefficient << (power*exponent))-value*point.numerator
    return (value > 0)-(value < 0)


def certified_sign(coeffs, point, desired):
    """Bound the scaled Horner value from the side that certifies its sign."""
    exponent = point.denominator.bit_length()-1
    value = 0
    for j in reversed(range(len(coeffs))):
        product = -point.numerator*value
        upper = (desired < 0) ^ bool(j % 2)
        rounded = -((-product) >> exponent) if upper else product >> exponent
        value = (coeffs[j] << 256)+rounded
    return value*desired > 0


def inward(point, bits, lower):
    shift = point.denominator.bit_length()-1
    leading = max(0, shift+1-point.numerator.bit_length())
    scale = 1 << min(shift, bits+leading)
    scaled = point.numerator*scale
    mantissa = -((-scaled)//point.denominator) if lower else scaled//point.denominator
    return Fraction(mantissa, scale)


def shorten(P, Q, lower, upper, sign):
    for bits in (6, 10, 16, 24, 40, 64, 128, 256, 512, 1024):
        left = inward(lower, bits, True)
        right = inward(upper, bits, False)
        if (lower <= left < right <= upper and certified_sign(P, left, sign)
                and certified_sign(P, right, -sign) and certified_sign(Q, left, -sign)
                and certified_sign(Q, right, -sign)):
            return left, right
    raise ArithmeticError('no strict dyadic certificate at the chosen precision')


def refine(P, Q, left, right, sign, n):
    for _ in range(3*n+40):
        if (0 < left < right < 1 and exact_sign(Q, left) == -sign
                and exact_sign(Q, right) == -sign):
            if exact_sign(P, left) == sign and exact_sign(P, right) == -sign:
                return left, right
        center = (left+right)/2
        at_center = exact_sign(P, center)
        if at_center == sign:
            left = center
        elif at_center == -sign:
            right = center
        else:
            left, right = (left+center)/2, (center+right)/2
    raise ArithmeticError(('refinement limit', n))


def generate(cutoff, first, last, out):
    if not 3 <= cutoff <= first <= last:
        raise ValueError('require 3 <= cutoff <= first <= last')
    rows = insertion_rows(cutoff, last+1)
    digest = hashlib.sha256()
    brackets = []
    count = 0
    for n in range(3, last+1):
        P, Q = list(rows[n]), list(rows[n+1])
        if len(brackets) != (n-2)//2 or len(P) != n-1 or P[::-1] != P or P[0] != 1:
            raise ArithmeticError(('degree or reciprocity', n))
        successor = []
        previous = Fraction(0)
        for i, (left, right) in enumerate(brackets):
            sign = (-1)**i
            left, right = refine(P, Q, left, right, sign, n)
            if not previous < left:
                raise ArithmeticError(('unordered brackets', n, i))
            successor.append((previous, left))
            previous = right
            if n >= first:
                a, b = shorten(P, Q, left, right, sign)
                record = [n, i, a.numerator, a.denominator.bit_length()-1,
                          b.numerator, b.denominator.bit_length()-1]
                data = (json.dumps(record, separators=(',', ':'))+'\n').encode('ascii')
                out.write(data)
                digest.update(data)
                count += 1
        if n % 2:
            desired = (-1)**(len(brackets)+1)
            if exact_sign(Q, Fraction(1)) != desired or not certified_sign(Q, Fraction(1), desired):
                raise ArithmeticError(('central sign', n))
            successor.append((previous, Fraction(1)))
        brackets = successor
    return dict(pairs=last-first+1, windows=count, uncompressed_sha256=digest.hexdigest())


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', type=Path)
    parser.add_argument('k', type=int)
    parser.add_argument('lower', type=int)
    parser.add_argument('upper', type=int)
    args = parser.parse_args()
    with args.certificate.open('wb') as raw:
        with gzip.GzipFile(filename='', fileobj=raw, mode='wb', mtime=0) as compressed:
            print(json.dumps(generate(args.k,args.lower,args.upper,compressed),sort_keys=True))
