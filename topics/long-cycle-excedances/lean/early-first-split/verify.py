"""Check the 47 first-split gamma certificates over the integers."""
import argparse
import gzip
import hashlib
import json
from fractions import Fraction
from math import comb
from pathlib import Path


def eulerian_rows(last):
    rows = [[1]]
    for n in range(1, last+1):
        prev = rows[-1] + [0]
        rows.append([(j+1)*prev[j] + (n-j)*(prev[j-1] if j else 0) for j in range(n)])
    return rows


def gamma_expansion(gamma, degree):
    if len(gamma) != degree//2+1 or gamma[-1] <= 0:
        raise ValueError(('shape', degree))
    coeffs = [0]*(degree+1)
    for j, value in enumerate(gamma):
        for h in range(degree-2*j+1):
            coeffs[h+j] += value*comb(degree-2*j, h)
    return coeffs


def dyadic(pair):
    a, e = pair
    if type(a) is not int or type(e) is not int or e<0:
        raise ValueError(('dyadic', pair))
    return Fraction(a, 1 << e)


def check_sign(coeffs, point, sign):
    # Homogenized evaluation, independent of directed rounding.
    num, den = point.as_integer_ratio()
    value, scale = coeffs[-1], 1
    for c in reversed(coeffs[:-1]):
        scale *= den
        value = num*value + c*scale
    if sign*value <= 0:
        raise ValueError(('wrong sign', point, sign))


def check(path):
    get_stream = gzip.open if path.suffix=='.gz' else open
    digest = hashlib.sha256()
    windows = signs = 0
    euler = eulerian_rows(107)
    with get_stream(path, 'rb') as source:
        for k in range(8,55):
            line = next(source)
            digest.update(line)
            data = json.loads(line)
            d = k-2
            if data['k'] != k or len(data['windows']) != d:
                raise ValueError(('missing case or window', k))
            p, q = data['p'], data['q']
            old, new = euler[2*k-2], euler[2*k-1].copy()
            # At 2k the cycle of label 1 either contains every label,
            # or it uses k-1 of the other labels and leaves a k-cycle.
            count = comb(2*k-1,k-1)
            for i,a in enumerate(euler[k-1]):
                for j,b in enumerate(euler[k-1]):
                    new[1+i+j] += count*a*b
            if gamma_expansion(p,2*k-3) != old or gamma_expansion(q,2*k-2) != new:
                raise ValueError(('original rows', k))
            prev = dyadic(data['outer'])
            check_sign(q,prev,(-1)**(d+1))
            check_sign(q,Fraction(0),1)
            for i,(left,right) in enumerate(data['windows']):
                l, r = dyadic(left), dyadic(right)
                if not prev < l < r < 0:
                    raise ValueError(('order', k, i))
                s = (-1)**(d-i)
                check_sign(p,l,s)
                check_sign(p,r,-s)
                check_sign(q,l,s)
                check_sign(q,r,s)
                prev = r
            signs += 4*d+2
            windows += d
        if next(source,None) is not None:
            raise ValueError('extra cases')
    return dict(cutoffs=[8,54], pairs=47, windows=windows, signs=signs,
                sha256=digest.hexdigest())


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', type=Path)
    print(json.dumps(check(parser.parse_args().certificate), sort_keys=True))
