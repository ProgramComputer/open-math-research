#!/usr/bin/env python3
"""Check the finite lower hyper-Bessel sign range with outward-rounded integers."""
import argparse
import hashlib
from functools import lru_cache
import json
from pathlib import Path


def up(a, b):
    return -(-a // b)


def atan_inverse(scale, n):
    lower = upper = 0
    power = n
    j = 0
    while True:
        divisor = (2*j + 1)*power
        if scale < divisor:
            return lower-1, upper+1
        lo, hi = scale//divisor, up(scale, divisor)
        if j % 2:
            lower -= hi
            upper -= lo
        else:
            lower += lo
            upper += hi
        j += 1
        power *= n*n


@lru_cache(None)
def pi_interval(scale):
    a,b = atan_inverse(scale,5)
    c,d = atan_inverse(scale,239)
    return 16*a-4*d, 16*b-4*c


@lru_cache(None)
def radial_factor(d, scale):
    p,q = pi_interval(scale)
    x,y = p//d,up(q,d)
    lo = hi = x
    lower = upper = 0
    j = 0
    while hi > 2:
        if j % 2:
            lower -= hi
            upper -= lo
        else:
            lower += lo
            upper += hi
        denom = scale**2*(2*j+2)*(2*j+3)
        lo,hi = lo*x*x//denom,up(hi*x*x,denom)
        j += 1
    # The sine series at x/scale has decreasing terms. Sine is 1-Lipschitz.
    error = hi + y-x
    s_lo,s_hi = lower-error,upper+error
    assert s_lo > 0
    return x*scale//s_hi, up(y*scale,s_lo)


@lru_cache(65536)
def power(m, d):
    return m**d


def positive_partial_sum(d, k, bits):
    scale = 1 << bits
    a,b = radial_factor(d,scale)
    factor = 2*d*k+d-1
    u = a*factor//(2*d)
    v = up(b*factor,2*d)
    assert u >= k*scale
    shift = bits*(d-1)
    zlo = (u**d) >> shift
    zhi = up(v**d, 1 << shift)
    assert zlo > 0
    left_lo = left_hi = right_lo = right_hi = scale
    signed_lower = scale
    for j in range(1, max(257, 12*k//d+257)):
        if j <= k:
            num = power(k-j+1,d) << bits
            left_lo = left_lo*num//zhi
            left_hi = up(left_hi*num,zlo)
        else:
            left_lo = left_hi = 0
        den = power(k+j,d) << bits
        right_lo = right_lo*zlo//den
        right_hi = up(right_hi*zhi,den)
        if j % 2:
            signed_lower -= left_hi + right_hi
            if v <= (k+j+1)*scale:
                if signed_lower > 0:
                    return j, signed_lower
                if left_hi <= 2 and right_hi <= 2:
                    return None
        else:
            signed_lower += left_lo + right_lo
    return None


def run(path, selected=None):
    digest = hashlib.sha256()
    cases = 0
    greatest_j = greatest_bits = 0
    with path.open('wb') as out:
        for d in selected or range(3,128):
            cutoff = 100*d if d <= 7 else 128
            for k in range(d//4+1,cutoff):
                for bits in [96,192,384,768,1536,3072]:
                    proof = positive_partial_sum(d,k,bits)
                    if proof:
                        break
                else:
                    raise ArithmeticError(f'Unsettled pair {(d,k)}')
                j, bound = proof
                # The normalized signed value is at least 2**exponent.
                exponent = bound.bit_length()-1-bits
                row = json.dumps([d,k,bits,j,exponent],separators=(',',':')).encode() + b'\n'
                out.write(row)
                digest.update(row)
                greatest_j = max(greatest_j,j)
                greatest_bits = max(greatest_bits,bits)
                cases += 1
    print(f'{cases} positive strict signs; maximum precision {greatest_bits} bits; longest truncation {greatest_j}; SHA-256 {digest.hexdigest()}')


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('ledger',type=Path)
    parser.add_argument('--dimension', type=int, choices=range(3,128))
    args=parser.parse_args()
    run(args.ledger,[args.dimension] if args.dimension else None)
