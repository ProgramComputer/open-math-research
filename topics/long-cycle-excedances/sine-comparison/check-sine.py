"""Rigorous point enclosures for the derivative-free adjacent-row comparison."""
from argparse import ArgumentParser
from fractions import Fraction
from itertools import permutations
import json
from math import factorial

import flint
from flint import arb, acb, arb_series, ctx


def literal(n, k):
    counts = [0] * (n + 1)
    for sigma in permutations(range(n)):
        seen = set()
        for i in range(n):
            if i in seen:
                continue
            j, length = i, 0
            while j not in seen:
                seen.add(j)
                j, length = sigma[j], length + 1
            if length < k:
                break
        else:
            counts[sum(i < j for i, j in enumerate(sigma))] += 1
    return counts


def normalized(n, k, sine):
    ctx.cap = n + 2
    s = arb(sine.numerator) / sine.denominator
    c = (1 - s*s).sqrt()
    r = arb.pi()/s
    t = -(-r*c).exp()
    free = (1-t) / (1-t*arb_series([0, r]).exp())
    short = arb_series(free, prec=k).log()
    row = free * arb_series([-short[j] for j in range(k)]).exp()
    w = acb(c, s)
    value = k/s*((w**(n+1)).imag*row[n] - (w**n).imag*row[n+1])
    return value, row, r, t


def literal_check():
    cases = 0
    sine = Fraction(5, 13)
    for n in range(2, 8):
        for k in range(2, n+1):
            _, row, r, t = normalized(n, k, sine)
            for m in (n, n+1):
                ev = sum(v*t**i for i, v in enumerate(literal(m,k)))
                expected = (r/(1-t))**m * ev/factorial(m)
                assert expected.overlaps(row[m]) and (expected-row[m]).abs_upper() < arb(2)**-200
            cases += 1
    return cases


def main():
    parser = ArgumentParser()
    parser.add_argument('--output', required=True)
    opts = parser.parse_args()
    ctx.prec = 384
    checks = []
    oracle = literal_check()
    for cycles in (5,11,20,32,48):
        k = (10002 + cycles - 1)//cycles
        for offset in (-2,-1,0):
            n = cycles*k + offset
            for sine in (Fraction(11,1000),Fraction(3,100)):
                assert n >= 10000 and 4*k <= n <= 48*k
                assert n*sine*sine >= Fraction(6,5)
                z, _, _, _ = normalized(n,k,sine)
                result = 'positive' if z > 0 else 'negative' if z < 0 else 'inconclusive'
                checks.append(dict(n=n,k=k,sine=str(sine),bits=ctx.prec,
                                   scaled_difference=z.str(28),outcome=result))
                print(n,k,str(sine),result,z.str(14),flush=True)
    with open(opts.output, 'w') as out:
        json.dump(dict(flint=flint.__version__,literal_pairs=oracle,points=checks),out,indent=2)
        out.write('\n')


if __name__ == '__main__':
    main()
