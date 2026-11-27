"""Export the points certified by an identified intermediate cross-check source."""
import argparse
import sys
from hashlib import sha256
from pathlib import Path


def parts(point):
    if not point.is_exact():
        raise ValueError("Non-dyadic interval endpoint")
    numerator, exp = map(int, point.man_exp())
    if numerator <= 0:
        raise ValueError("Endpoint must be positive")
    if exp >= 0:
        return numerator << exp, 0
    bits = -exp
    while bits and numerator % 2 == 0:
        bits -= 1
        numerator //= 2
    return numerator, bits


def export(source, dest, nmin, nmax, kmin, kmax):
    # Leave all upstream arithmetic and acceptance checks in their original form.
    raw = source.read_bytes()
    if sha256(raw).hexdigest() != "d0e7dbb6a18e5c6734fda1e1cde61f56c609e1cf87a509cab7824f0b431ffdd0":
        raise ValueError("Unexpected upstream source SHA-256")
    text = raw.decode("utf-8")
    old = 'def pair(n,k,f,g):'
    locus = '        gap += 1\n'
    if text.count(old) != 1 or text.count(locus) != 1:
        raise ValueError("Unexpected upstream source")
    text = text.replace(
        locus, '        emit(n, k, gap, left, right)\n' + locus
    )
    def emit(n, k, gap, left, right):
        values = n, k, gap, *parts(left), *parts(right)
        dest.write(','.join(map(str, values)) + '\n')
    env = {'__name__': 'ledger_upstream', 'emit': emit, 'print': lambda *a, **kw: print(*a, file=sys.stderr, **kw)}
    exec(compile(text, str(source), 'exec'), env)
    env['main'](nmin, nmax, kmin, kmax)


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('source', type=Path)
    ap.add_argument('--nmin', type=int, default=251)
    ap.add_argument('--nmax', type=int, default=1000)
    ap.add_argument('--kmin', type=int, default=7)
    ap.add_argument('--kmax', type=int, default=250)
    a = ap.parse_args()
    if not __debug__:
        raise SystemExit('Use Python with assertions enabled.')
    export(a.source, sys.stdout, a.nmin, a.nmax, a.kmin, a.kmax)
