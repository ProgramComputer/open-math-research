"""Replay the finite part of ordered threshold three using only Python 3.10+."""
import argparse
import gzip
import json
from math import comb, factorial, gcd
from pathlib import Path

ARCHIVE = Path(__file__).resolve().parents[1] / 'results' / 'threshold-three.json.gz'


def count_rows(limit):
    """Choose all nonsmall labels, partition them, and insert singleton/doubleton gaps."""
    assoc = [[0] * (limit//3 + 1) for _ in range(limit + 1)]
    assoc[0][0] = 1
    for s in range(3, limit+1):
        for k in range(1, s//3 + 1):
            assoc[s][k] = sum(comb(s-1, b-1) * assoc[s-b][k-1]
                              for b in range(3, s-3*(k-1)+1))
    for n in range(limit+1):
        row = []
        for k in range(n//3+1):
            count = 0
            for s in range(3*k, n+1):
                if assoc[s][k] == 0:
                    continue
                small = n-s
                # With b doubletons, the small labels form small-b unordered blocks.
                completions = sum(factorial(small) * factorial(k+small-b)
                                  // (factorial(small-2*b)*factorial(b)*2**b)
                                  for b in range(small//2+1))
                count += comb(n, s)*assoc[s][k]*completions
            row.append(count)
        yield row


def primitive(a):
    while a and a[-1] == 0:
        a.pop()
    content = gcd(*a)
    return [c//content for c in a] if content else []


def negative_remainder(a, b):
    """Positive integer pseudo-division followed by primitive normalization."""
    a = list(a)
    leading = b[-1]
    while len(a) >= len(b):
        scale = abs(leading)
        factor = a[-1] if leading > 0 else -a[-1]
        common = gcd(scale, factor)
        scale, factor = scale//common, factor//common
        a = [c*scale for c in a]
        offset = len(a) - len(b)
        for k, c in enumerate(b):
            a[k+offset] -= factor*c
        a = primitive(a)
    return [-c for c in a]


def signed_degrees(a, b):
    steps = []
    while a:
        steps.append((len(a)-1, 1 if a[-1] > 0 else -1))
        if not b:
            break
        a, b = b, negative_remainder(a, b)
    return steps


def vectors(limit):
    old = None
    for n, a in enumerate(count_rows(limit)):
        if len(a) != n//3 + 1 or min(a) <= 0:
            raise ArithmeticError(f'Incorrect support at n={n}')
        sturm = signed_degrees(a, [k*c for k,c in enumerate(a) if k])
        expected = list(range(n//3, -1, -1))
        if sturm != [(d, 1) for d in expected]:
            raise ArithmeticError(f'Standard Sturm chain failed at n={n}')
        consecutive = None
        if old is not None:
            reduced = old
            if len(old) == len(a):
                reduced = [-c for c in negative_remainder(old, a)]
            consecutive = signed_degrees(a, reduced)
            if consecutive != [(d, 1) for d in expected]:
                raise ArithmeticError(f'Consecutive strict remainder chain failed at n={n}')
        yield dict(n=n, j=3, coefficients=a, sturm=sturm, consecutive_chain=consecutive)
        old = a


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true', help='regenerate the finite archive')
    args = parser.parse_args()
    # The independent archive overlaps the analytical proof by two rows.
    records = list(vectors(96))
    payload = json.dumps(records, separators=(',', ':')).encode()
    if args.write:
        ARCHIVE.write_bytes(gzip.compress(payload, compresslevel=9, mtime=0))
    elif gzip.decompress(ARCHIVE.read_bytes()) != payload:
        raise ValueError('Finite archive mismatch')
    print('97 coefficient vectors, 97 simple negative-root counts, 96 strict interlacings.')


if __name__ == '__main__':
    main()
