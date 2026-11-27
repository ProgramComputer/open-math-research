"""Verify likelihood-ratio minors and log-concavity from integer counts."""
import argparse
import gzip
import io
import json
from collections import Counter
from math import comb
from pathlib import Path


def by_first_block(nmax, j, weight):
    rows = [[1]]
    for n in range(1, nmax+1):
        row = [0] * (n//j+1)
        for s in range(1, n+1):
            ways = weight * comb(n, s)
            for k, a in enumerate(rows[n-s]):
                row[k+(s>=j)] += ways*a
        rows.append(row)
    return rows


def ordered_sizes(n):
    """Insert the largest label into a block or into a fresh singleton slot."""
    if n == 0:
        yield ()
        return
    for sizes in ordered_sizes(n-1):
        for i, size in enumerate(sizes):
            yield sizes[:i]+(size+1,)+sizes[i+1:]
        for i in range(len(sizes)+1):
            yield sizes[:i]+(1,)+sizes[i:]


def check(nmax, ledger):
    passed = Counter()
    oracle = [Counter(ordered_sizes(n)) for n in range(9)]
    for j in range(2, 21):
        for u in (1, 2, 4):
            rows = by_first_block(nmax, j, u)
            for n, row in enumerate(rows):
                if ledger:
                    ledger.write(json.dumps({'j':j,'u':u,'n':n,'coefficients':row})+'\n')
                if n < len(oracle):
                    direct = [0]*len(row)
                    for sizes, multiplicity in oracle[n].items():
                        direct[sum(s >= j for s in sizes)] += multiplicity * u**len(sizes)
                    assert row == direct
                    passed['literal rows'] += 1
                passed['rows'] += 1
                for k in range(1, len(row)-1):
                    assert row[k]**2 > row[k-1]*row[k+1]
                    passed['strict row log-concavity'] += 1
                    assert k*(n-k*j)*row[k]**2 > (k+1)*(n-(k-1)*j)*row[k-1]*row[k+1]
                    passed['fractional Newton'] += 1
                if n == nmax:
                    continue
                nextrow=rows[n+1]
                for k in range(len(nextrow)-1):
                    old_next = row[k+1] if k+1 < len(row) else 0
                    assert nextrow[k+1]*row[k] > old_next*nextrow[k]
                    passed['strict adjacent likelihood'] += 1
                    if n>k*j and old_next:
                        assert (n-k*j)*nextrow[k+1]*row[k] >= (n+1-k*j)*old_next*nextrow[k]
                        passed['normalized ratio growth'] += 1
                for m in range(n, min(n+j,nmax)+1):
                    later=rows[m]
                    # later is LR-smaller than the old row shifted right by one.
                    for k in range(1,len(later)-1):
                        assert later[k]*row[k] >= later[k+1]*row[k-1]
                        passed['upper shifted likelihood'] += 1
                        assert k*later[k]*row[k] > (k+1)*later[k+1]*row[k-1]
                        passed['derivative likelihood'] += 1
                if n:
                    for k in range(1,len(rows[n-1])):
                        assert (n+1)*row[k]**2 >= n*rows[n-1][k]*nextrow[k]
                        passed['normalized column log-concavity'] += 1
    return dict(sorted(passed.items()))


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ledger', type=Path, help='write gzip JSON lines for every row')
    args=parser.parse_args()
    if args.ledger:
        with args.ledger.open('wb') as raw:
            with gzip.GzipFile(filename='', fileobj=raw, mode='wb', mtime=0) as compressed:
                with io.TextIOWrapper(compressed, encoding='utf8') as ledger:
                    counts=check(80,ledger)
    else:
        counts=check(80,None)
    print(json.dumps({'n':[0,80],'j':[2,20],'u':[1,2,4],'passed':counts}, indent=2))
