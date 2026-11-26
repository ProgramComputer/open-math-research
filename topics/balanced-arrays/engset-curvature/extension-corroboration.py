"""High-precision exact screens for extension concavity, using local files."""
import argparse
from collections import Counter
import gzip
import json
from math import comb
from pathlib import Path

from flint import fmpz


def signs(a, d, bits):
    scale = 2**bits
    u = [int(fmpz(y*((i+1)*scale)**d//x).root(d))
         for i,(x,y) in enumerate(zip(a, a[1:]))]
    for k in range(1,len(u)-1):
        margin = 2*u[k]-u[k-1]-u[k+1]
        yield k, (1 if margin>2 else -1 if margin<-2 else 0)


def data_from_files(base):
    names = ('results/corank-one.jsonl.gz', 'results/source_range.jsonl',
             'results/degree_reduction.jsonl',
             'results/column-extension-corank-two.jsonl.gz',
             'results/column-extension-cap-two.jsonl.gz',
             'finite-residual/records.jsonl.gz')
    rows = {}
    for name in names:
        file = base/name
        if not file.is_file():
            print(f'Missing: {name}', flush=True)
            continue
        data = file.read_bytes()
        if name.endswith('.gz'):
            data = gzip.decompress(data)
        for rec in map(json.loads,data.splitlines()):
            for field,offset in [('coefficients',0),('left',0),('right',1)]:
                if field in rec:
                    key = rec['n'], rec['r'], rec['d']+offset
                    a = tuple(map(int,rec[field]))
                    if key in rows:
                        assert a==rows[key]
                    rows[key] = a
    yield from sorted(rows.items())


def corank_one(n,d):
    """Exclude rows common to all d k-subsets, by inclusion–exclusion."""
    a = []
    for k in range(n*(d-1)//d+1):
        term = comb(n,k)**d
        total = term
        for i in range(k):
            numerator = term*(k-i)**d
            denominator = (i+1)*(n-i)**(d-1)
            term, remainder = divmod(numerator, denominator)
            assert not remainder
            total += (-1 if i%2==0 else 1)*term
        a.append(total)
    return a


def corank_range(max_n, max_d):
    for n in range(4,max_n+1):
        for d in range(3,max_d+1):
            yield (n,d-1,d), corank_one(n,d)


def check(records,bits):
    output = Counter()
    vectors = 0
    for (n,r,d), a in records:
        if r==d:
            continue
        vectors += 1
        for k, sign in signs(a,d,bits):
            output[sign] += 1
            if sign!=1:
                print(n,r,d,k,sign,flush=True)
    print(vectors,dict(output),flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive',type=Path)
    parser.add_argument('--max-n',type=int,default=90)
    parser.add_argument('--max-d',type=int,default=24)
    parser.add_argument('--bits',type=int,default=192)
    args=parser.parse_args()
    records = data_from_files(args.archive) if args.archive else corank_range(args.max_n,args.max_d)
    check(records,args.bits)
