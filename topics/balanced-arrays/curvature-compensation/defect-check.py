"""Replay small counts against direct enumeration, and optionally check roots."""
import argparse
from itertools import combinations, product
import json
from pathlib import Path
from runpy import run_path
import sys

HERE = Path(__file__).resolve().parent
coefficient = run_path(str(HERE / 'defect-histogram.py'))['coefficient']


def check_small():
    tested = 0
    for n in range(1, 6):
        for d in range(1, 5):
            for k in range(n + 1):
                all_choices = list(combinations(range(n), k))
                counts = [0]*(d+1)
                for columns in product(all_choices, repeat=d):
                    occupancies = [0]*n
                    for rows in columns:
                        for i in rows:
                            occupancies[i] += 1
                    counts[max(occupancies)] += 1
                target = 0
                for r, increment in enumerate(counts):
                    target += increment
                    lower, upper, _ = coefficient(n,d,r,k)
                    assert (lower,upper) == (target,target)
                    for order in range(1,4):
                        lower,upper,_ = coefficient(n,d,r,k,order)
                        assert lower <= target <= upper
                    tested += 1
    print(f'Exact direct enumeration and truncated bounds checked at {tested} small inputs.')


def check_roots(files, shared):
    sys.path.insert(0, str(shared))
    from roots import root_report
    for f in files:
        rows = [json.loads(line) for line in f.read_text().splitlines()]
        d, r, n = (rows[0][x] for x in ('d','r','n'))
        assert len(rows) == n*r//d + 1
        assert all((row['n'],row['d'],row['r'],row['k']) == (n,d,r,k)
                   and row['lower'] == row['upper'] > 0
                   for k,row in enumerate(rows))
        report = root_report([row['lower'] for row in rows])
        assert report['distinct_real_roots'] == len(rows)-1
        print(f.name, round(sum(row['seconds'] for row in rows),3), report)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--shared', type=Path, help='path to shared/python with roots.py')
    parser.add_argument('files', nargs='*', type=Path)
    args = parser.parse_args()
    check_small()
    if args.files:
        if args.shared is None:
            parser.error('--shared is required for root checks')
        check_roots(args.files, args.shared)
