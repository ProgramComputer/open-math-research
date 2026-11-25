"""Recompute the original rank-two evidence by two counts and exact Sturm sequences."""

import json
import sys
from pathlib import Path

topic = Path(__file__).resolve().parent
sys.path.extend((str(topic / 'code'), str(topic.parents[1] / 'shared' / 'python')))

from coefficients import column_count
from rank_two_counts import rank_two
from roots import root_report


def verify(archive):
    expected = {(n, d) for n in range(41) for d in range(4, 13)}
    checked = 0
    for line in archive:
        row = json.loads(line)
        n, d = row['n'], row['d']
        if (n, d) not in expected or row['r'] != 2:
            raise ValueError(f'Unexpected or duplicate triple {(n, 2, d)}')
        expected.remove((n, d))
        degree = 2*n // d
        by_matching = [rank_two(n, k, d) for k in range(degree + 1)]
        by_columns = [column_count(n, k, 2, d) for k in range(degree + 1)]
        if by_matching != by_columns or by_columns != row['coefficients']:
            raise ArithmeticError(f'Counts disagree at {(n, 2, d)}')
        certificate = root_report(by_matching)
        if certificate != row['root_report'] or not certificate['real_rooted']:
            raise ArithmeticError(f'Exact root check failed at {(n, 2, d)}')
        checked += 1
    if expected:
        raise ValueError(f'Archive missing {len(expected)} triples')
    print(f'Verified {checked} complete rows using matchings, column capacities and exact Sturm counts.')


if __name__ == '__main__':
    with (topic / 'results' / 'source_range.jsonl').open() as rows:
        verify(rows)
