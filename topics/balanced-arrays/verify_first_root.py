"""Exact checks for balanced-array roots closest to zero. Python 3.10+."""
import argparse
import json
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path

HERE = Path(__file__).resolve().parent


def direct_count(n, d, r, k):
    columns = list(combinations(range(n), k))
    return sum(all(sum(i in c for c in matrix) <= r for i in range(n))
               for matrix in product(columns, repeat=d))


def check_exceptions():
    expected = {(3, 2): (6, 24, 6), (3, 3): (8, 27, 27),
                (4, 3): (14, 78, 36), (4, 4): (16, 81, 81)}
    rows = []
    for d in (3, 4):
        for r in range(1, d + 1):
            a2 = direct_count(3, d, r, 2)
            if a2:
                counts = direct_count(2, d, r, 1), direct_count(3, d, r, 1), a2
                if counts != expected[d, r] or counts[0] * counts[1] < 3 * counts[2]:
                    raise ValueError((d, r, counts))
                rows.append([d, r, *counts])
    if len(rows) != len(expected):
        raise ValueError('Missing boundary case')
    return rows


def read_vectors(directory):
    found = {}

    def add(row):
        if 'coefficients' in row:
            key = row['n'], row['r'], row['d']
            a = tuple(row['coefficients'])
            if found.setdefault(key, a) != a:
                raise ValueError(f'Conflicting input at {key}')

    for name in ('source_range', 'balanced', 'corank_research_rows', 'phase_certificates',
                 'linear_tail_ranges', 'degree_reduction'):
        path = directory / f'{name}.jsonl'
        if path.exists():
            with path.open() as stream:
                for line in stream:
                    add(json.loads(line))
    for name in ('small_rows', 'small_rows_extension'):
        path = directory / f'{name}.json'
        if path.exists():
            data = json.loads(path.read_text())
            for row in data.get('exceptions', []):
                add(row)
            for block in data.get('rows', []) if name == 'small_rows_extension' else []:
                for row in block['residual']:
                    add(dict(row, n=block['n']))
    return found


def descending_sign(a, t):
    """Sign of P(-t), by homogenized integer Horner evaluation."""
    p, q = -t.numerator, t.denominator
    result, scale = a[-1], 1
    for c in reversed(a[:-1]):
        scale *= q
        result = result * p + c * scale
    return (result > 0) - (result < 0)


def bisect(a, lo, hi):
    if lo == hi:
        return lo, hi
    mid = (lo + hi) / 2
    sign = descending_sign(a, mid)
    if sign == 0:
        return mid, mid
    return (mid, hi) if sign > 0 else (lo, mid)


def check_archives(directory):
    vectors = read_vectors(directory)
    if not vectors:
        raise ValueError(f'No coefficient archives at {directory}')
    eligible = {key: a for key, a in vectors.items() if key[2] >= 3 and len(a) >= 2}
    intervals = {}
    for key, a in eligible.items():
        m = a[1]
        lo, hi = Fraction(1, m), Fraction(6, 5*m)
        lower_sign = descending_sign(a, lo)
        if lower_sign < 0 or descending_sign(a, hi) >= 0:
            raise ValueError(f'First-root endpoint signs at {key}')
        intervals[key] = (lo, lo) if lower_sign == 0 else (lo, hi)
        if any((k+1)**key[2] * a[k+1] > m*a[k] for k in range(1, len(a)-1)):
            raise ValueError(f'Layer count at {key}')
    comparisons = 0
    for (n, r, d), a in eligible.items():
        key, nxt = (n, r, d), (n+1, r, d)
        if nxt not in eligible:
            continue
        b = eligible[nxt]
        lower, upper = intervals[nxt]
        old_lower, old_upper = intervals[key]
        # Compare the actual rational isolators, independently of the row-difference bound.
        while upper >= old_lower:
            if upper == lower == old_lower == old_upper or old_upper <= lower:
                raise ValueError(f'Root order at {key}')
            lower, upper = bisect(b, lower, upper)
            old_lower, old_upper = bisect(a, old_lower, old_upper)
        if n >= 2 and len(b) >= 3 and a[1]*b[1] < 3*b[2]:
            raise ValueError(f'Extended disk too small at {key}')
        intervals[nxt], intervals[key] = (lower, upper), (old_lower, old_upper)
        comparisons += 1
    return {'available_vectors': len(vectors), 'eligible_nonlinear_or_linear': len(eligible),
            'consecutive_pairs_compared': comparisons}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archives', type=Path, default=HERE/'results')
    args = parser.parse_args()
    print(json.dumps({'exhaustive_boundary_counts': check_exceptions(),
                      **check_archives(args.archives)}, indent=2))
