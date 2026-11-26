"""Reproduce the corank-two counts and the interior column-extension obstruction."""
import argparse
from collections import defaultdict
from fractions import Fraction
from math import comb, factorial, lcm, perm
import gzip
import json
from pathlib import Path

from flint import fmpz_poly

from verify_column_extension import derivatives, require, root_report, special_count
from roots import interlaces


def corank_two_count(n, k, columns):
    """Inclusion–exclusion over rows having at most one zero."""
    if columns*k > n*(columns-2):
        return 0
    result = 0
    for marked in range(min(n, columns*k//(columns-1)) + 1):
        scale = factorial(marked)
        counts = []
        for omitted in range(marked + 1):
            needed = k-marked+omitted
            ways = comb(n-marked, needed) if 0 <= needed <= n-marked else 0
            counts.append(ways * (scale//factorial(omitted)))
        product = fmpz_poly(counts).pow_trunc(columns, marked + 1)
        numerator = sum(perm(marked, h)*int(product[h]) for h in range(len(product)))
        term, remainder = divmod(numerator, scale**columns)
        require(remainder == 0, "marked-row count must be integral")
        result += (-1)**marked * comb(n, marked) * term
    return result


def count_by_zero_quota(n, k, columns, minimum):
    """Count labeled complements by tracking rows still needing one or two zeros."""
    holes = n-k
    initial = (n, 0) if minimum == 2 else (0, n)
    states = {initial: 1}
    for step in range(columns):
        nxt = defaultdict(int)
        for (two, one), count in states.items():
            done = n-two-one
            for from_two in range(max(0, holes-one-done), min(holes, two)+1):
                left = holes-from_two
                for from_one in range(max(0, left-done), min(one, left)+1):
                    target = (two-from_two, one-from_one+from_two)
                    if 2*target[0]+target[1] > (columns-step-1)*holes:
                        continue
                    ways = comb(two, from_two)*comb(one, from_one)*comb(done, left-from_one)
                    nxt[target] += count*ways
        states = nxt
    return states.get((0, 0), 0)



def has_spacing(coefficients, ratio):
    degree = len(coefficients)-1
    scaled = [c * ratio.numerator**k * ratio.denominator**(degree-k)
              for k, c in enumerate(coefficients)]
    return interlaces(coefficients, scaled)


def geometric_symbol(left, right, ratio):
    # Homogenize each factor to keep the product integral as it is constructed.
    geometric = [1]
    for i in range(len(left)-1):
        leading, constant = ratio.numerator**i, ratio.denominator**i
        geometric = [a*constant + b*leading for a, b in zip(geometric+[0], [0]+geometric)]
    tilted = [c*Fraction(b,a) for c,a,b in zip(geometric,left,right)]
    denominator = lcm(*(x.denominator for x in tilted))
    return [int(denominator*x) for x in tilted]


def check_spacing_witness(left, right):
    for ratio in map(Fraction, ('6/5', '5/4', '4/3', '3/2', '5/3', '7/4', '2')):
        tilted = geometric_symbol(left, right, ratio)
        require(root_report(tilted)['real_rooted'] and has_spacing(tilted, ratio),
                'modified symbol does not have the specified spacing')
        require(has_spacing(left, ratio) == (ratio < 2), 'unexpected input spacing')


def check_spacing_pilot():
    directory = Path(__file__).resolve().parents[1] / 'results'
    tested = 0
    for name in ('column-extension-screen.jsonl.gz', 'column-extension-corank-two.jsonl.gz'):
        with gzip.open(directory / name, 'rt') as stream:
            for record in map(json.loads, stream):
                n, r = record['n'], record['r']
                if r < 2 or n > 36:
                    continue
                ratio = 1 + Fraction(2*r,n)
                left = record['left']
                tilted = geometric_symbol(left, record['right'], ratio)
                for polynomial in (left, tilted):
                    require(root_report(polynomial)['real_rooted'] and has_spacing(polynomial, ratio),
                            f'spacing failure at {(n,r,record["d"])}')
                tested += 1
    require(tested == 337, 'unexpected number of geometric symbols')
    print('Verified the input and modified symbol spacing at all 337 pilot parameters.')


def check(record, recount):
    n, r, d = (record[key] for key in ('n', 'r', 'd'))
    left, right = record['left'], record['right']
    require(r == d-1 and len(left) == n*r//d + 1 and len(right) == n*r//(d+1) + 1,
            'degrees or rank')
    if recount:
        expected_left = [special_count(n, k, r, d) for k in range(len(left))]
        expected_right = [corank_two_count(n, k, d+1) for k in range(len(right))]
        require((expected_left, expected_right) == (left, right), 'inclusion–exclusion mismatch')
    m = len(left)-1
    symbol = [Fraction(comb(m, k)*b, left[k]) for k, b in enumerate(right)]
    den = lcm(*(x.denominator for x in symbol))
    actual = root_report([int(den*x) for x in symbol])
    require(actual == record['report'], 'Sturm count differs')
    if (n,r,d) == (36,5,6):
        for vector, columns, minimum in ((left,d,1), (right,d+1,2)):
            require(vector == [count_by_zero_quota(n,k,columns,minimum) for k in range(len(vector))],
                    'independent complement-count mismatch')
            require(root_report(vector)['distinct_real_roots'] == len(vector)-1,
                    'expected simple real roots for each array polynomial')
        check_spacing_witness(left, right)
        a, b, c = derivatives(symbol[::-1], Fraction(-13,4))
        require(b*b < a*c, 'expected a strict Laguerre violation')
        require(actual['squarefree_degree'] == 25 and actual['distinct_real_roots'] == 23,
                'expected one conjugate pair in the symbol')
    return actual['real_rooted']


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--recount', action='store_true', help='recompute all coefficients from the formula')
    parser.add_argument('--spacing-pilot', action='store_true', help='replay only the 337 geometric-symbol tests')
    args = parser.parse_args()
    if args.spacing_pilot:
        check_spacing_pilot()
        raise SystemExit(0)
    archive = Path(__file__).resolve().parents[1] / 'results/column-extension-corank-two.jsonl.gz'
    with gzip.open(archive, 'rt') as stream:
        rows = list(map(json.loads, stream))
    keys = [(row['n'],row['d']) for row in rows]
    require(keys == [(n,d) for n in (16,24,30,36,48,60,72) for d in (4,5,6,8,10,14,18,24)
                     if 2*d <= n], 'incomplete grid')
    failures = sum(not check(record, args.recount) for record in rows)
    print(f'Checked {len(rows)} symbols, of which {failures} have a nonreal zero.')
    print('Both array rows at (n,r,d)=(36,5,6) passed the independent count and root tests.')
