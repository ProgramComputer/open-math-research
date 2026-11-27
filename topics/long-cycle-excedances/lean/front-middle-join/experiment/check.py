"""Exact coefficient-norm experiment for the exterior singleton criterion."""
from fractions import Fraction
from itertools import permutations
from math import comb, isqrt
from pathlib import Path
import gzip
import json

SIZES = (12, 24, 40, 64, 96, 128)
DENOMINATOR = 10**6


def eulerian_rows(limit):
    rows = [[1]]
    for size in range(1, limit + 1):
        old = rows[-1]
        rows.append([
            (j + 1) * (old[j] if j < len(old) else 0)
            + (size - j) * (old[j - 1] if j else 0)
            for j in range(size)
        ])
    return rows


def add_shifted_product(out, left, right, factor, shift=1):
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            if a and b:
                out[shift + i + j] += factor * a * b


def anchored(k, limit, eulerian):
    # Choose the cycle containing the greatest letter and delete that letter
    # inside the cycle. Its contribution is t times the Eulerian row.
    rows = [[1]]
    for size in range(1, limit + 1):
        row = [0] * (size + 1)
        for cycle in range(k, size + 1):
            add_shifted_product(row, eulerian[cycle - 1], rows[size - cycle],
                                comb(size - 1, cycle - 1))
        rows.append(row)
    return rows


def inserted(k, limit, eulerian):
    # Insertion into a longer cycle yields the derivative operator.
    # A newly admissible minimum-length cycle yields the lag term.
    rows = [[1]]
    for n in range(limit):
        row = [0] * (n + 2)
        for j, a in enumerate(rows[-1]):
            row[j] += j * a
            row[j + 1] += (n - j) * a
        if k <= n + 1:
            add_shifted_product(row, eulerian[k - 1], rows[n + 1 - k],
                                comb(n, k - 1))
        rows.append(row)
    return rows


def literal_row(n, k):
    row = [0] * (n + 1)
    for perm in permutations(range(n)):
        unused = set(range(n))
        while unused:
            start = unused.pop()
            length, current = 1, perm[start]
            while current != start:
                unused.remove(current)
                length += 1
                current = perm[current]
            if length < k:
                break
        else:
            row[sum(j < image for j, image in enumerate(perm))] += 1
    return row


def norm_ratio(row, h, lower, upper, a):
    # Horner on the nonnegative and negative powers separately.
    above = Fraction(0)
    for coefficient in reversed(row[h:]):
        above = above * upper + abs(coefficient)
    below = Fraction(0)
    for coefficient in row[:h]:
        below = below / lower + abs(coefficient)
    return (above + below / lower) / a


def rational_bracket(value):
    scaled = value * DENOMINATOR
    floor = scaled.numerator // scaled.denominator
    ceil = -(-scaled.numerator // scaled.denominator)
    return [floor, ceil]


def check_window(n, p, q, lag, h):
    a, b = p[h], p[h + 1]
    assert a > 0 and b > 0
    u = Fraction(a, b)
    lower, upper = 7 * u / 8, 9 * u / 8
    t = p.copy()
    t[h] -= a
    t[h + 1] -= b
    w = q.copy()
    for j, p_j in enumerate(p):
        w[j] -= (h + 1) * p_j
        w[j + 1] -= (n - h - 1) * p_j
    w[h] += a
    w[h + 1] -= a
    # Independent identity through the insertion split, at the coefficient level.
    # W = (1-t)[t P'-(h+1)P+a*t^h] + t*lag.
    centered = [((j - h - 1) * coefficient) for j, coefficient in enumerate(p)]
    centered[h] += a
    insertion_w = lag.copy()
    for j, coefficient in enumerate(centered):
        insertion_w[j] += coefficient
        insertion_w[j + 1] -= coefficient
    assert w == insertion_w, (n, h)

    mt = norm_ratio(t, h, lower, upper, a)
    mw = norm_ratio(w, h, lower, upper, a)
    return dict(h=h, a=a, u=[u.numerator, u.denominator],
                lower=[lower.numerator, lower.denominator],
                upper=[upper.numerator, upper.denominator],
                t=t, w=w, t_bracket=rational_bracket(mt), w_bracket=rational_bracket(mw),
                t_pass=mt < Fraction(1, 8), w_pass=mw < 1)


def main():
    eulerian = eulerian_rows(max(SIZES))
    literal_count = 0
    for k in (2, 3, 7):
        rows = anchored(k, 8, eulerian)
        for n in range(9):
            assert rows[n] == literal_row(n, k), (n, k)
            literal_count += 1
    pairs = []
    for n in SIZES:
        for k in sorted({3, 7, n // 4, n}):
            anchor = anchored(k, n + 1, eulerian)
            insert = inserted(k, n + 1, eulerian)
            assert anchor == insert, (n, k)
            p, q = anchor[n:n + 2]
            hmax = isqrt(49 * n) // 20
            lag = [0] * len(q)
            add_shifted_product(lag, eulerian[k - 1], anchor[n + 1 - k], comb(n, k - 1))
            windows = [check_window(n, p, q, lag, h) for h in range(1, hmax + 1)]
            pairs.append(dict(n=n, k=k, p=p, q=q, windows=windows))
    here = Path(__file__).resolve().parent
    data = json.dumps(dict(bracket_denominator=DENOMINATOR, pairs=pairs), indent=2) + '\n'
    (here / 'ledger.json.gz').write_bytes(gzip.compress(data.encode(), mtime=0))

    count = sum(len(row['windows']) for row in pairs)
    passes = 0
    print('Each norm bracket has denominator 1000000 and bounds M/a inclusively.')
    print(' n   k  h     T lower     T upper     W lower     W upper   T   W')
    for row in pairs:
        for window in row['windows']:
            tl, tu = window['t_bracket']
            wl, wu = window['w_bracket']
            tp, wp = window['t_pass'], window['w_pass']
            passes += tp and wp
            print(f"{row['n']:3} {row['k']:3} {window['h']:2} "
                  f"{tl:11} {tu:11} {wl:11} {wu:11}   {str(tp):5} {str(wp)}")
    print(f'Both strict tests passed in {passes}/{count} windows across {len(pairs)} row pairs.')
    print('All old and successor rows agree with the independent anchored-cycle recurrence.')
    print(f'Literal permutation enumeration independently matched {literal_count} small rows.')
    windows = [(row['n'], row['k'], w) for row in pairs for w in row['windows']]
    for component in ('t', 'w'):
        n, k, witness = max(windows, key=lambda record: record[2][component + '_bracket'][1])
        lo, hi = witness[component + '_bracket']
        print(f'Maximum {component.upper()} norm ratio is in [{lo}, {hi}]/1000000, '
              f'attained up to bracket precision at n={n}, k={k}, h={witness["h"]}.')



if __name__ == '__main__':
    main()
