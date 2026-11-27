"""Construct and replay a rational certificate for any fixed old degree d >= 2."""
import argparse
import json
import sys
from fractions import Fraction as Q
from functools import cache
from itertools import pairwise
from math import comb, factorial, gcd, lcm
from pathlib import Path


# The certificate format encodes exact unbounded integers in decimal.
if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)


def coefficient_error(d):
    return (d + 2) ** 2 * (2 ** (d + 1) * 8 ** (d + 2) + 2) * (2 * d + 4) ** (d + 1)


@cache
def model(d, c, derivative):
    if derivative:
        return (Q(0),) + tuple((c - k) ** (k - 1) / factorial(k - 1) for k in range(1, d + 1)) + (Q(0),)
    return (Q(1),) + tuple((c - k) ** k / factorial(k) for k in range(1, d + 1))


def primitive(values):
    scale = lcm(*(v.denominator for v in values))
    row = [int(v * scale) for v in values]
    content = gcd(*row)
    return [i // content for i in row]


@cache
def derivative_rows(d, c):
    # Projective limit in y=x/(1+x), then its ordinary derivatives.
    f = model(d, c, False)
    values = [(-1) ** h * sum(comb(d - k, h - k) * f[k] for k in range(h + 1)) for h in range(d + 1)]
    rows = []
    while values:
        values = primitive(values)
        rows.append(values)
        values = [i * v for i, v in enumerate(values) if i]
    return rows


def sign_at(row, a, b):
    value = row[-1]
    power = 1
    for coefficient in reversed(row[:-1]):
        power *= b
        value = a * value + power * coefficient
    return (value > 0) - (value < 0)


def roots_to_right(rows, a, b):
    # Descartes applied after translation is exact when all roots are real.
    signs = [sign_at(row, a, b) for row in rows]
    signs = [sign for sign in signs if sign]
    return sum(first != second for first, second in pairwise(signs))


def root_intervals(d, c, precision):
    rows = derivative_rows(d, c)
    denominator = 1 << precision
    @cache
    def count(a):
        return d - roots_to_right(rows, a, denominator)
    result = []
    for rank in range(1, d + 1):
        lo, hi = 0, denominator
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if count(mid) >= rank:
                hi = mid
            else:
                lo = mid
        result.append((Q(lo, denominator), Q(hi, denominator)))
    return result


def good_sign(d, lo, hi, a, b, pad, derivative, direction):
    left, right = model(d, lo, derivative), model(d, hi, derivative)
    order = len(left) - 1
    total = 0
    for k, (u, v) in enumerate(zip(left, right)):
        low_weight = a ** k * (1 - b) ** (order - k)
        high_weight = b ** k * (1 - a) ** (order - k)
        if direction * (-1) ** k > 0:
            total += u * low_weight - pad * high_weight
        else:
            total -= (v + pad) * high_weight
    return total > 0


def seam_sign(d, lo, hi, a, pad):
    if hi >= d + Q(1, 2) or a <= 0:
        return False
    w = (1 - a) / a
    f_lo, f_hi = model(d, lo, False), model(d, hi, False)
    slopes = model(d, hi, True)
    previous = f_lo[d - 1] - pad - sum((f_hi[k] + pad) * w ** (d - 1 - k) for k in range(d - 1))
    remainder = sum((slopes[k] + pad) * w ** (d - 1 - k) for k in range(d))
    return previous > 4 * (hi - d + pad) * remainder


def root_ok(d, lo, hi, a, b, pad, rank):
    direction = (-1) ** rank
    if not 0 <= a < b <= 1 or not good_sign(d, lo, hi, a, a, pad, False, -direction):
        return False
    if b == 1:
        return rank == d and seam_sign(d, lo, hi, a, pad)
    return good_sign(d, lo, hi, b, b, pad, False, direction) and good_sign(d, lo, hi, a, b, pad, True, direction)


def propose(d, lo, hi, depth, pad):
    left = root_intervals(d, hi, depth + 20)
    right = root_intervals(d, lo, depth + 20)
    fences = [Q(0)] + [(r[1] + l[0]) / 2 for r, l in zip(right, left[1:])] + [Q(1)]
    brackets = []
    for rank, ((l, _), (_, r)) in enumerate(zip(left, right), 1):
        for e in range(2, depth + 14):
            denominator = 1 << e
            a = max(Q(0), Q((l * denominator).__floor__() - 1, denominator))
            b = min(Q(1), Q((r * denominator).__ceil__() + 1, denominator))
            if rank > 1 and a <= fences[rank - 1] or rank < d and b >= fences[rank]:
                continue
            if root_ok(d, lo, hi, a, b, pad, rank):
                brackets.append([str(a), str(b)])
                break
        else:
            return None
    return brackets


def generate(d):
    todo = [(Q(d), Q(d + 1), 0)]
    cells = []
    while todo:
        lo, hi, depth = todo.pop()
        pad = Q(1, 1 << (32 + 2 * depth))
        brackets = propose(d, lo, hi, depth, pad)
        if brackets is not None:
            cells.append([str(lo), str(hi), str(pad), brackets])
        else:
            mid = (lo + hi) / 2
            todo.extend(((mid, hi, depth + 1), (lo, mid, depth + 1)))
    cutoff = coefficient_error(d) * max(Q(cell[2]).denominator for cell in cells)
    return {'degree': d, 'cutoff': cutoff, 'cells': cells}


def replay(certificate):
    d, cutoff = certificate['degree'], certificate['cutoff']
    if not isinstance(d, int) or d < 2 or not isinstance(cutoff, int) or cutoff < 2:
        raise ValueError('Invalid degree or cutoff')
    end = Q(d)
    for lo, hi, pad, brackets in certificate['cells']:
        lo, hi, pad = Q(lo), Q(hi), Q(pad)
        if lo != end or not lo < hi <= d + 1 or pad <= 0 or coefficient_error(d) > pad * cutoff or len(brackets) != d:
            raise ValueError(f'Invalid cell at {lo}')
        last = -1
        for rank, (a, b) in enumerate(brackets, 1):
            a, b = Q(a), Q(b)
            if a <= last or not root_ok(d, lo, hi, a, b, pad, rank):
                raise ValueError(f'Invalid degree-{d} bracket {rank} in [{lo}, {hi}]')
            last = b
        end = hi
    if end != d + 1:
        raise ValueError('Incomplete cover')
    print(f"Degree {d}: {len(certificate['cells'])} cells, all j >= {cutoff}", flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('file', type=Path)
    parser.add_argument('--generate', type=int, metavar='DEGREE')
    args = parser.parse_args()
    if args.generate is None:
        replay(json.loads(args.file.read_text()))
    else:
        if args.generate < 2:
            parser.error('degree must be at least two')
        data = generate(args.generate)
        replay(data)
        args.file.write_text(json.dumps(data, separators=(',', ':')) + '\n')
