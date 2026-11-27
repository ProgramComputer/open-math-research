#!/usr/bin/env python3
"""Generate the nine explicit 32-bit recurrence ledgers in exact arithmetic."""
import argparse
from fractions import Fraction
from math import ceil, factorial, isqrt
from pathlib import Path

UPPERS = (6, 10, 16, 22, 28, 34, 40, 44, 48)
STAR_NUMERATORS = (228, 278, 331, 368, 397, 421, 441, 453, 463)
SCALE = 2**32


def star_numerator(upper):
    cutoff = 10000 // upper
    shape = (1 - Fraction(1, cutoff)) / (160 * upper)
    base = 2**56
    poles = range(-32, 32)
    weights = {q: ceil(base * (1 + shape * ((2*q + 1)**2 - 1))**-96)
               for q in poles}
    head = max(sum(ceil(Fraction(weights[q], 2 * abs(q-a)))
                   for q in poles if q != a)
               for a in range(-33, 33))
    first_tail = ceil(base * (1 + shape * (63**2 - 1))**-95 / (190 * shape))
    return ceil(Fraction(256 * (head + ceil(Fraction(ceil(Fraction(first_tail, 63)), 2))), base))


def numerator_mass(cutoff, degree_bin):
    if degree_bin < 4:
        return Fraction(0)
    if degree_bin == 4:
        return Fraction(1)
    if degree_bin <= 8:
        low = Fraction(degree_bin - 1, 4)
        mass = 1 / (low - Fraction(1, cutoff)) - Fraction(4, degree_bin)
        return mass + (Fraction(1, 4 * cutoff) if degree_bin == 8 else 0)
    return (Fraction(1, 4) + Fraction(1, cutoff)) / (2 * factorial((degree_bin - 1) // 4))


def ledger(upper, star):
    cutoff = 10000 // upper
    angular = Fraction(isqrt(192000) // upper, 4)
    linear = [ceil(SCALE * numerator_mass(cutoff, i) * Fraction(star, 256) / angular)
              for i in range(241)]
    q = [SCALE]
    for b in range(1, 241):
        numerator = sum(i * linear[i] * q[b-i] for i in range(4, b+1))
        quotient, remainder = divmod(numerator, b * SCALE)
        q.append(quotient + int(remainder != 0))
    return linear, q


def lean_array(entries):
    return '#[' + ',\n  '.join(', '.join(map(str, entries[i:i+12]))
                               for i in range(0, len(entries), 12)) + ']'


def lean_ledger(j, linear, q):
    return f"""import CoarseStarConstants

namespace OpenMathResearch.LongCycleExcedances

def coarseL{j} : Array ℕ := {lean_array(linear)}

def coarseQ{j} : Array ℕ := {lean_array(q)}

end OpenMathResearch.LongCycleExcedances
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('directory', type=Path)
    args = parser.parse_args()
    for j, (upper, star) in enumerate(zip(UPPERS, STAR_NUMERATORS, strict=True)):
        if star_numerator(upper) != star:
            raise ValueError(f'Unexpected signed star cap at upper slab boundary {upper}')
        expected = lean_ledger(j, *ledger(upper, star))
        path = args.directory / f'CoarseProductData{j}.lean'
        if args.check:
            if path.read_text() != expected:
                raise ValueError(f'Ledger file differs from the independently generated exact data: {path}')
        else:
            path.write_text(expected)
        print(j, upper, 241)


if __name__ == '__main__':
    main()
