"""Rebuild the outward-rounded product and principal costs from the Lean input ledger."""
from ast import literal_eval
from fractions import Fraction
from math import factorial, ceil
from pathlib import Path
import argparse


def error(j):
    if j == 0:
        return Fraction(4, 7)
    if j == 1:
        return Fraction(453, 1000)
    return min(Fraction(4, 7) - (Fraction(1, 2) if j == 2 else Fraction(547, 1000)),
               Fraction(j + 1, 2 * j * factorial(j)))


def ledger(path):
    return {int(label): literal_eval(entries)
            for line in path.read_text().splitlines() if line.strip()
            for label, entries in [line.split(maxsplit=1)]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('linear', type=Path)
    parser.add_argument('--lean-q', type=Path)
    parser.add_argument('--lean-caps', type=Path)
    parser.add_argument('--write-q', type=Path)
    args = parser.parse_args()
    source = ledger(args.linear)
    lowers = [4, 6, 10, 16, 22, 28, 34, 40, 44]
    uppers = lowers[1:] + [48]
    caps = [72559, 12006, 643, 104, 101, 101, 101, 101, 101]
    if sorted(source) != uppers:
        raise ValueError('wrong slab list')
    scale = 2**56
    result = {}
    for lower, upper, cap in zip(lowers, uppers, caps, strict=True):
        linear = source[upper]
        if len(linear) != 241 or any(coefficient < 0 for coefficient in linear):
            raise ValueError(f'invalid linear table for {upper}')
        q = [scale]
        for b in range(1, 241):
            numerator = sum(i * linear[i] * q[b - i] for i in range(1, b + 1))
            quotient, remainder = divmod(numerator, b * scale)
            q.append(quotient + int(remainder != 0))
        cost = Fraction(1, 10000) + Fraction(2, scale) * sum(
            error(min(40, max(0, lower - (b + 3)//4))) * value
            for b, value in enumerate(q))
        actual = ceil(cost * 10**6)
        if actual != cap:
            raise ValueError(f'inconsistent cost cap for {upper}: {actual} != {cap}')
        print(lower, upper, actual)
        result[upper] = q
    if args.lean_q and ledger(args.lean_q) != result:
        raise ValueError('q table differs from Lean')
    if args.lean_caps and literal_eval(args.lean_caps.read_text()) != caps:
        raise ValueError('cap table differs from Lean')
    if args.write_q:
        args.write_q.write_text(''.join(f'{upper} {result[upper]}\n' for upper in uppers))


if __name__ == '__main__':
    main()
