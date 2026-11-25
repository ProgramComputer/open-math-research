"""Reconstruct and certify the ordered threshold-four rows and strip bound.

Requires python-flint. Coefficients come from separate associated Stirling
counts for small and large blocks. Consecutive signs use a Sturm–Tarski query.
"""

import argparse
import json
from fractions import Fraction
from gzip import GzipFile
from math import comb, factorial
from pathlib import Path

from flint import arb, ctx, fmpq, fmpq_poly, fmpz_poly


def ball(value):
    value = Fraction(value)
    return arb(fmpq(value.numerator, value.denominator))


def strip_certificate():
    """Certify an interval cover at Im z=4/3 with the real part rearranged."""
    ctx.prec = 160
    y = ball(Fraction(4, 3))
    sine = y.sin()
    cosine = y.cos()
    if not (sine > 0 and cosine > ball(Fraction(1, 5))
            and -cosine.log() < ball(Fraction(8, 5))):
        raise ArithmeticError("The sine and cosine bounds failed")
    pending = [(Fraction(-2), Fraction(2))]
    leaves = []
    while pending:
        low, high = pending.pop()
        x = ball(low).union(ball(high))
        if not x.contains(ball(low)) or not x.contains(ball(high)):
            raise ArithmeticError("The ball does not enclose its interval")
        imaginary_cubic = y*(1 + x + x*x/2 - y*y/6)
        v = 1 - imaginary_cubic/(x.exp()*sine)
        real_cubic = 1 + x + (x*x-y*y)/2 + (x*x*x-3*x*y*y)/6
        real = imaginary_cubic*cosine/sine - real_cubic + 2*v
        if v < 0:
            leaves.append((low, high, "v_below_zero"))
        elif v > ball(Fraction(1, 12)):
            leaves.append((low, high, "v_above_one_twelfth"))
        elif real > 0:
            leaves.append((low, high, "real_part_positive"))
        elif real < 0:
            leaves.append((low, high, "real_part_negative"))
        else:
            if high-low <= Fraction(1, 2**24):
                raise ArithmeticError(f"Unresolved strip interval [{low}, {high}]")
            midpoint = (low+high)/2
            pending.extend(((midpoint, high), (low, midpoint)))
    if leaves[0][0] != -2 or leaves[-1][1] != 2 or any(
            left[1] != right[0] for left, right in zip(leaves, leaves[1:])):
        raise ArithmeticError("The strip cover has a gap")
    return [[str(low), str(high), reason] for low, high, reason in leaves]


def restricted_block_counts(limit, minimum, maximum):
    table = [[1]]
    for n in range(1, limit+1):
        counts = [0]*(n//minimum+1)
        for size in range(minimum, min(maximum, n)+1):
            choices = comb(n-1, size-1)
            for k, previous in enumerate(table[n-size], start=1):
                counts[k] += choices*previous
        table.append(counts)
    return table


def coefficient_rows(limit):
    small = restricted_block_counts(limit, 1, 3)
    large = restricted_block_counts(limit, 4, limit)
    factorials = [factorial(n) for n in range(limit+1)]
    completed = [
        [sum(count*factorials[k+b] for b, count in enumerate(small[n]))
         for k in range((limit-n)//4+1)]
        for n in range(limit+1)
    ]
    for n in range(limit+1):
        coefficients = [0]*(n//4+1)
        for labels in range(n+1):
            choices = comb(n, labels)
            for k, count in enumerate(large[labels]):
                coefficients[k] += choices*count*completed[n-labels][k]
        yield coefficients


def variation_pair(first, second):
    """Signed remainder variation at minus and plus infinity."""
    negative_signs = []
    positive_signs = []
    while first:
        positive = 1 if first.leading_coefficient() > 0 else -1
        positive_signs.append(positive)
        negative_signs.append(positive*(-1)**first.degree())
        if not second:
            break
        residue = (-(fmpq_poly(first) % fmpq_poly(second))).numer()
        first = second
        second = residue // residue.content() if residue else residue

    def variations(signs):
        return sum(a != b for a, b in zip(signs, signs[1:]))

    return [variations(negative_signs), variations(positive_signs)]


def records(limit):
    yield dict(kind="strip", threshold=4, imaginary_part="4/3", arb_precision=160,
               intervals=strip_certificate())
    previous = None
    for n, coefficients in enumerate(coefficient_rows(limit)):
        row = fmpz_poly(coefficients)
        if row.degree() != n//4 or min(coefficients) <= 0:
            raise ArithmeticError(f"Unexpected degree or coefficients in row {n}")
        derivative = row.derivative()
        sturm = variation_pair(row, derivative)
        if sturm[0]-sturm[1] != row.degree():
            raise ArithmeticError(f"Row {n} lacks the required distinct real zeros")
        preceding = None
        if previous is not None:
            # The query sums sign(row'(root)*previous(root)) over the roots
            # of row. Each term must be +1 for the consecutive orientation.
            if row.degree() == 0:
                preceding = [0, 0]
            else:
                numerator = (fmpq_poly(derivative**2 * previous) % fmpq_poly(row)).numer()
                preceding = variation_pair(row, numerator)
            if preceding[0]-preceding[1] != row.degree():
                raise ArithmeticError(f"The pair ending at row {n} lacks strict interlacing")
        yield dict(kind="row", n=n, coefficients=coefficients,
                   sturm_variations=sturm, preceding_tarski_variations=preceding)
        previous = row


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path)
    parser.add_argument("--limit", type=int, default=200)
    parser.add_argument("--verify", action="store_true")
    args = parser.parse_args()
    if args.limit < 0:
        parser.error("the row limit must be nonnegative")
    if args.verify:
        with GzipFile(args.archive, "rb") as archive:
            for line, result in zip(archive, records(args.limit), strict=True):
                if json.loads(line) != result:
                    raise ArithmeticError(f"Archive differs at record {result.get('n', 'strip')}")
    else:
        with args.archive.open("xb") as destination:
            with GzipFile(filename="", fileobj=destination, mode="wb", mtime=0) as archive:
                for result in records(args.limit):
                    archive.write((json.dumps(result, separators=(",", ":")) + "\n").encode())
    print(f"Certified strip and {args.limit+1} rows with {args.limit} consecutive pairs.")


if __name__ == "__main__":
    main()
