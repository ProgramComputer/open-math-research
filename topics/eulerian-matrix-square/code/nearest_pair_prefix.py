"""Reconstruct and certify the nearest-root inequalities through row 256."""

import argparse
import gzip
import hashlib
import json
import math
from pathlib import Path

from flint import fmpq, fmpz_poly


TOPIC = Path(__file__).resolve().parents[1]
RESULTS = TOPIC / "results"
ARCHIVE = RESULTS / "nearest-pair-prefix.jsonl.gz"
PREFIX = range(2, 257)


def read_source_rows():
    """Use the published vectors and, where present, their dyadic separators."""
    originals = {}
    with (RESULTS / "family-rows.jsonl").open() as stream:
        for row in map(json.loads, stream):
            n = row["n"]
            if 2 <= n <= 125:
                if row["coefficients"][0] != 0:
                    raise ArithmeticError(f"Missing origin factor in published row {n}")
                circles = None
                if "separators_hex" in row:
                    # The final separator for x*H_n lies between its first root and zero.
                    circles = [fmpq(*(-float.fromhex(x)).as_integer_ratio())
                               for x in reversed(row["separators_hex"][:-1])]
                originals[n] = ("family-rows.jsonl", row["coefficients"][1:], circles)

    for filename, wanted in (("rows-126-255.jsonl.gz", range(126, 256)),
                             ("large-rows.jsonl.gz", (256,))):
        with gzip.open(RESULTS / filename, "rt") as stream:
            for row in map(json.loads, stream):
                n = row["n"]
                if n in wanted:
                    if n in originals or row["stripped_zero"] != 1:
                        raise ArithmeticError(f"Invalid published row {n}")
                    circles = [unpack_dyadic(point) for point in row["positive_dyadics"]]
                    originals[n] = (filename, row["coefficients"], circles)
                if n == wanted[-1]:
                    break
    if sorted(originals) != list(PREFIX):
        raise ValueError("Published archives lack the required row inventory")
    return originals


def descent_row(n):
    """Exact alternating Eulerian formula, with no use of the row recurrence."""
    weights = [(-1)**i * math.comb(n+1, i) for i in range(n)]
    powers = [(i+1)**n for i in range(n)]
    return fmpz_poly([sum(weights[i] * powers[j-i] for i in range(j+1))
                      for j in range(n)])


def square_rows():
    eulerian = [None] + [descent_row(n) for n in range(1, 257)]
    for n in PREFIX:
        outer = eulerian[n]
        yield n, sum((outer[k-1] * eulerian[k] for k in range(1, n+1)), fmpz_poly([]))


def pack_dyadic(point):
    numerator, denominator = map(int, (point.numerator, point.denominator))
    if denominator & (denominator-1):
        raise ValueError(f"Expected a dyadic point, got {point}")
    return [numerator, 1-denominator.bit_length()]


def unpack_dyadic(record):
    numerator, exponent = record
    if type(numerator) is not int or type(exponent) is not int:
        raise ValueError("Expected integer dyadic coordinates")
    return fmpq(numerator) * fmpq(2)**exponent


def verify_separators(poly, separators):
    """Count all the roots by strict signs, including the last ray to infinity."""
    if len(separators) != poly.degree()-1 or poly[0] <= 0 or poly.leading_coefficient() <= 0:
        raise ArithmeticError("Incorrect degree, endpoint sign, or separator count")
    previous = fmpq(0)
    for i, point in enumerate(separators, 1):
        if point <= previous or (-1)**i * poly(-point) <= 0:
            raise ArithmeticError(f"Invalid separator of radius {point} at rank {i}")
        previous = point


def propose_small_separators(poly):
    """Floating-point proposals only, used for the first 22 archived rows."""
    roots = poly.complex_roots()
    if len(roots) != poly.degree() or any(not root.imag.is_zero() for root, _ in roots):
        raise ArithmeticError("Could not propose the small-row separators")
    radii = sorted(-float(root.real) for root, _ in roots)
    return [fmpq(*((a+b)/2).as_integer_ratio()) for a, b in zip(radii, radii[1:])]


def refine(poly, separators, rank):
    boundaries = [fmpq(0)] + separators
    left = boundaries[rank-1]
    sign = (-1)**(rank-1)
    if rank < poly.degree():
        right = boundaries[rank]
    else:
        # The last sign is eventually opposite by the leading monomial.
        right = max(fmpq(1), 2*left)
        while sign * poly(-right) >= 0:
            right *= 2

    while (right-left)*4096 > left:
        middle = (left+right)/2
        value = sign * poly(-middle)
        if value == 0:
            delta = (right-left)/4
            while delta*16384 > middle:
                delta /= 2
            return middle-delta, middle+delta
        if value > 0:
            left = middle
        else:
            right = middle
    return left, right


def verify_intervals(poly, separators, intervals):
    if len(intervals) != min(3, poly.degree()):
        raise ValueError("Missing a nearest-root interval")
    boundaries = [fmpq(0)] + separators
    for rank, (left, right) in enumerate(intervals, 1):
        if not 0 < left < right or left < boundaries[rank-1]:
            raise ArithmeticError(f"Invalid left boundary for rank {rank}")
        if rank < poly.degree() and right > boundaries[rank]:
            raise ArithmeticError(f"Invalid right boundary for rank {rank}")
        sign = (-1)**(rank-1)
        if sign*poly(-left) <= 0 or sign*poly(-right) >= 0:
            raise ArithmeticError(f"Invalid interval signs for rank {rank}")


def verify_order(n, left, right):
    chain = [right[0], left[0], right[1]]
    if n >= 3:
        chain.extend((left[1], right[2]))
    if any(a[1] >= b[0] for a, b in zip(chain, chain[1:])):
        raise ArithmeticError(f"An adjacent-row inequality is unproved at row {n}")


def certificate_rows(saved=None):
    sources = read_source_rows()
    previous = None
    for n, poly in square_rows():
        filename, original_coefficients, original_separators = sources[n]
        coefficients = list(map(int, poly))
        if coefficients != original_coefficients or poly.degree() != n-1 or min(coefficients) <= 0:
            raise ArithmeticError(f"Incorrect reconstructed coefficients at row {n}")
        digest = hashlib.sha256(json.dumps(coefficients, separators=(",", ":")).encode()).hexdigest()
        identity = dict(n=n, degree=n-1, coefficient_source=filename, coefficient_sha256=digest)
        if saved is None:
            separators = original_separators
            if separators is None:
                separators = propose_small_separators(poly)
            verify_separators(poly, separators)
            intervals = [refine(poly, separators, rank)
                         for rank in range(1, min(3, poly.degree())+1)]
            record = dict(identity, positive_separators=list(map(pack_dyadic, separators)),
                          nearest_intervals=[list(map(pack_dyadic, interval)) for interval in intervals])
        else:
            record = saved[n]
            if any(record.get(key) != value for key, value in identity.items()):
                raise ValueError(f"Certificate identity mismatch at row {n}")
            separators = list(map(unpack_dyadic, record["positive_separators"]))
            if original_separators is not None and separators != original_separators:
                raise ValueError(f"Published separators mismatch at row {n}")
            verify_separators(poly, separators)
            intervals = [tuple(map(unpack_dyadic, interval)) for interval in record["nearest_intervals"]]
        verify_intervals(poly, separators, intervals)
        if previous is not None:
            verify_order(n-1, previous, intervals)
        previous = intervals
        yield record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", nargs="?", type=Path, default=ARCHIVE)
    parser.add_argument("--replay", action="store_true")
    args = parser.parse_args()
    if args.replay:
        with gzip.open(args.archive, "rt") as stream:
            rows = list(map(json.loads, stream))
        if [row["n"] for row in rows] != list(PREFIX):
            raise ValueError("The prefix certificate must contain rows 2 through 256 in order")
        records = list(certificate_rows({row["n"]: row for row in rows}))
    else:
        records = list(certificate_rows())
        with args.archive.open("wb") as raw:
            with gzip.GzipFile(filename="", fileobj=raw, mode="wb", mtime=0) as stream:
                for record in records:
                    stream.write((json.dumps(record, separators=(",", ":")) + "\n").encode())
    if len(records) != len(PREFIX):
        raise ArithmeticError("Incomplete verification")
    print("Verified rows 2–256 and all nearest-root inequalities for pairs n=2–255.")


if __name__ == "__main__":
    main()
