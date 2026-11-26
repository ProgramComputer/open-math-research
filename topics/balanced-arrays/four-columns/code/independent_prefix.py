"""Independently check the stored four-column prefix by integer arithmetic."""
from argparse import ArgumentParser
from collections import defaultdict
import gzip
from itertools import combinations
import json
from math import factorial
from pathlib import Path
from time import monotonic

from flint import fmpz


def matching_counts(quota):
    """Append one color to a matching on the preceding colors."""
    counts = [1]
    for colors in range(4):
        updated = [0] * ((colors + 1) * quota // 2 + 1)
        for pairs, count in enumerate(counts):
            free = colors * quota - 2 * pairs
            factor = 1
            for cross_pairs in range(min(quota, free) + 1):
                updated[pairs + cross_pairs] += count * factor
                factor = (
                    factor * (quota - cross_pairs) * (free - cross_pairs)
                    // (cross_pairs + 1)
                )
        counts = updated
    return counts


def independent_coefficients(last):
    """Assign matching blocks to rows using integer falling factorials."""
    rows = [[] for _ in range(last + 1)]
    factorials = [factorial(n) for n in range(last + 1)]
    for quota in range(last // 2 + 1):
        counts = matching_counts(quota)
        divisor = factorials[quota] ** 4
        for n in range(2 * quota, last + 1):
            first_pairs = max(0, 4 * quota - n)
            # Nested evaluation of the falling-factorial expansion.
            value = counts[first_pairs]
            for pairs in range(first_pairs + 1, 2 * quota + 1):
                value = value * (n - 4 * quota + pairs) + counts[pairs]
            value *= factorials[n] // factorials[n - 2 * quota]
            coefficient, remainder = divmod(value, divisor)
            if remainder or coefficient <= 0:
                raise ValueError(f"invalid coefficient at {(n, quota)}")
            rows[n].append(coefficient)
    return rows


def direct_array_rows(last):
    """Add labeled array rows and collect column sums, without matchings."""
    masks = [()] + list(combinations(range(4), 1)) + list(combinations(range(4), 2))
    counts = {(0, 0, 0, 0): 1}
    for n in range(last + 1):
        yield [counts[(quota,) * 4] for quota in range(n // 2 + 1)]
        if n == last:
            break
        updated = defaultdict(int)
        for sums, count in counts.items():
            for mask in masks:
                target = tuple(value + (column in mask) for column, value in enumerate(sums))
                updated[target] += count
        counts = updated


def paired_columns_coefficient(n, quota):
    """Count arrays by the rows containing both columns of either pair."""
    factorials = [factorial(j) for j in range(n + 1)]
    total = 0
    for a in range(quota + 1):
        for b in range(quota + 1):
            remaining = n - a - b
            first = quota - a
            second = quota - b
            if remaining < 2 * max(first, second):
                continue
            row_choices = factorials[n] // (
                factorials[a] * factorials[b] * factorials[remaining]
            )
            first_choices = factorials[remaining] // (
                factorials[first] ** 2 * factorials[remaining - 2 * first]
            )
            second_choices = factorials[remaining] // (
                factorials[second] ** 2 * factorials[remaining - 2 * second]
            )
            total += row_choices * first_choices * second_choices
    return total


def point_sign(row, numerator, denominator):
    """Homogeneous integer Horner evaluation at x=-(numerator/denominator)^4."""
    while numerator % 2 == 0 and denominator > 1:
        numerator //= 2
        denominator //= 2
    x = -(fmpz(numerator) ** 4)
    shift = 4 * (denominator.bit_length() - 1)
    value = row[-1]
    for power, coefficient in enumerate(row[-2::-1], 1):
        value = value * x + (coefficient << (power * shift))
    return int(value > 0) - int(value < 0)


def verify(directory, last):
    started = monotonic()
    rows = independent_coefficients(last)
    for n, row in enumerate(direct_array_rows(min(12, last))):
        if row != rows[n]:
            raise ValueError(f"direct array enumeration disagrees at {n=}")
    for n in sorted({last // 2, max(0, last - 1), last}):
        for quota in sorted({0, n // 4, n // 2}):
            if paired_columns_coefficient(n, quota) != rows[n][quota]:
                raise ValueError(f"paired-column enumeration disagrees at {(n, quota)}")
    print(f"Independently reconstructed {sum(map(len, rows))} coefficients "
          f"in {monotonic() - started:.2f}s.", flush=True)
    expected = nodes = 0
    for source in sorted(directory.glob("rows-*.jsonl.gz")):
        with gzip.open(source, "rt") as stream:
            for line in stream:
                record = json.loads(line)
                n = record["n"]
                if n > last:
                    continue
                if n != expected or record["a"] != rows[n]:
                    raise ValueError(f"coefficient record mismatch at {n=}, {expected=}")
                expected += 1
                degree = n // 2
                if len(rows[n]) != degree + 1 or rows[n][0] != 1 or rows[n][-1] <= 0:
                    raise ValueError(f"degree or endpoint mismatch at {n=}")
                points = record["t_numerators"]
                denominator = record["t_denominator"]
                if denominator != 1 << 32 or len(points) != max(0, degree - 1):
                    raise ValueError(f"invalid dyadic specification at {n=}")
                row = list(map(fmpz, rows[n]))
                previous = 0
                for j, numerator in enumerate(points, 1):
                    if type(numerator) is not int or numerator <= previous:
                        raise ValueError(f"invalid node at {(n, j)}")
                    previous = numerator
                    if point_sign(row, numerator, denominator) != (-1) ** j:
                        raise ValueError(f"wrong exact sign at {(n, j)}")
                    nodes += 1
    if expected != last + 1:
        raise ValueError(f"missing row {expected}")
    print(f"Checked rows 0–{last} and {nodes} interior signs by integer arithmetic "
          f"in {monotonic() - started:.2f}s.")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--last", type=int, default=532, choices=range(533), metavar="0..532")
    args = parser.parse_args()
    verify(args.directory, args.last)
