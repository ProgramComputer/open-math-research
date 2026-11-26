"""Independently replay every dyadic endpoint using cleared denominators."""
import argparse
import gzip
import itertools
import json
from pathlib import Path


def brute(n):
    counts = [0] * n
    for permutation in itertools.permutations(range(n)):
        if any(j == i or permutation[j] == i for i, j in enumerate(permutation)):
            continue
        counts[sum(j > i for i, j in enumerate(permutation))] += 1
    return counts


def check(path):
    count = 0
    with gzip.open(path, "rt") as data:
        for record in map(json.loads, data):
            n = record["n"]
            row = record["coefficients"]
            if n <= 8 and row != brute(n):
                raise ArithmeticError(f"Direct permutation count mismatch at {n}")
            for rank, pair in enumerate(record["brackets"], 1):
                for side, (numerator, shift) in enumerate(pair):
                    value = row[-1]
                    offset = shift
                    for coefficient in reversed(row[1:-1]):
                        value = (coefficient << offset) - value * numerator
                        offset += shift
                    if (value > 0) - (value < 0) != (-1) ** (rank - 1 + side):
                        raise ArithmeticError((n, rank, side))
                    count += 1
    if count != 79600:
        raise ArithmeticError(f"Unexpected number of bracket endpoints: {count}")
    print(f"Direct permutations through 8 and {count} denominator-cleared Horner signs passed.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path)
    check(parser.parse_args().archive)
