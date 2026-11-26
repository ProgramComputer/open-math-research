"""Reconstruct the threshold-three certificate by inclusion-exclusion."""

import argparse
from gzip import open as gzip_open
import json
from math import comb
from pathlib import Path


def eulerian_rows(limit):
    rows = [[1]]
    for n in range(1, limit + 1):
        row = [0] * n
        for j, count in enumerate(rows[-1]):
            row[j] += (j + 1) * count
            if j + 1 < n:
                row[j + 1] += (n - 1 - j) * count
        rows.append(row)
    return rows


def add_multiple(target, source, factor, shift=0):
    for j, count in enumerate(source):
        target[j + shift] += factor * count


def reconstruct(limit):
    unrestricted = eulerian_rows(limit)
    derangements = []
    for n in range(limit + 1):
        row = [0] * max(1, n)
        for m in range(n + 1):
            add_multiple(row, unrestricted[m], (-1)**(n - m) * comb(n, m))
        derangements.append(row)
        if n < 3:
            continue
        result = row.copy()
        factor = 1
        for j in range(1, n // 2 + 1):
            # Choose an unordered collection of j disjoint unordered pairs.
            factor = factor * comb(n - 2*j + 2, 2) // j
            add_multiple(result, derangements[n - 2*j], (-1)**j * factor, j)
        yield n, result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path, default=Path(__file__).with_name(
        "threshold-three-prefix.jsonl.gz"))
    parser.add_argument("--through", type=int, default=401)
    args = parser.parse_args()
    if not 3 <= args.through <= 401:
        parser.error("--through must be between 3 and 401")
    with gzip_open(args.archive, "rt", encoding="ascii") as records:
        for n, row in reconstruct(args.through):
            record = json.loads(records.readline())
            if record["n"] != n or record["coefficients"] != row:
                raise ArithmeticError(f"Inclusion-exclusion disagrees at n={n}")
        if args.through == 401 and records.read(1):
            raise ArithmeticError("Unexpected additional rows")
    print(f"Reconstructed all {args.through-2} coefficient vectors by deleting "
          "fixed points and transpositions from Eulerian permutations.")


if __name__ == "__main__":
    main()
