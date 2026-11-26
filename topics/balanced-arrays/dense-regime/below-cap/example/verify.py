"""Replay the exact worked example with only the Python standard library."""
import argparse
import gzip
import json
from collections import Counter
from fractions import Fraction
from functools import cache
from itertools import combinations
from math import comb
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def capped_count(n, r, d, quota):
    """Append labeled columns, tracking clipped zero counts up to d-r."""
    minimum_zeros = d - r
    states = Counter({(0,) * n: 1})
    complements = tuple(combinations(range(n), n - quota))

    @cache
    def next_states(state):
        counts = Counter()
        for complement in complements:
            updated = list(state)
            for row in complement:
                updated[row] = min(minimum_zeros, updated[row] + 1)
            counts[tuple(sorted(updated))] += 1
        return counts

    for _ in range(d):
        updated = Counter()
        for state, weight in states.items():
            for target, multiplicity in next_states(state).items():
                updated[target] += weight * multiplicity
        states = updated
    return states[(minimum_zeros,) * n]


def evaluate(coefficients, point):
    result = Fraction(0)
    for coefficient in reversed(coefficients):
        result = result * point + coefficient
    return result


def check_intervals(coefficients, raw_intervals, name):
    intervals = [tuple(map(Fraction, pair)) for pair in raw_intervals]
    require(len(intervals) == len(coefficients)-1 and coefficients[-1] != 0,
            f"number of {name} intervals must equal degree")
    previous = Fraction(0)
    for index, (lo, hi) in enumerate(intervals, 1):
        require(previous < lo < hi, f"{name} interval {index} overlaps or is invalid")
        left = evaluate(coefficients, -lo)
        right = evaluate(coefficients, -hi)
        require((-1)**(index-1) * left > 0 and (-1)**index * right > 0,
                f"{name} interval {index} lacks its exact alternating signs")
        previous = hi
    return intervals


def check_archive(path, key, expected):
    found = 0
    n, r, d = key
    with gzip.open(path, "rt", encoding="utf-8") as stream:
        for line in stream:
            row = json.loads(line)
            if (row["n"], row["r"]) != (n, r):
                continue
            for field, shift in (("left", 0), ("right", 1)):
                if row["d"] + shift == d:
                    require(row[field] == expected, f"archive mismatch in {field}")
                    found += 1
    require(found > 0, "target case missing from comparison archive")
    print(f"Matched {found} archived coefficient vector")


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--archive", type=Path, help="optional existing column-extension JSONL.GZ")
    args = cli.parse_args()
    data = json.loads(Path(__file__).with_name("example.json").read_text())
    n, r, d = (data[key] for key in ("n", "r", "d"))
    require(1 < r < d-1, "expected a proper non-endpoint cap")
    capped = [capped_count(n, r, d, k) for k in range(n*r//d + 1)]
    unrestricted = [comb(n, k)**d for k in range(n+1)]
    require(capped == data["capped"], "capped recount mismatch")
    require(unrestricted == data["unrestricted"], "full count mismatch")
    if args.archive is not None:
        check_archive(args.archive, (n, r, d), capped)
    capped_intervals = check_intervals(capped, data["capped_magnitude_intervals"], "capped")
    full_intervals = check_intervals(unrestricted, data["unrestricted_magnitude_intervals"], "full")
    tolerance = Fraction(1, n*n)
    matched = []
    for index, ((clo, chi), (flo, fhi)) in enumerate(zip(capped_intervals, full_intervals), 1):
        low_ratio, high_ratio = clo / fhi, chi / flo
        if 1-tolerance < low_ratio <= high_ratio < 1+tolerance:
            matched.append(index)
        else:
            require(high_ratio < 1-tolerance or low_ratio > 1+tolerance,
                    f"comparison {index} is inconclusive")
    require(matched == data["matched_indices"], "incorrect match list")
    print(f"Verified {len(capped_intervals)} capped and {len(full_intervals)} unrestricted simple negative zeros")
    print(f"Exactly the matched indices {matched} are within relative {tolerance}")


if __name__ == "__main__":
    main()
