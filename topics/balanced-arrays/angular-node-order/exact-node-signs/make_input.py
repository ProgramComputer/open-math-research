#!/usr/bin/env python3
"""Supply independently checked integer coefficients and untrusted search hints."""

import argparse
import gzip
from hashlib import sha256
import json
import math
from pathlib import Path


HERE = Path(__file__).resolve().parent
SAMPLED_ARCHIVE = HERE.parent / "screen-angular-signs.jsonl.gz"
FINITE_VECTORS = HERE.parent.parent / "finite-36" / "exact-vectors.jsonl"
SOURCE_HASH = "eea2b4519ef71be6904638ac07c57c1a852e2976fa59b98eca8fb406a69aadf0"
ARCHIVE_HASH = "177524eb815024cc3fe761a2767abb05f18eadf395e36adf8a263969a8a56a23"


def endpoint_coefficients(n, d, r):
    degree = n * r // d
    if r == 1:
        coefficients = [1]
        for k in range(1, degree + 1):
            upper = n - d * (k - 1)
            numerator = coefficients[-1] * math.prod(range(upper - d + 1, upper + 1))
            term, remainder = divmod(numerator, k**d)
            if remainder:
                raise ArithmeticError(f"Nonintegral rank-one coefficient at {(n, d, k)}")
            coefficients.append(term)
        return coefficients
    if r != d - 1:
        raise ValueError(f"Expected rank one or corank one at {(n, d, r)}")
    signed_row = [(-1)**j * math.comb(n, j) for j in range(degree + 1)]
    coefficients = []
    for k in range(degree + 1):
        choose = math.comb(n, k)
        coefficient = 0
        for j in range(k + 1):
            coefficient += signed_row[j] * choose**d
            if j < k:
                choose = choose * (k - j) // (n - j)
        coefficients.append(coefficient)
    return coefficients


def emit(key, coefficients, nodes):
    n, d, r = key
    degree = n * r // d
    if len(coefficients) != degree + 1 or coefficients[0] != 1 or min(coefficients) < 1:
        raise ArithmeticError(f"Invalid degree or coefficients for {key}")
    print(n, d, r, degree, len(nodes))
    print(*(format(term, "x") for term in coefficients))
    for quota, num, den in nodes:
        print(quota, format(num, "x"), format(den, "x"))


def replay():
    source = FINITE_VECTORS.read_bytes()
    if sha256(source).hexdigest() != SOURCE_HASH or sha256(SAMPLED_ARCHIVE.read_bytes()).hexdigest() != ARCHIVE_HASH:
        raise ValueError("Input hashes differ from the pinned Git blobs")
    finite = {}
    for line in source.splitlines():
        row = json.loads(line)
        finite[row["n"], row["d"], row["r"]] = row["coefficients"]
    expected = set(finite)
    expected.update((n, d, r) for n in range(2, 49) for d in range(2, min(n, 10) + 1)
                    for r in {1, d - 1})

    seen = set()
    count = 0
    with gzip.open(SAMPLED_ARCHIVE, "rt", encoding="utf-8") as stream:
        metadata = json.loads(next(stream))
        if metadata["format"] != "balanced-angular-sign-screen-v1":
            raise ValueError("Unexpected archive format")
        for line in stream:
            row = json.loads(line)
            if row["type"] == "summary":
                if next(stream, None) is not None:
                    raise ValueError("Trailing records in archive")
                break
            n, d, r = key = row["n"], row["d"], row["r"]
            if key in seen or key not in expected or row["type"] != "case":
                raise ValueError(f"Unexpected or repeated archive triple {key}")
            seen.add(key)
            coefficients = finite[key] if key in finite else endpoint_coefficients(*key)
            if coefficients != row["coefficients"]:
                raise ValueError(f"Coefficient replay differs for {key}")
            nodes = []
            for quota, (recorded, num, den, sign) in enumerate(row["nodes"], 1):
                if recorded != quota or sign != (-1)**quota or num <= 0:
                    raise ValueError(f"Unexpected archive quota, sign or tilt at {key + (quota,)}")
                nodes.append((quota, num, den))
            if len(nodes) != n * r // d - 1:
                raise ValueError(f"Incomplete quota list for {key}")
            count += len(nodes)
            emit(key, coefficients, nodes)
        else:
            raise ValueError("Missing archive summary")
    if seen != expected or len(seen) != 745 or count != 9162:
        raise ValueError(f"Incomplete archive: {len(seen)} triples, {count} nodes")


def saturation_quota(n, d):
    """Return the floor of n^((d-1)/d) using integer comparisons."""
    target = n ** (d - 1)
    lo, hi = 0, n
    while hi - lo > 1:
        middle = (lo + hi) // 2
        if middle**d <= target:
            lo = middle
        else:
            hi = middle
    return lo


def selected_quotas(degree):
    edges = (1, 2, 3, 4, 6, 8, 12, 16)
    selected = set(edges) | {degree - edge for edge in edges}
    selected.update(degree * j // 12 for j in range(1, 12))
    return sorted(k for k in selected if 0 < k < degree)


def extension_cases(mode):
    cases = set()
    if mode == "rank-one":
        for d in (11, 16, 24, 36, 64, 96, 128, 256, 512, 1024):
            for degree in (2, 3, 5, 8, 13, 21):
                for residue in (0, d // 2, d - 1):
                    cases.add((degree * d + residue, d, 1))
        for d in (8, 12, 16, 24, 32, 48, 64):
            for degree in (d // 2, d, 2 * d, 4 * d):
                for residue in (0, d - 1):
                    cases.add((degree * d + residue, d, 1))
    elif mode == "corank-one":
        for d in (11, 16, 24, 32, 48, 64, 96, 128, 192, 256):
            for n in (d, d + 1, 3 * d // 2, 2 * d, 2 * d + 1):
                if n <= 384:
                    cases.add((n, d, d - 1))
        for d in (8, 12, 16, 24, 32, 48):
            for n in (3 * d, 4 * d, 6 * d, 8 * d):
                cases.add((n, d, d - 1))
    elif mode == "corank-crossover":
        for d in (9, 13, 19, 23):
            for n in (d * d, d * d + 1):
                cases.add((n, d, d - 1))
    for key in sorted(cases):
        n, d, r = key
        degree = n * r // d
        quotas = range(1, degree) if degree <= 24 else selected_quotas(degree)
        if mode == "corank-crossover":
            # In the uncapped model the expected number of full rows is n*(k/n)^d.
            center = saturation_quota(n, d)
            quotas = sorted(set(quotas) | {k for k in range(center - 4, center + 5) if 0 < k < degree})
        nodes = [(k, 0, 1) for k in quotas]
        emit(key, endpoint_coefficients(*key), nodes)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("replay", "rank-one", "corank-one", "corank-crossover"))
    args = parser.parse_args()
    if args.mode == "replay":
        replay()
    else:
        extension_cases(args.mode)


if __name__ == "__main__":
    main()
