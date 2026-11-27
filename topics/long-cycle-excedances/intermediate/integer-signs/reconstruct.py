"""Independently count the anchored least-label cycle, then certify a genuine pair."""
import argparse
import gzip
import hashlib
import json
import subprocess
from math import comb
from pathlib import Path

from flint import fmpz_poly


def anchored(k, nmax, width):
    # Eulerian coefficients by alternating power sums, independent of the
    # coefficient insertion recurrence used in the audited program.
    factors = {}
    for a in range(k, nmax + 1):
        m = a - 1
        factors[a] = fmpz_poly([
            sum((-1)**v * comb(m + 1, v) * (i + 1 - v)**m for v in range(i + 1))
            for i in range(min(m, width))
        ])
    original = [fmpz_poly([1])]
    X = fmpz_poly([0, 1])
    for n in range(1, nmax + 1):
        q = fmpz_poly()
        for a in range(k, n + 1):
            if original[n-a]:
                q += comb(n-1,a-1) * factors[a].mul_low(original[n-a], width)
        original.append((X*q).truncate(width + 1))
    return [[int(original[n][i+1]) for i in range(width)] for n in (nmax-1,nmax)]


def sign_at(c, a, bits, n, direction):
    w = len(c)
    D = 1 << bits
    numerator = sum((-1)**i * v * a**i * D**(w-1-i) for i,v in enumerate(c))
    U = D * (w+1)**n - a*(w+2)**n
    assert 0 < U
    return direction*numerator*U > (w+1)**(2*n)*a**w


def first_pair(shard_path):
    with gzip.open(shard_path, "rt") as stream:
        shard = []
        for line in stream:
            record = tuple(map(int, line.split(",")))
            if shard and record[:2] != shard[0][:2]:
                break
            shard.append(record)
    return shard


def verify(shard_path, checker):
    shard = first_pair(shard_path)
    if len(shard) != 26 or shard[0][:2] != (251, 13):
        raise ValueError("Unexpected first-pair fixture.")
    n, k = shard[0][:2]
    rows = anchored(k, n + 1, 60)
    for old, cutoff, rank, a, a_bits, b, b_bits in shard:
        direction = (-1) ** (rank - 1)
        for numerator, bits, old_sign in ((a, a_bits, direction), (b, b_bits, -direction)):
            if not sign_at(rows[0], numerator, bits, old, old_sign):
                raise ValueError(f"Uncertified old sign at cutoff {cutoff}, rank {rank}.")
            if not sign_at(rows[1], numerator, bits, old + 1, -direction):
                raise ValueError(f"Uncertified next sign at cutoff {cutoff}, rank {rank}.")
    encoded = "".join(json.dumps(row, separators=(",", ":")) + "\n" for row in rows).encode("ascii")
    expected = Path(__file__).with_name("first-pair-coefficients.jsonl")
    if encoded != expected.read_bytes():
        raise ValueError("The retained coefficient fixture differs.")
    insertion = subprocess.check_output([checker.resolve(), "--first-pair-prefixes"])
    if encoded != insertion:
        raise ValueError("The anchored and insertion coefficient arrays differ.")
    print(
        f"k={k} sizes={n},{n + 1} coefficients={sum(map(len, rows))} "
        f"gaps={len(shard)} exact_signs={4 * len(shard)} sha256={hashlib.sha256(encoded).hexdigest()}"
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("first_shard", type=Path)
    parser.add_argument("checker", type=Path)
    args = parser.parse_args()
    if not __debug__:
        raise SystemExit("Use Python with assertions enabled.")
    verify(args.first_shard, args.checker)
