"""Verify the exact obstruction to 31 relative bits from a full polynomial."""
import csv
import gzip
from decimal import Decimal, localcontext
from math import comb
from pathlib import Path
import sys


def endpoint(shards):
    matches = []
    for shard in sorted(shards.glob("part-*.csv.gz")):
        with gzip.open(shard, "rt") as stream:
            for record in csv.reader(stream):
                if record[:3] == ["255", "13", "32"]:
                    matches.append(tuple(map(int, record)))
    (record,) = matches
    return record


def full_row(size, cutoff):
    # Explicit Eulerian numbers of permutations of cutoff-1 labels.
    seed = [
        sum((-1)**i * comb(cutoff, i) * (j + 1 - i)**(cutoff - 1)
            for i in range(j + 1))
        for j in range(cutoff - 1)
    ]
    rows = {cutoff: seed}
    for n in range(cutoff, size):
        following = [0] * n
        for j, count in enumerate(rows[n]):
            following[j] += (j + 1) * count
            following[j + 1] += (n - j - 1) * count
        factor = comb(n, cutoff - 1)
        for j, count in enumerate(rows.get(n + 1 - cutoff, ())):
            for i, weight in enumerate(seed):
                following[i + j + 1] += factor * weight * count
        if following[0] != 1 or following != following[::-1]:
            raise ArithmeticError(f"Invalid reciprocal row at size {n + 1}")
        rows[n + 1] = following
    return rows[size]


def homogeneous(row, numerator, bits):
    value = 0
    for j, coefficient in enumerate(reversed(row)):
        value = value * numerator + (coefficient << (bits * j))
    return value


def main(shards):
    n, k, rank, p, bits, _, _ = endpoint(shards)
    if (p, bits) != (871689497096755307205496065384395168305363817049, 170):
        raise ValueError("Wrong left endpoint")
    coefficients = full_row(n + 1, k)
    sign = 1 if rank % 2 == 0 else -1
    signed = sign * homogeneous(coefficients, -p, bits)
    positive = homogeneous(coefficients, p, bits)
    if not (0 < (signed << 31) < positive < (signed << 32)):
        raise ArithmeticError("Exact sharpness comparisons failed")
    print(f"PASS: n={n + 1} k={k} rank={rank} degree={len(coefficients)-1} sign={sign}")
    print("2^31 * signed numerator < positive numerator < 2^32 * signed numerator")
    with localcontext() as ctx:
        ctx.prec = 24
        print("Signed-to-positive ratio (decimal for reference):", Decimal(signed) / Decimal(positive))


if __name__ == "__main__":
    main(Path(sys.argv[1]))
