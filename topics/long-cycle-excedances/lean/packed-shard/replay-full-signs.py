"""Reconstruct the full reduced rows by distinguished cycle and check the shard."""

import csv
from math import comb
from pathlib import Path
import sys

from flint import fmpz_poly


def cycle_weights(last):
    cycle = [fmpz_poly(), fmpz_poly([0, 1])]
    x = cycle[1]
    for size in range(2, last + 1):
        prior = cycle[-1]
        # Eulerian insertion of the largest letter. The cycle-length
        # generating weights keep the mandatory factor of x.
        cycle.append((size - 1) * x * prior + x * (1 - x) * prior.derivative())
    return cycle


def original_rows(last, cutoff):
    cycles = cycle_weights(last)
    rows = [fmpz_poly([1])]
    for n in range(1, last + 1):
        row = fmpz_poly()
        for length in range(cutoff, n + 1):
            remainder = rows[n - length]
            if remainder:
                row += comb(n - 1, length - 1) * cycles[length] * remainder
        rows.append(row)
    return rows


def dyadic_sign(coefficients, numerator, bits):
    scaled = coefficients[-1]
    shift = 0
    for coefficient in reversed(coefficients[:-1]):
        shift += bits
        scaled = (coefficient << shift) - numerator * scaled
    return (scaled > 0) - (scaled < 0)


def main(path):
    with path.open(newline="") as shard:
        records = [tuple(map(int, row)) for row in csv.reader(shard)]
    assert len(records) == 131
    full = original_rows(256, 13)
    reduced = {}
    for n in range(251, 257):
        assert full[n][0] == 0 and full[n][1] == full[n][n - 1] == 1
        assert full[n].degree() == n - 1
        reduced[n] = [int(value) for value in full[n].coeffs()[1:]]
    for n, cutoff, rank, a, a_bits, b, b_bits in records:
        assert cutoff == 13 and n in range(251, 256)
        old, new = reduced[n], reduced[n + 1]
        expected = (-1)**(rank - 1)
        observed = (dyadic_sign(old, a, a_bits), dyadic_sign(old, b, b_bits),
                    dyadic_sign(new, a, a_bits), dyadic_sign(new, b, b_bits))
        assert observed == (expected, -expected, -expected, -expected), (n, rank)
    print("Independent full-degree distinguished-cycle replay: 524 exact signs.")


if __name__ == "__main__":
    main(Path(sys.argv[1]))
