"""Independently rebuild the selected Eulerian-square rows and verify all dyadic root intervals."""

import gzip
import json
import sys
from pathlib import Path
from flint import fmpq, fmpz_poly

SIZES = (128, 192, 256, 384, 512, 768, 1024)


def descent_row(n):
    """Eulerian coefficient formula as an exact product of integer power series."""
    power_sums = fmpz_poly([j**n for j in range(1, n+1)])
    difference = fmpz_poly([1, -1]).pow_trunc(n+1, n)
    return difference.mul_low(power_sums, n)


def main():
    limit = max(SIZES)
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(max(4300, 2*limit*len(str(limit))+10))
    outer = {n: descent_row(n) for n in SIZES}
    expected = {n: fmpz_poly([]) for n in SIZES}
    for k in range(1, limit+1):
        inner = outer[k] if k in outer else descent_row(k)
        for n in SIZES:
            if k <= n:
                expected[n] += outer[n][k-1]*inner
    path = Path(__file__).resolve().parent / "results" / "large-rows.jsonl.gz"
    with gzip.open(path, "rt") as stream:
        saved = list(map(json.loads, stream))
    if [row["n"] for row in saved] != list(SIZES):
        raise ValueError("Missing, duplicated or unexpected row size")
    for row in saved:
        n = row["n"]
        poly = expected[n]
        if poly.degree() != n-1 or list(poly) != row["coefficients"] or min(poly) <= 0:
            raise ArithmeticError(f"Coefficient verification failed at {n}")
        probes = row["positive_dyadics"]
        if len(probes) != n-2 or row["simple_negative_zeros"] != n-1 or row["stripped_zero"] != 1:
            raise ValueError(f"Incorrect certificate size or multiplicity at {n}")
        previous = fmpq(0)
        for i, (mantissa, exponent) in enumerate(probes, 1):
            radius = fmpq(mantissa) * fmpq(2)**exponent
            if radius <= previous or (-1)**i * poly(-radius) <= 0:
                raise ArithmeticError(f"Invalid separator {i} at n={n}")
            previous = radius
        print(f"Verified n={n}: {n-1} distinct negative zeros and the simple zero at the origin.")


if __name__ == "__main__":
    main()
