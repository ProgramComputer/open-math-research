"""Independently rebuild the selected Eulerian-square rows and verify all dyadic root intervals."""

import argparse
import gzip
import json
import sys
from pathlib import Path
from flint import fmpq, fmpq_poly, fmpz_poly

SIZES = (128, 192, 256, 384, 512, 768, 1024)


def descent_row(n):
    """Eulerian coefficient formula as an exact product of integer power series."""
    power_sums = fmpz_poly([j**n for j in range(1, n+1)])
    difference = fmpz_poly([1, -1]).pow_trunc(n+1, n)
    return difference.mul_low(power_sums, n)


def check_initial(row, poly):
    n = row["n"]
    if list(poly) != row["coefficients"] or poly.degree() != n or not row["real_rooted"]:
        raise ValueError(f"Incorrect original row at {n}")
    if row["squarefree_degree"] != n or row["distinct_real_roots"] != n:
        raise ValueError(f"Incorrect reported simple root count at {n}")
    if row["method"] == "primitive rational Sturm":
        a = fmpq_poly(poly)
        b = a.derivative()
        chain = [a]
        while b:
            chain.append(b)
            a, b = b, -(a % b)
        if chain[-1].degree() != 0:
            raise ArithmeticError(f"Repeated root at {n}")
        right = [1 if q.leading_coefficient() > 0 else -1 for q in chain]
        left = [(-1)**q.degree() * sign for q, sign in zip(chain, right)]
        def changes(signs):
            return sum(a != b for a, b in zip(signs, signs[1:]))
        if changes(left) - changes(right) != n:
            raise ArithmeticError(f"Sturm count failed at {n}")
    elif row["method"] == "exact dyadic sign separation":
        points = [fmpq(*float.fromhex(x).as_integer_ratio()) for x in row["separators_hex"]]
        if len(points) != n-1 or any(x >= y for x, y in zip(points, points[1:])):
            raise ValueError(f"Bad separator list at {n}")
        for i, x in enumerate(points, 1):
            if (-1)**(n+i) * poly(x) <= 0:
                raise ArithmeticError(f"Invalid dyadic sign at {n}")
    else:
        raise ValueError(f"Unknown original root certificate at {n}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path)
    parser.add_argument("--initial", action="store_true", help="check all original rows 0 through 125")
    parser.add_argument("--interval", nargs=2, type=int, metavar=("FIRST", "LAST"))
    args = parser.parse_args()
    if args.initial and args.interval:
        parser.error("--initial and --interval select different certificate formats")
    sizes = SIZES if args.interval is None else tuple(range(args.interval[0], args.interval[1]+1))
    if args.initial:
        sizes = tuple(range(1, 126))
    if not sizes or (not args.initial and min(sizes) < 2):
        parser.error("this verifier expects row sizes of at least two")
    limit = max(sizes)
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(max(4300, 2*limit*len(str(limit))+10))
    outer = {n: descent_row(n) for n in sizes}
    expected = {n: fmpz_poly([]) for n in sizes}
    for k in range(1, limit+1):
        inner = outer[k] if k in outer else descent_row(k)
        for n in sizes:
            if k <= n:
                expected[n] += outer[n][k-1]*inner
    root = Path(__file__).resolve().parent / "results"
    if args.initial:
        path = args.archive or root / "family-rows.jsonl"
        with path.open() as stream:
            initial = list(map(json.loads, stream))
        if [row["n"] for row in initial] != list(range(126)):
            raise ValueError("Missing, duplicated or unexpected original row")
        for row in initial:
            n = row["n"]
            poly = fmpz_poly([1]) if n == 0 else fmpz_poly([0,1])*expected[n]
            check_initial(row, poly)
        print("Verified all coefficients and exact root certificates for rows 0 through 125.")
        return
    with gzip.open(args.archive or root / "large-rows.jsonl.gz", "rt") as stream:
        saved = list(map(json.loads, stream))
    if [row["n"] for row in saved] != list(sizes):
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
