#!/usr/bin/env python3
"""Independently check the archived bracket polynomial signs with exact integers."""

import argparse
import csv
from fractions import Fraction
import gzip
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent


def dyadic(encoded):
    mantissa, exponent = encoded.split("p")
    whole, _, fractional = mantissa.partition(".")
    numerator = int(whole + fractional, 16)
    return Fraction(numerator) * Fraction(2)**(int(exponent) - 4 * len(fractional))


def parity_sums(w, d, coefficients):
    x = w**d
    s = x.denominator.bit_length() - 1
    if 2**s != x.denominator:
        raise ValueError("Expected a dyadic endpoint")
    degree = len(coefficients) - 1
    num_power = 1
    even = odd = 0
    for j, coefficient in enumerate(coefficients):
        term = (coefficient * num_power) << (s * (degree - j))
        if j % 2:
            odd += term
        else:
            even += term
        num_power *= x.numerator
    return even, odd, s * degree


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", nargs="?", type=Path, default=HERE / "replay.csv.gz")
    args = parser.parse_args()
    count = 0
    with gzip.open(HERE.parent / "screen-angular-signs.jsonl.gz", "rt", encoding="utf-8") as archive:
        with gzip.open(args.certificate, "rt", encoding="utf-8", newline="") as certificate:
            rows = csv.DictReader(certificate)
            for line in archive:
                case = json.loads(line)
                if case["type"] != "case":
                    continue
                coefficients = case["coefficients"]
                n, d, r = (case[key] for key in ("n", "d", "r"))
                for k, _, _, sign in case["nodes"]:
                    row = next(rows)
                    if tuple(int(row[key]) for key in ("n", "d", "r", "k", "sign")) != (n, d, r, k, sign):
                        raise ValueError(f"Unexpected certificate row for {(n, d, r, k)}")
                    lo, hi = dyadic(row["lo"]), dyadic(row["hi"])
                    if not 0 < lo < hi:
                        raise ValueError(f"Invalid dyadic bracket for {(n, d, r, k)}")
                    ev_lo, od_lo, scale_lo = parity_sums(lo, d, coefficients)
                    ev_hi, od_hi, scale_hi = parity_sums(hi, d, coefficients)
                    scale = max(scale_lo, scale_hi)
                    lower = (ev_lo << (scale - scale_lo)) - (od_hi << (scale - scale_hi))
                    upper = (ev_hi << (scale - scale_hi)) - (od_lo << (scale - scale_lo))
                    if (sign > 0 and lower <= 0) or (sign < 0 and upper >= 0):
                        raise ArithmeticError(f"Could not establish whole-bracket sign for {(n, d, r, k)}")
                    count += 1
            if next(rows, None) is not None or count != 9162:
                raise ValueError(f"Unexpected certificate inventory after {count} nodes")
    print(f"Verified {count} whole-bracket polynomial signs using exact dyadic arithmetic")


if __name__ == "__main__":
    main()
