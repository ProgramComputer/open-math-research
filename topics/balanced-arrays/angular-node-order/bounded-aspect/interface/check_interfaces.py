#!/usr/bin/env python3
"""Check archived angular brackets against geometric and dominance boundaries."""

from collections import Counter
import csv
from fractions import Fraction
import gzip
from hashlib import sha256
import json
from math import factorial
from pathlib import Path


ANGULAR = Path(__file__).resolve().parents[2]
COEFFICIENTS = ANGULAR / "screen-angular-signs.jsonl.gz"
BRACKETS = ANGULAR / "exact-node-signs" / "replay.csv.gz"
INPUT_HASHES = {
    COEFFICIENTS: "177524eb815024cc3fe761a2767abb05f18eadf395e36adf8a263969a8a56a23",
    BRACKETS: "163dfdd650e90b96e6c87fb7256679a3d7781603a311465122be99c3a017110a",
}


def dyadic(encoded):
    mantissa, exponent = encoded.split("p")
    whole, _, fractional = mantissa.partition(".")
    numerator = int(whole + fractional, 16)
    return Fraction(numerator) * Fraction(2)**(int(exponent) - 4 * len(fractional))


def relation(lo, hi, boundary, above):
    if above:
        if lo >= boundary:
            return "proved"
        if hi <= boundary:
            return "reversed"
    else:
        if hi <= boundary:
            return "proved"
        if lo >= boundary:
            return "reversed"
    return "unresolved"


def replay_archived_brackets():
    for path, expected in INPUT_HASHES.items():
        if sha256(path.read_bytes()).hexdigest() != expected:
            raise ValueError(f"Input hash mismatch for {path}")
    counts = Counter()
    failures = Counter()
    with gzip.open(COEFFICIENTS, "rt", encoding="utf-8") as archive:
        with gzip.open(BRACKETS, "rt", encoding="utf-8", newline="") as certificates:
            rows = csv.DictReader(certificates)
            for entry in map(json.loads, archive):
                if entry["type"] != "case":
                    continue
                a = entry["coefficients"]
                n, d, r = (entry[name] for name in ("n", "d", "r"))
                degree = len(a) - 1
                for k, *_ in entry["nodes"]:
                    row = next(rows)
                    if tuple(int(row[name]) for name in ("n", "d", "r", "k")) != (n, d, r, k):
                        raise ValueError(f"Mismatched certificate row at {(n, d, r, k)}")
                    lo, hi = dyadic(row["lo"])**d, dyadic(row["hi"])**d
                    if not 0 < lo < hi:
                        raise ValueError(f"Invalid bracket at {(n, d, r, k)}")
                    counts["angular brackets"] += 1
                    tests = [
                        ("lower dominance boundary", lo, hi, Fraction(a[k-1], a[k]), True),
                        ("upper dominance boundary", lo, hi, Fraction(a[k], a[k+1]), False),
                    ]
                    if k >= 2:
                        tests.append(("preceding geometric node", lo**2, hi**2, Fraction(a[k-2], a[k]), True))
                    if k+1 < degree:
                        tests.append(("following geometric node", lo**2, hi**2, Fraction(a[k], a[k+2]), False))
                    for name, lower, upper, target, above in tests:
                        outcome = relation(lower, upper, target, above)
                        counts[name, outcome] += 1
                        if outcome == "reversed" and "dominance" in name:
                            failures[d] += 1
            if next(rows, None) is not None:
                raise ValueError("Unexpected additional certificate rows")
    for key, value in counts.items():
        print(key, value)
    expected = {
        "angular brackets": 9162,
        ("lower dominance boundary", "proved"): 9025,
        ("upper dominance boundary", "proved"): 9026,
        ("lower dominance boundary", "reversed"): 137,
        ("upper dominance boundary", "reversed"): 136,
        ("preceding geometric node", "proved"): 8471,
        ("following geometric node", "proved"): 8471,
    }
    if counts != expected or failures != {2: 206, 3: 67}:
        raise ValueError("Unexpected replay summary")
    print(f"Dominance failures by dimension: {dict(sorted(failures.items()))}")


def check_rational_constants():
    n, d, r, k = 10**6, 250_000, 127_000, 500_000
    worst_neighbor_gap = Fraction(r, d) - Fraction(k+1, n)
    angular_hypothesis_gap = Fraction(r, d) - Fraction(k+3, n)
    assert n == 4*d and 0 < k-1 < k+1 < n*r//d and 0 < r < d
    assert 2*d*worst_neighbor_gap**2 > 30
    assert sum(Fraction(5**j, factorial(j)) for j in range(7)) > 100
    assert 30 < 2*d*angular_hypothesis_gap**2 < 32 and 3**8 < n
    assert Fraction(3, 1) / (1 - Fraction(1, n))**2 < 4
    assert sum(Fraction(9, 2)**j / factorial(j) for j in range(6)) > 50
    assert (1 - 4*Fraction(1, 50) - Fraction(1, 50)**2) / 4 > Fraction(9, 40)
    assert Fraction(10, 9) < Fraction(4, 3) < 4*Fraction(1, 3) + 4*Fraction(1, 81)
    print("Finite obstruction constants verified with exact rational arithmetic")


def check_sign_correct_reversal():
    n = 144
    a = [factorial(n)//(factorial(m)**2*factorial(n-2*m)) for m in range(n//2+1)]
    rational_square = Fraction(a[4], a[6])
    even = sum(a[m]*rational_square**(m//2) for m in range(0, len(a), 2))
    odd = sum(a[m]*rational_square**(m//2) for m in range(1, len(a), 2))
    angular_lower = Fraction(51, 4*(2*n+1))
    assert angular_lower**4 > rational_square
    assert even**2 < rational_square*odd**2
    print(f"Explicit reversal: w_4^2 > t_5 and P(-t_5) < 0 at (144, 2, 1), t_5^2={rational_square}")


if __name__ == "__main__":
    check_rational_constants()
    replay_archived_brackets()
    check_sign_correct_reversal()
