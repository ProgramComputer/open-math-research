"""Certify the first nonzero cycle-lag pairs using exact dyadic signs."""

import argparse
from fractions import Fraction
from gzip import GzipFile
import json
from math import comb
from pathlib import Path
from runpy import run_path

TOPIC = Path(__file__).resolve().parent
ARCHIVE = TOPIC / "first-lag-prefix.jsonl.gz"
LIMIT = 200

bracket_helpers = run_path(str(TOPIC / "verify_threshold_three.py"))
as_float = bracket_helpers["as_float"]
dyadic = bracket_helpers["dyadic"]
find_brackets = bracket_helpers["find_brackets"]
sign_at = bracket_helpers["sign_at"]
smaller = bracket_helpers["smaller"]
eulerian_rows = run_path(str(TOPIC / "verify_cycle_deletions.py"))["eulerian_rows"]
add_product = run_path(str(TOPIC / "verify.py"))["add_product"]


def pencils(rows, k):
    new_single = rows[2 * k - 1]
    lag = [0] * len(new_single)
    add_product(lag, rows[k - 1], rows[k - 1], comb(2 * k - 1, k - 1))
    return tuple([a + sign * b for a, b in zip(new_single, lag)] for sign in (1, -1))


def certify(k, old, new, bounds):
    for row, size in zip((old, *new), (2 * k - 2, 2 * k - 1, 2 * k - 1)):
        if len(row) != size or row[0] != 1 or row != row[::-1]:
            raise ArithmeticError(f"Wrong degree, endpoints or reciprocity at k={k}")
    if len(bounds) != k - 2 or sum(a * (-1)**j for j, a in enumerate(old)):
        raise ArithmeticError(f"Wrong old root count at k={k}")
    target = (-1)**(k - 1)
    if any(target * sum(a * (-1)**j for j, a in enumerate(row)) <= 0 for row in new):
        raise ArithmeticError(f"Wrong pencil sign at -1 for k={k}")
    old, plus, minus = ([0] + row for row in (old, *new))
    previous_right = None
    for h, (left, right) in enumerate(bounds, 1):
        if not smaller(left, right) or (previous_right and not smaller(previous_right, left)):
            raise ArithmeticError(f"Wrong interval order at {(k, h)}")
        target = (-1)**h
        if (sign_at(old, left), sign_at(old, right)) != (-target, target):
            raise ArithmeticError(f"Wrong old signs at {(k, h)}")
        if any(sign_at(row, endpoint) != target for row in (plus, minus)
               for endpoint in (left, right)):
            raise ArithmeticError(f"Wrong pencil signs at {(k, h)}")
        previous_right = right


def generate(rows, last):
    previous = []
    for m in range(2, 2 * last - 1):
        # The shared bracket finder expects the degree-m row t A_m(t).
        old = [0] + rows[m]
        bounds = find_brackets(m + 1, old, previous)
        if m >= 4 and m % 2 == 0:
            k = m // 2 + 1
            new = pencils(rows, k)
            plus, minus = ([0] + row for row in new)
            for index, (left, right) in enumerate(bounds):
                target = (-1)**(index + 1)
                # Refine the old sign change until stable pencil signs hold.
                while any(sign_at(row, p) != target for row in (plus, minus)
                          for p in (left, right)):
                    mid = dyadic((as_float(left) + as_float(right)) / 2)
                    if not smaller(left, mid) or not smaller(mid, right):
                        raise ArithmeticError(f"Could not refine bracket at {(k, index + 1)}")
                    if sign_at(old, mid) == target:
                        right = mid
                    else:
                        left = mid
                bounds[index] = [left, right]
            certify(k, rows[m], new, bounds)
            yield {"k": k, "brackets": bounds}
        previous = bounds


def interval_horner(row, lo, hi):
    low = high = Fraction(row[-1])
    for coefficient in reversed(row[:-1]):
        values = (lo * low, hi * low, lo * high, hi * high)
        low = coefficient + min(values)
        high = coefficient + max(values)
    return low, high


def certify_variation(rows):
    lo, hi = Fraction(-3583, 50000), Fraction(-1433, 20000)
    old, new_single = rows[8], rows[9]
    left = interval_horner(old, lo, lo)[0]
    right = interval_horner(old, hi, hi)[0]
    if left * right >= 0 or interval_horner(new_single, lo, hi)[0] <= 11:
        raise ArithmeticError("Wrong Eulerian signs in total variation example")
    row = new_single.copy()
    add_product(row, rows[4], rows[4], 20 * comb(9, 4))
    if interval_horner(row, lo, hi)[1] >= -1:
        raise ArithmeticError("Wrong lag sign in total variation example")
    if Fraction(comb(9, 4) * sum(rows[4])**2, sum(old)) != Fraction(9, 5):
        raise ArithmeticError("Wrong signed sum in total variation example")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="create a new certificate")
    parser.add_argument("--archive", type=Path, default=ARCHIVE)
    parser.add_argument("--through", type=int, default=LIMIT)
    args = parser.parse_args()
    if not 3 <= args.through <= LIMIT:
        parser.error(f"threshold limit must be between 3 and {LIMIT}")
    rows = eulerian_rows(max(9, 2 * args.through - 1))
    certify_variation(rows)
    count = 0
    with args.archive.open("xb" if args.write else "rb") as raw:
        with GzipFile(filename="", fileobj=raw, mode="wb" if args.write else "rb",
                      **({"mtime": 0} if args.write else {})) as stream:
            if args.write:
                for record in generate(rows, args.through):
                    stream.write((json.dumps(record, separators=(",", ":")) + "\n").encode())
                    count += len(record["brackets"])
            else:
                for k in range(3, args.through + 1):
                    record = json.loads(stream.readline())
                    if record["k"] != k:
                        raise ArithmeticError(f"Wrong threshold record at k={k}")
                    bounds = record["brackets"]
                    certify(k, rows[2 * k - 2], pencils(rows, k), bounds)
                    count += len(bounds)
                if args.through == LIMIT and stream.read(1):
                    raise ArithmeticError("Unexpected additional records")
    print(f"Certified {args.through - 2} thresholds, {count} dyadic brackets, "
          "and the total variation obstruction.")


if __name__ == "__main__":
    main()
