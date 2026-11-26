"""Verify the finite join for minimum cycle length three using dyadic signs."""
import argparse
from gzip import GzipFile
import json
from math import comb, exp, frexp, ldexp, log, log1p, pi, tan
from pathlib import Path

LIMIT = 401
ARCHIVE = Path(__file__).with_name("threshold-three-prefix.jsonl.gz")


def coefficient_rows(last):
    # Inserting the new maximum into an existing cycle, or removing its 3-cycle.
    rows = [[1], [], []]
    for n in range(3, last + 1):
        old = rows[-1]
        row = [0] * n
        for h, coefficient in enumerate(old):
            row[h] += h * coefficient
            row[h + 1] += (n - 1 - h) * coefficient
        factor = comb(n - 1, 2)
        for h, coefficient in enumerate(rows[n - 3]):
            row[h + 1] += factor * coefficient
            row[h + 2] += factor * coefficient
        rows.append(row)
        yield n, row


def sign_at(row, point):
    # Evaluate E(-x)/(-x). Round in each Horner step with absolute error < 1
    # in scaled units. Since 0 < x < 1 the total error is less than len(row).
    numerator, shift = point
    if not (isinstance(numerator, int) and isinstance(shift, int)
            and shift > 0 and 0 < numerator < (1 << shift)):
        raise ValueError("Expected an interior positive dyadic")
    bits = 16
    while bits <= 2048:
        acc = row[-1] << bits
        for coefficient in row[-2:0:-1]:
            acc = (coefficient << bits) - ((acc * numerator) >> shift)
        if abs(acc) > len(row):
            return 1 if acc > 0 else -1
        bits *= 2
    raise ArithmeticError("Indeterminate sign at certificate point")


def dyadic(value):
    mantissa, exponent = frexp(value)
    n = round(mantissa * 2**40)
    shift = 40 - exponent
    while not n % 2:
        n //= 2
        shift -= 1
    return [n, shift]


def as_float(point):
    return ldexp(point[0], -point[1])


def smaller(x, y):
    return (x[0] << y[1]) < (y[0] << x[1])


def root_guess(n, h):
    if h <= 0.36 * n**0.5:
        return n * log1p(1 / h)
    theta = pi * (h + 0.5) / (n + 1)
    for _ in range(4):
        s = pi / tan(theta)
        a = 1 / (1 + exp(s))
        theta = pi * (h + 0.5 + a + a * (1 - a) * s) / (n + 1)
    return pi / tan(theta)


def find_brackets(n, row, previous):
    bounds = []
    for h in range(1, (n - 2) // 2 + 1):
        left = (as_float(previous[h-2][1]) if h >= 2 else ldexp(1.0, -n-4))
        right = as_float(previous[h-1][0]) if h <= len(previous) else 1.0
        high, low = -log(left), -log(right)
        margin = 1 / (100 * n)
        guess = root_guess(n, h)
        target = (-1)**(h-1)
        if low + margin < guess < high - margin:
            trial = [dyadic(exp(-guess-margin)), dyadic(exp(-guess+margin))]
            if sign_at(row, trial[0]) == target and sign_at(row, trial[1]) == -target:
                bounds.append(trial)
                continue
        # Strict order with the previous row supplies an interval. The checker
        # below verifies both signs after generating and when replaying it.
        while high - low > margin:
            mid = (high + low) / 2
            if sign_at(row, dyadic(exp(-mid))) == target:
                high = mid
            else:
                low = mid
        bounds.append([dyadic(exp(-high)), dyadic(exp(-low))])
    return bounds


def certify(n, row, bounds, previous):
    if row[0] or row[1] != 1 or len(row) != n or row[1:] != row[:0:-1]:
        raise ArithmeticError(f"Wrong endpoint, degree or reciprocity at n={n}")
    count = (n - 2) // 2
    if len(bounds) != count:
        raise ArithmeticError(f"Wrong bracket count at n={n}")
    for h, (left, right) in enumerate(bounds, 1):
        if not smaller(left, right) or (h >= 2 and not smaller(bounds[h-2][1], left)):
            raise ArithmeticError(f"Overlapping row brackets at {(n,h)}")
        if (sign_at(row, left), sign_at(row, right)) != ((-1)**(h-1), (-1)**h):
            raise ArithmeticError(f"Inconsistent signs at {(n,h)}")
        if h <= len(previous) and not smaller(right, previous[h-1][0]):
            raise ArithmeticError(f"New root fails the right comparison at {(n,h)}")
        if h >= 2 and not smaller(previous[h-2][1], left):
            raise ArithmeticError(f"New root fails the left comparison at {(n,h)}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="create a new archive")
    parser.add_argument("--archive", type=Path, default=ARCHIVE)
    parser.add_argument("--through", type=int, default=LIMIT)
    args = parser.parse_args()
    if not 3 <= args.through <= LIMIT:
        parser.error(f"row limit must be between 3 and {LIMIT}")
    previous = []
    number = 0
    with args.archive.open("xb" if args.write else "rb") as raw:
        with GzipFile(filename="", fileobj=raw, mode="wb" if args.write else "rb",
                      **({"mtime": 0} if args.write else {})) as stream:
            for n, row in coefficient_rows(args.through):
                if args.write:
                    bounds = find_brackets(n, row, previous)
                else:
                    rec = json.loads(stream.readline())
                    if rec["n"] != n or rec["coefficients"] != row:
                        raise ArithmeticError(f"Coefficient record differs at n={n}")
                    bounds = rec["brackets"]
                certify(n, row, bounds, previous)
                if args.write:
                    rec = dict(n=n, coefficients=row, brackets=bounds)
                    stream.write((json.dumps(rec, separators=(",", ":"))+"\n").encode())
                previous = bounds
                number += len(bounds)
            if not args.write and args.through == LIMIT and stream.read(1):
                raise ArithmeticError("Extra archive record")
    print(f"Certified {args.through-2} rows, {args.through-3} consecutive pairs "
          f"and {number} interior dyadic brackets.")


if __name__ == "__main__":
    main()
