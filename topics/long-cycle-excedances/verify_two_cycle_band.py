#!/usr/bin/env python3
"""Exact certificates for both insertion signs in the finite two-cycle band."""
from argparse import ArgumentParser
from contextlib import ExitStack
from gzip import GzipFile
from hashlib import sha256
from json import dumps
from math import comb
from pathlib import Path

from flint import fmpz_poly


GRID_BITS = 256
ONE = 1 << GRID_BITS
T = fmpz_poly([0, 1])
WORK_BITS = 256


def check(condition, message):
    if not condition:
        raise ArithmeticError(message)


def eulerian_rows(last):
    """A_m uses excedance/descent exponents 0 through m-1."""
    rows = [fmpz_poly([1]), fmpz_poly([1])]
    for m in range(1, last):
        row = tuple(map(int, rows[-1].coeffs()))
        padded = (0, *row, 0)
        rows.append(fmpz_poly([
            (h + 1) * padded[h + 1] + (m + 1 - h) * padded[h]
            for h in range(m + 1)
        ]))
    for m in range(1, last + 1):
        powers = [v**m for v in range(m + 1)]
        signed_binomials = [(-1)**j * comb(m + 1, j) for j in range(m + 1)]
        finite_differences = [
            sum(signed_binomials[j] * powers[h + 1 - j] for j in range(h + 1))
            for h in range(m)
        ]
        check(rows[m] == fmpz_poly(finite_differences),
              f"Eulerian recurrence and finite differences disagree at m={m}")
    return rows


def original_row(n, k, eulerian):
    """Reconstruct E_{n,k}/t from the cycle containing label one."""
    check(k <= n < 3 * k, f"outside one- or two-cycle regime {(n, k)}")
    two_cycles = fmpz_poly()
    for length in range(k, n - k + 1):
        two_cycles += comb(n - 1, length - 1) * (
            eulerian[length - 1] * eulerian[n - length - 1]
        )
    return eulerian[n - 1] + T * two_cycles


class Signs:
    def __init__(self, polynomial, degree):
        self.coefficients = tuple(map(int, polynomial.coeffs()))
        self.degree = degree
        check(len(self.coefficients) == degree + 1, "wrong polynomial degree")
        check(self.coefficients[0] == 1 and self.coefficients == self.coefficients[::-1],
              "wrong extreme coefficients or reciprocity")
        self.at_one = sum((-1)**j * a for j, a in enumerate(self.coefficients))
        self.scaled = tuple(a << WORK_BITS for a in reversed(self.coefficients))

    def __call__(self, numerator):
        """Certify the sign of P(-numerator / 2**GRID_BITS) using only integers."""
        if numerator == 0:
            return 1
        if numerator == ONE:
            return (self.at_one > 0) - (self.at_one < 0)
        check(0 < numerator < ONE, "outside the dyadic unit interval")
        scaled = self.scaled
        # Each signed Horner step's rounding error is less than one scaled unit.
        # All later multiplications by the argument have magnitude less than one.
        for _ in range(9):
            it = iter(scaled)
            value = next(it)
            for coefficient in it:
                value = coefficient - ((numerator * value) >> GRID_BITS)
            if abs(value) > self.degree:
                return (value > 0) - (value < 0)
            scaled = tuple(coefficient << 64 for coefficient in scaled)
        raise ArithmeticError("could not certify a dyadic endpoint sign")


def refine_and_transfer(old, pencils, brackets, location):
    """Certify the old brackets and put all next lower roots in the gaps."""
    check(len(brackets) == old.degree // 2, f"wrong old bracket count at {location}")
    if old.degree % 2:
        check(old(ONE) == 0, f"missing old central root at {location}")
        target = (-1)**(len(brackets) + 1)
        check(all(pencil(ONE) == target for pencil in pencils),
              f"wrong pencil central signs at {location}")
    else:
        check(all(pencil(ONE) == 0 for pencil in pencils),
              f"missing pencil central roots at {location}")

    refined = []
    following = []
    previous_right = 0
    for rank, (left, right) in enumerate(brackets, 1):
        target = (-1)**rank
        check(0 <= left < right <= ONE and previous_right <= left,
              f"overlapping old brackets at {location}, rank {rank}")
        check(old(left) == -target and old(right) == target,
              f"wrong old endpoint signs at {location}, rank {rank}")

        def correct(endpoint):
            return all(pencil(endpoint) == target for pencil in pencils)

        left_correct = correct(left)
        right_correct = correct(right)
        while not (left_correct and right_correct):
            middle = (left + right) // 2
            check(left < middle < right,
                  f"dyadic grid exhausted at {location}, rank {rank}")
            middle_sign = old(middle)
            if middle_sign == target:
                right = middle
                right_correct = correct(right)
            else:
                check(middle_sign == -target, f"wrong midpoint sign at {location}, rank {rank}")
                left = middle
                left_correct = correct(left)

        check(previous_right < left, f"empty pencil gap at {location}, rank {rank}")
        refined.append((left, right))
        following.append((previous_right, left))
        previous_right = right

    if old.degree % 2:
        check(previous_right < ONE, f"empty pencil central gap at {location}")
        following.append((previous_right, ONE))
    check(len(following) == (old.degree + 1) // 2, f"wrong pencil root count at {location}")
    return refined, following


def independent_eulerian_brackets(eulerian, last):
    """Start with A_1=1 and locate each Eulerian family row by exact signs."""
    brackets = {1: []}
    old = Signs(eulerian[1], 0)
    for m in range(1, last):
        new = Signs(eulerian[m + 1], m)
        _, brackets[m + 1] = refine_and_transfer(old, (new,), brackets[m], f"A_{m}")
        old = new
    return brackets


def json_bytes(value):
    return dumps(value, separators=(",", ":")).encode("ascii")


def write_record(stream, full, n, k, old, plus, minus, old_brackets, next_brackets):
    checked_data = {
        "old_coefficients": old.coefficients,
        "positive_pencil_coefficients": plus.coefficients,
        "negative_pencil_coefficients": minus.coefficients,
        "old_brackets": old_brackets,
        "next_brackets": next_brackets,
    }
    record = {
        "n": n,
        "k": k,
        "old_degree": old.degree,
        "checked_old_roots": old.degree,
        "grid_bits": GRID_BITS,
        "insertion_identity": True,
        "positive_lag_sign": True,
        "negative_lag_sign": True,
        "strict_interlacing": True,
        "old_at_minus_one_sign": (old.at_one > 0) - (old.at_one < 0),
        "positive_pencil_at_minus_one_sign": (plus.at_one > 0) - (plus.at_one < 0),
        "negative_pencil_at_minus_one_sign": (minus.at_one > 0) - (minus.at_one < 0),
    }
    record.update({f"{key}_sha256": sha256(json_bytes(value)).hexdigest()
                   for key, value in checked_data.items()})
    if full:
        record.update(checked_data)
    stream.write(json_bytes(record) + b"\n")


def verify(first_k, last_k, last_old, records, full_records):
    eulerian = eulerian_rows(last_old)
    base_brackets = independent_eulerian_brackets(eulerian, 2 * last_k - 2)
    tested = roots = 0
    for k in range(first_k, last_k + 1):
        brackets = base_brackets[2 * k - 2]
        old_polynomial = original_row(2 * k - 1, k, eulerian)
        old = Signs(old_polynomial, 2 * k - 3)
        digest = sha256()
        covered = checked_roots = 0
        for n in range(2 * k - 1, min(last_old, 3 * k - 2) + 1):
            actual = original_row(n + 1, k, eulerian)
            lag = comb(n, k - 1) * (T * eulerian[k - 1] * eulerian[n - k])
            plus = Signs(actual, n - 1)
            minus = Signs(actual - 2 * lag, n - 1)
            # Independently check the polynomial insertion identity at every pair.
            t = T
            derivative_part = t * (1 - t) * old_polynomial.derivative()
            drift_part = (1 + (n - 1) * t) * old_polynomial
            check(actual == derivative_part + drift_part + lag, f"wrong insertion formula {(n, k)}")
            refined, brackets = refine_and_transfer(old, (plus, minus), brackets, (n, k))
            if n >= 2 * k:
                covered += 1
                checked_roots += n - 2
                digest.update(repr((n, brackets)).encode("ascii"))
                if records is not None:
                    write_record(records, full_records, n, k, old, plus, minus, refined, brackets)
            old_polynomial = actual
            old = plus
        tested += covered
        roots += checked_roots
        print(f"k={k}: {covered} pairs, {checked_roots} old roots, {digest.hexdigest()}", flush=True)

    eligible_degrees = [
        n - 2
        for n in range(6, last_old + 1)
        for k in range(first_k, last_k + 1)
        if 2 * k <= n <= 3 * k - 2
    ]
    check(tested == len(eligible_degrees) and roots == sum(eligible_degrees),
          "incomplete requested range")
    print(f"Certified {tested} consecutive pairs and both insertion signs at "
          f"{roots} old roots, including reciprocal partners.", flush=True)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--first-k", type=int, default=3)
    parser.add_argument("--last-k", type=int)
    parser.add_argument("--last-old", type=int, default=191)
    parser.add_argument("--records", type=Path, help="write a gzip JSONL index of certified pairs")
    parser.add_argument("--full-records", action="store_true",
                        help="include coefficients and dyadic brackets in each record")
    args = parser.parse_args()
    if args.full_records and args.records is None:
        parser.error("--full-records requires --records")
    last_k = args.last_k if args.last_k is not None else args.last_old // 2
    if not 6 <= args.last_old <= 191 or not 3 <= args.first_k <= last_k <= args.last_old // 2:
        parser.error("require 6 <= last old size <= 191 and 3 <= first k <= last k <= floor(last old size/2)")
    with ExitStack() as stack:
        records = None
        if args.records is not None:
            raw = stack.enter_context(args.records.open("xb"))
            records = stack.enter_context(
                GzipFile(filename="", mode="wb", fileobj=raw, mtime=0)
            )
        verify(args.first_k, last_k, args.last_old, records, args.full_records)


if __name__ == "__main__":
    main()
