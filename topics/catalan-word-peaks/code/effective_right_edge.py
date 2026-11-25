"""Exact finite interface for the Catalan strict-peak right-edge theorem."""

from fractions import Fraction as Q
from math import comb
import json
from pathlib import Path
import sys

from flint import fmpq_poly, fmpz_poly


def coefficient_row(n):
    if not n:
        return fmpz_poly([1])
    coefficients = []
    for k in range((n-1)//2+1):
        numerator = comb(n-k, k)*comb(2*n-3*k, n-2*k-1)
        entry, remainder = divmod(numerator, n-k)
        if remainder:
            raise ArithmeticError((n, k, "nonintegral coefficient"))
        coefficients.append(entry)
    return fmpz_poly(coefficients)(fmpz_poly([-1, 1]))


def generated_rows(last):
    t = fmpz_poly([0, 1])
    rows = [fmpz_poly([1])]
    square = []
    for n in range(1, last+1):
        square.append(sum((rows[i]*rows[n-1-i] for i in range(n)), fmpz_poly([])))
        row = square[-1]
        if n >= 2:
            row += (1-t)*(rows[n-2]-square[n-2])
        rows.append(row)
    return rows


def negative_primitive_remainder(left, right):
    remainder = (-(fmpq_poly(left) % fmpq_poly(right))).numer()
    return remainder // remainder.content() if remainder else remainder


def oriented_pair(old, new):
    if new.degree() == 0:
        return True
    a = new
    b = old if old.degree() < new.degree() else -negative_primitive_remainder(old, new)
    while b:
        if b.degree() != a.degree()-1 or b.leading_coefficient() <= 0:
            return False
        a, b = b, negative_primitive_remainder(a, b)
    return a.degree() == 0


def margins():
    d = Q(799, 800)
    if not (5*Q(2, 3)**9 < Q(19, 100) and 5*Q(2, 3)**9 < 2**9/Q(120)):
        raise ArithmeticError("Exterior sign margins failed")
    if not all((1+x*x)**2-Q(18, 5)*x < -Q(1, 8) for x in (Q(9, 20), Q(1, 2))):
        raise ArithmeticError("Horizontal slit interval failed")
    if not (d*d/3 > Q(57, 100)**2 and 1+2*d > Q(5, 3)**2
            and 2*d*d*(1+d)/Q(26, 5) > Q(19, 25)
            and Q(16, 27) < Q(39, 50)**2):
        raise ArithmeticError("Vertical chord parameter bounds failed")
    if not (Q(19, 15)**80 > 3600*80**2 and Q(19, 15)*Q(80, 81)**2 > 1
            and 5*Q(38, 75)**80 < 1):
        raise ArithmeticError("Vertical chord endpoint sign failed")
    e = Q(13, 25)**80
    if not (Q(19, 100)-5*e > Q(1, 10)
            and Q(5, 80**2)+Q(21, 20)*e < Q(1, 2)
            and Q(19, 1000) > 5*e*(Q(13, 25)+Q(11, 10))):
        raise ArithmeticError("Derivative and consecutive-value margins failed")


def main():
    margins()
    archive = Path(sys.argv[1]) if len(sys.argv) > 1 else (
        Path(__file__).resolve().parents[1]/"results"/"family-rows.jsonl"
    )
    with archive.open() as stream:
        checked = {r["n"]: r["coefficients"] for line in stream if (r := json.loads(line))}
    rows = generated_rows(80)
    translate = fmpq_poly([-11, 16], 16)
    for n, row in enumerate(rows):
        if list(map(int, row)) != checked[n] or row != coefficient_row(n):
            raise ArithmeticError(f"Independent coefficient methods disagree at row {n}")
        if n < 9 and any(c <= 0 for c in fmpq_poly(row)(translate)):
            raise ArithmeticError(f"Positive translate failed at row {n}")
        if n and not oriented_pair(rows[n-1], row):
            raise ArithmeticError(f"Strict oriented pair failed at row {n}")
    print("Verified 9 positive translates, 81 exact rows, and 80 strict oriented pairs.")


if __name__ == "__main__":
    main()
