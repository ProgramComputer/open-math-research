"""Check strict alternation at rational separators for selected ordered-partition rows.

Python 3 with python-flint (tested with 0.9.0). The numerical root centers
only propose separators. All verdicts use integer polynomial evaluations.
"""
from fractions import Fraction
from math import comb
from flint import ctx, fmpz_poly


def count_rows(threshold, last):
    rows = [[1]]
    for n in range(1, last + 1):
        row = [0] * (1 + n // threshold)
        for size in range(1, n + 1):
            choices = comb(n, size)
            marked = int(size >= threshold)
            for k, ways in enumerate(rows[n - size]):
                row[k + marked] += choices * ways
        rows.append(row)
    return rows


def dyadic_midpoint(ball):
    mantissa, exponent = map(int, ball.mid().man_exp())
    return Fraction(mantissa << max(exponent, 0), 1 << max(-exponent, 0))


def search_centers(row):
    guesses = fmpz_poly(row).complex_roots()
    if any(degree != 1 for _, degree in guesses):
        raise ArithmeticError("root proposal did not find distinct centers")
    return [dyadic_midpoint(-value.real) for value, _ in guesses]


def sign(row, point):
    if point is None:
        return (-1) ** (len(row) - 1)
    numerator, denominator = point.as_integer_ratio()
    value = row[-1]
    factor = 1
    for coefficient in reversed(row[:-1]):
        factor *= denominator
        value = coefficient * factor - numerator * value
    return (value > 0) - (value < 0)


def certify(old, new):
    m = len(old) - 1
    carry = len(new) - len(old)
    centers = sorted(search_centers(old) + search_centers(new))
    cuts = [Fraction(0)] + [(a + b) / 2 for a, b in zip(centers, centers[1:])] + [None]
    old_sign = new_sign = 1
    if len(cuts) - 1 != 2 * m + carry or any(c <= 0 for c in centers):
        raise ArithmeticError("degree or sign mismatch in proposed centers")
    if any(a >= b for a, b in zip(cuts[:-2], cuts[1:-1])):
        raise ArithmeticError("proposed rational separators were not strictly ordered")
    for index, cut in enumerate(cuts):
        if (sign(old, cut), sign(new, cut)) != (old_sign, new_sign):
            raise ArithmeticError(f"exact comparison failed at separator {index}")
        if index % 2 == carry:
            old_sign = -old_sign
        else:
            new_sign = -new_sign
    # IVT gives one distinct negative root per sign-changing interval for
    # each reversed polynomial. The two degree counts exhaust all zeros.
    return len(cuts) - 1


def main():
    ctx.prec = 100
    total = 0
    for j, m in [(3, 24), (5, 28), (9, 32), (15, 22), (19, 13)]:
        all_rows = count_rows(j, j * (m + 1))
        for s in (0, j // 2, j - 1):
            n = m * j + s
            old, new = (all_rows[n + i][::-1] for i in range(2))
            certified = certify(old, new)
            total += certified
            print(f"j={j:2}  n={n:3}  old degree={m:2}  new degree={len(new)-1:2}"
                  f"  certified sign-changing intervals={certified}")
    print(f"15 consecutive pairs, {total} disjoint sign-changing intervals across the pairs.")


if __name__ == "__main__":
    main()
