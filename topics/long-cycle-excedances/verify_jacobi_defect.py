"""Check the finite examples in jacobi-defect.md with exact arithmetic."""

from fractions import Fraction
from itertools import permutations, zip_longest


def check(condition, message):
    if not condition:
        raise ArithmeticError(message)


def genuine_row(size):
    """Enumerate E_{size,3}/t directly from the permutation definition."""
    coefficients = [0] * (size - 1)
    for permutation in permutations(range(size)):
        remaining = set(range(size))
        while remaining:
            start = min(remaining)
            length = 1
            label = permutation[start]
            remaining.remove(start)
            while label != start:
                remaining.remove(label)
                label = permutation[label]
                length += 1
            if length < 3:
                break
        else:
            excedances = sum(label > index for index, label in enumerate(permutation))
            coefficients[excedances - 1] += 1
    return tuple(coefficients)


def evaluate(coefficients, argument):
    value = 0
    for coefficient in reversed(coefficients):
        value = value * argument + coefficient
    return value


def multiply(left, right):
    result = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i + j] += a * b
    return tuple(result)


def subtract(left, right):
    return tuple(a - b for a, b in zip_longest(left, right, fillvalue=0))


def quadratic(parameter):
    return (1, parameter, 1)


def check_lower_root(parameter, left, right):
    check(-1 < left < right < 0, "invalid bracket for the noncentral root")
    polynomial = quadratic(parameter)
    check(evaluate(polynomial, left) < 0 < evaluate(polynomial, right),
          f"wrong root signs for R_{parameter}")


def verify():
    rows = {size: genuine_row(size) for size in range(3, 8)}
    check(rows[3] == (1, 1) and rows[4] == quadratic(4)
          and rows[5] == multiply((1, 1), quadratic(10)), "unexpected genuine early rows")

    brackets = {
        4: (Fraction(-27, 100), Fraction(-26, 100)),
        9: (Fraction(-113, 1000), Fraction(-112, 1000)),
        10: (Fraction(-102, 1000), Fraction(-100, 1000)),
        11: (Fraction(-92, 1000), Fraction(-91, 1000)),
    }
    for parameter, (left, right) in brackets.items():
        check_lower_root(parameter, left, right)
    order = (4, 9, 10, 11)
    for earlier, later in zip(order, order[1:]):
        check(brackets[earlier][1] < brackets[later][0], "overlapping root brackets")

    # The remaining quadratic roots are reciprocal partners. The order of
    # the roots in (-1, 0) and the central root at -1 interlace the four rows.
    synthetic = multiply(quadratic(9), quadratic(11))
    check(synthetic == (1, 20, 101, 20, 1) and synthetic != rows[6],
          "synthetic and genuine rows must be distinct")
    left, right = brackets[11]
    check(subtract(quadratic(9), quadratic(11)) == (0, -2, 0),
          "wrong second factor in the derivative of the synthetic row")
    check(subtract(rows[4], quadratic(11)) == (0, -7, 0),
          "wrong genuine residual row at the synthetic root")
    # The lag coefficient is binom(6, 2) = 15. The numerator of the
    # residue is at least 15*7*(1+left), and the denominator is positive.
    numerator = 105 * (1 + left)
    denominator = 2 * (1 - left) * (11 + 2 * right)
    check(numerator > 4 * denominator > 0, "synthetic residue bound failed")

    canonical = (Fraction(3, 25), Fraction(6, 5), 1)
    check(subtract(multiply((25, 1), rows[5]), rows[6])
          == tuple(200 * coefficient for coefficient in canonical) + (0, 0),
          "wrong monic Euclidean predecessor of the genuine row")
    check(subtract(rows[4], quadratic(10)) == (0, -6, 0),
          "wrong genuine predecessor value at the first pole")
    check(subtract(canonical, (0, 0, Fraction(22, 25)))
          == tuple(Fraction(3, 25) * coefficient for coefficient in quadratic(10)),
          "wrong canonical predecessor value at the first pole")
    check(Fraction(75, 11) / abs(brackets[10][0]) > 60, "genuine weight ratio bound failed")

    factor = (1, 91, 386, 91, 1)
    check(multiply((1, 1), factor) == rows[7], "wrong noncentral factor of the genuine row")
    left, right = Fraction(-1, 4), Fraction(-1, 5)
    check(evaluate(factor, left) == Fraction(245, 256)
          and evaluate(factor, right) == Fraction(-1554, 625), "wrong marked-length bracket")
    check(1 + 4 * left + right**2 > 0 and 1 + 10 * right + left**2 < 0,
          "wrong bounds for the length-four and length-five factors")
    print("Verified five genuine rows, the synthetic ratio > 4, the genuine weight ratio > 60,")
    print("and opposite signs for the length-four and length-five marked terms.")


if __name__ == "__main__":
    verify()
