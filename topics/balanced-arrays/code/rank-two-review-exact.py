from fractions import Fraction
from itertools import combinations, combinations_with_replacement
from math import factorial, gcd


class MarginCounts:
    """Counts for any one labeled margin vector in each permutation class."""

    def __init__(self, maximum_quota):
        self.margins = list(combinations_with_replacement(range(maximum_quota + 1), 4))
        self.indices = {margins: index for index, margins in enumerate(self.margins)}
        self.previous_rows = []
        supports = [(i,) for i in range(4)] + list(combinations(range(4), 2))
        for margins in self.margins:
            predecessors = []
            for support in supports:
                if all(margins[index] > 0 for index in support):
                    predecessor = list(margins)
                    for index in support:
                        predecessor[index] -= 1
                    predecessors.append(self.indices[tuple(sorted(predecessor))])
            self.previous_rows.append((margins[-1], sum(margins), predecessors))
        self.row_count = 0
        self.counts = [1] + [0] * (len(self.margins) - 1)

    def add_row(self, permit_empty):
        self.row_count += 1
        previous = self.counts
        self.counts = [0] * len(previous)
        for index, (largest, total, predecessors) in enumerate(self.previous_rows):
            if largest <= self.row_count and total <= 2 * self.row_count:
                self.counts[index] = sum(previous[j] for j in predecessors)
                if permit_empty:
                    self.counts[index] += previous[index]

    def balanced(self, quota):
        return self.counts[self.indices[(quota,) * 4]]


def primitive(polynomial):
    while polynomial and polynomial[-1] == 0:
        polynomial.pop()
    divisor = 0
    for coefficient in polynomial:
        divisor = gcd(divisor, coefficient)
        if divisor == 1:
            return polynomial
    if divisor:
        return [coefficient // divisor for coefficient in polynomial]
    return polynomial


def sign(value):
    return (value > 0) - (value < 0)


def negative_remainder(dividend, divisor):
    """A positive rational multiple of the negative Euclidean remainder."""
    remainder = dividend[:]
    leading = divisor[-1]
    while remainder and len(remainder) >= len(divisor):
        offset = len(remainder) - len(divisor)
        multiplier = sign(leading) * remainder[-1]
        remainder = [abs(leading) * coefficient for coefficient in remainder]
        for index, coefficient in enumerate(divisor, offset):
            remainder[index] -= multiplier * coefficient
        remainder = primitive(remainder)
    return [-coefficient for coefficient in remainder]


def variations(values):
    nonzero_signs = [sign(value) for value in values if value]
    return sum(left != right for left, right in zip(nonzero_signs, nonzero_signs[1:]))


def negative_root_count_and_gcd_degree(polynomial):
    sequence = [polynomial]
    if len(polynomial) > 1:
        sequence.append(primitive([index * coefficient for index, coefficient
                                   in enumerate(polynomial) if index]))
        while len(sequence[-1]) > 1:
            remainder = negative_remainder(sequence[-2], sequence[-1])
            if not remainder:
                break
            sequence.append(remainder)
    at_infinity = variations([row[-1] * (-1)**(len(row) - 1) for row in sequence])
    at_zero = variations([row[0] for row in sequence])
    return at_infinity - at_zero, len(sequence[-1]) - 1


def add(*polynomials):
    result = [Fraction(0)] * max(map(len, polynomials))
    for polynomial in polynomials:
        for index, coefficient in enumerate(polynomial):
            result[index] += coefficient
    while result and result[-1] == 0:
        result.pop()
    return result


def scale(factor, polynomial):
    return [factor * coefficient for coefficient in polynomial]


def multiply(*polynomials):
    result = [1]
    for polynomial in polynomials:
        product = [Fraction(0)] * (len(result) + len(polynomial) - 1)
        for i, left in enumerate(result):
            for j, right in enumerate(polynomial):
                product[i + j] += left * right
        result = product
    return result


def symbolic_fourth_moment(origin):
    """Return p4(n) in powers of n - origin."""
    counts = MarginCounts(4)
    coefficients = [[] for _ in range(5)]
    binomial = [1]
    for nonempty_rows in range(1, 17):
        counts.add_row(permit_empty=False)
        binomial = multiply(binomial, [Fraction(origin + 1 - nonempty_rows, nonempty_rows),
                                       Fraction(1, nonempty_rows)])
        for quota in range(1, 5):
            coefficient = counts.balanced(quota) * factorial(quota)**3
            coefficients[quota] = add(coefficients[quota], scale(coefficient, binomial))
    _, b1, b2, b3, b4 = coefficients
    return add(multiply(b1, b1, b1, b1), scale(-4, multiply(b1, b1, b2)),
               scale(2, multiply(b2, b2)), scale(4, multiply(b1, b3)), scale(-4, b4))


def main():
    polynomial = symbolic_fourth_moment(76)
    assert all(coefficient < 0 for coefficient in polynomial)
    print("Coefficients of p4(76+t), in ascending order:", *polynomial, flush=True)
    counts = MarginCounts(37)
    for row_count in range(76):
        polynomial = [counts.balanced(quota) * factorial(quota)**3
                      for quota in range(row_count // 2 + 1)]
        roots, gcd_degree = negative_root_count_and_gcd_degree(polynomial)
        degree = len(polynomial) - 1
        assert (roots == degree - gcd_degree) == (row_count <= 15), row_count
        if 12 <= row_count <= 17 or row_count == 75:
            print((row_count, degree, roots, gcd_degree), flush=True)
        if row_count < 75:
            counts.add_row(permit_empty=True)
    print("Checked 0 <= n <= 75 by exact Sturm sequences.")


if __name__ == "__main__":
    main()
