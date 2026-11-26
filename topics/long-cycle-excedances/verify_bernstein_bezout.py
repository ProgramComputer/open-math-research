"""Check finite Bernstein Bézout successes and an exact middle-slice failure."""

from fractions import Fraction
from math import comb, factorial, lcm


def add(left, right):
    result = [0] * max(len(left), len(right))
    for i, value in enumerate(left):
        result[i] += value
    for i, value in enumerate(right):
        result[i] += value
    return result


def multiply(left, right):
    result = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i + j] += a * b
    return result


def eulerian_rows(limit):
    rows = {1: [1]}
    for n in range(2, limit + 1):
        result = [0] * n
        for j, value in enumerate(rows[n - 1]):
            result[j] += (j + 1) * value
            result[j + 1] += (n - 1 - j) * value
        rows[n] = result
    return rows


def marked_rows(k, limit, eulerian):
    rows = {}
    for n in range(k, limit + 1):
        layers = [eulerian[n - 1]] + [[0] for _ in range(n // k - 1)]
        for length in range(k, n - k + 1):
            for j, remainder in enumerate(rows[n - length]):
                product = multiply(eulerian[length - 1], remainder)
                weighted = [0] + [comb(n - 1, length - 1) * c for c in product]
                layers[j + 1] = add(layers[j + 1], weighted)
        rows[n] = layers
    return rows


def bezout(q, p, size):
    q = q + [0] * (size + 1 - len(q))
    p = p + [0] * (size + 1 - len(p))
    result = [[0] * size for _ in range(size)]
    for i in range(1, size + 1):
        for j in range(i):
            difference = q[i] * p[j] - p[i] * q[j]
            for h in range(i - j):
                result[i - 1 - h][j + h] += difference
    return result


def bernstein_matrices(old, new, size):
    degree = len(old) + len(new) - 2
    matrices = [[[0] * size for _ in range(size)] for _ in range(degree + 1)]
    for i, p in enumerate(old):
        for j, q in enumerate(new):
            matrix = bezout(q, p, size)
            for h in range(i + j, degree + 1):
                # One common scaling by degree! keeps the matrices integral.
                multiplier = comb(h, i + j) * factorial(degree) // comb(degree, i + j)
                for row in range(size):
                    for col in range(size):
                        matrices[h][row][col] += multiplier * matrix[row][col]
    return matrices


def check_positive_definite(matrix):
    matrix = [row[:] for row in matrix]
    previous = 1
    for k in range(len(matrix)):
        pivot = matrix[k][k]
        if pivot <= 0:
            raise ArithmeticError(f"Nonpositive leading principal minor of order {k + 1}")
        for i in range(k + 1, len(matrix)):
            for j in range(i, len(matrix)):
                numerator = matrix[i][j] * pivot - matrix[i][k] * matrix[k][j]
                value, remainder = divmod(numerator, previous)
                if remainder:
                    raise ArithmeticError("Nonintegral fraction-free elimination")
                matrix[j][i] = matrix[i][j] = value
        previous = pivot


VECTOR = [12, -16, 23, -17, 20, -16, 17, -14, 14, -10, 4]
RANK = len(VECTOR)
PREFIX = 2 * RANK - 1


def eta(p):
    return Fraction(1, p) if p % 2 == 0 else Fraction(0)


def limiting_form():
    return sum(
        VECTOR[p - 1] * VECTOR[q - 1] * min(p, q) * (1 + eta(p) + eta(q))
        for p in range(1, RANK + 1)
        for q in range(1, RANK + 1)
    )


def eulerian_prefix(m):
    return [
        sum((-1) ** h * comb(m + 1, h) * (j + 1 - h) ** m for h in range(j + 1))
        if j < m else 0
        for j in range(PREFIX + 1)
    ]


def two_cycle_prefix(n, k):
    if not 2 * k <= n < 3 * k:
        raise ValueError("Expected exactly two cycle-count layers")
    single = eulerian_prefix(n - 1)
    double = [0] * (PREFIX + 1)
    eulerian = {length: eulerian_prefix(length - 1) for length in range(k, n - k + 1)}
    for length in range(k, n - k + 1):
        weight = comb(n - 1, length - 1)
        for i, left in enumerate(eulerian[length][:-1]):
            for j, right in enumerate(eulerian[n - length][:PREFIX - i]):
                double[i + j + 1] += weight * left * right
    return single, double


def bezout_entry(a, b, i, j):
    return sum(
        a[r] * b[i + j + 1 - r] - b[r] * a[i + j + 1 - r]
        for r in range(max(i, j) + 1, i + j + 2)
    )


def reversed_middle_block(n, k):
    p0, p1 = two_cycle_prefix(n, k)
    q0, q1 = two_cycle_prefix(n + 1, k)
    xp0 = [0] + p0
    xp1 = [0] + p1
    # Twice the middle Bernstein coefficient after reversing the monomial basis.
    return [
        [2 * bezout_entry(xp0, q0, i, j) + bezout_entry(xp1, q0, i, j)
         + bezout_entry(xp0, q1, i, j) for j in range(RANK)]
        for i in range(RANK)
    ]


def main():
    eulerian = eulerian_rows(49)
    pairs = [(n, k) for n in range(6, 35) for k in range(3, n // 2 + 1)]
    pairs.append((48, 21))
    count = 0
    rows_by_k = {}
    for n, k in pairs:
        if k not in rows_by_k:
            rows_by_k[k] = marked_rows(k, 49 if k == 21 else 35, eulerian)
        rows = rows_by_k[k]
        matrices = bernstein_matrices(rows[n], rows[n + 1], n - 1)
        for i, matrix in enumerate(matrices):
            try:
                check_positive_definite(matrix)
            except ArithmeticError as error:
                raise ArithmeticError((n, k, i)) from error
            count += 1
        if (n, k) == (21, 10):
            reversed_block = [
                [matrices[1][n - 2 - i][n - 2 - j] for j in range(RANK)]
                for i in range(RANK)
            ]
            if reversed_block != reversed_middle_block(n, k):
                raise ArithmeticError("Full and reversed truncated constructions differ")
    if len(pairs) != 226 or count != 1383:
        raise ArithmeticError("Wrong finite positive-check count")
    print("Positive definite Bernstein matrices for 225 consecutive pairs and (48, 21).", flush=True)

    if limiting_form() != Fraction(-5, 2):
        raise ArithmeticError("Wrong limiting quadratic form")
    n, k = 5376, 2560
    matrix = reversed_middle_block(n, k)
    scale = lcm(*range(1, RANK + 1))
    vector = [value * (scale // p) ** (n - 1) for p, value in enumerate(VECTOR, 1)]
    form = sum(vector[i] * vector[j] * matrix[i][j] for i in range(RANK) for j in range(RANK))
    if form >= 0:
        raise ArithmeticError(f"No negative middle Bernstein witness at {(n, k)}")
    print(f"Strictly negative middle Bernstein form at {(n, k)}.")


if __name__ == "__main__":
    main()
