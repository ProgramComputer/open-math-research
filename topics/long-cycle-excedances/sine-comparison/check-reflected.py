"""Exact principal budgets from eleven reflected terms and a telescoping tail."""
from fractions import Fraction as F
from math import factorial
from pathlib import Path


def log_budget(h, amplitude):
    start = 12
    head = sum(
        (F(1, t) + F(1, t + 1)) / (1 + h * t * (t + 1))**96
        for t in range(1, start)
    )
    tail = 1 / (h * start**2 * (1 + h * start * (start + 1))**95)
    return (1 + head + tail) / (2 * amplitude)


def main():
    million = 10**6
    for aspect, h, amplitude, eta in (
        (10, F(1, 405), F(109, 10), F(1, 10)),
        (48, F(1, 1940), F(227, 100), F(4, 5)),
    ):
        y = F(1, aspect) - F(1, 10000)
        assert 40*h <= y and amplitude <= F(5477, 50)*y
        upper = log_budget(h, amplitude)
        assert upper < eta
        print("aspect at most", aspect, "logarithm norm <",
              (upper.numerator * million // upper.denominator) + 1, "/1000000")
    # The positive series and a geometric remainder certify these rational exponential bounds.
    for x, cap in ((F(1, 10), F(10, 9)), (F(4, 5), F(1113, 500)), (F(18, 5), F(110, 3))):
        trunc = 24
        upper = sum(x**m / factorial(m) for m in range(trunc))
        upper += x**trunc / factorial(trunc) / (1 - x/(trunc + 1))
        assert upper < cap
    assert sum(F(1, m) for m in range(1, 21)) < F(18, 5)
    # Rows in this reviewed table have four *upward* rounded error costs.
    table = Path(__file__).with_name("carrier-output.txt")
    expected = [(4, 6), (6, 10), (10, 16), (16, 22), (22, 28),
                (28, 34), (34, 40), (40, 44), (44, 48)]
    rows = [list(map(int, line.split())) for line in table.read_text().splitlines()]
    assert [(row[0], row[1]) for row in rows] == expected
    for lower, upper, _, _, first, other, regular, atom, _ in rows:
        carrier = F(54, 55) if upper <= 10 else F(6000, 12243)
        costs = F(first + other + regular + atom, million)
        margin = carrier - costs
        assert margin > F(325, 1000)
        print("aspect", lower, upper, "scaled determinant >", int(million*margin), "/1000000")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("run with assertions enabled")
    main()
