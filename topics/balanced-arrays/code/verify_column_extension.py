"""Check the finite symbols and the sharp seven-row obstruction."""
import argparse
import gzip
import json
import sys
from fractions import Fraction
from functools import cache
from math import comb, lcm, perm
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.append(str(HERE.parents[2] / "shared" / "python"))
from coefficients import column_count, special_count
from roots import root_report


def require(condition, message):
    if not condition:
        raise ValueError(message)


def derivatives(coefficients, point):
    return [
        sum(c * perm(j, order) * point ** (j - order)
            for j, c in enumerate(coefficients) if j >= order)
        for order in range(3)
    ]


def check_uniform_bound():
    t = 15
    point = Fraction(57, 100)
    eps = 6 * Fraction(559872, 823543) ** t
    coeffs = [comb(6, k) * comb(7, k) for k in range(5, -1, -1)]
    require(0 < eps < 1 and 2 * Fraction(5, 6) ** 6 < 1, "tail monotonicity")
    bounds = [
        c * k * comb(7*t, t) * Fraction(k, 7) ** (6*t)
        * Fraction(7-k, 7) ** t / (1-eps)
        for c, k in zip(coeffs, range(5, -1, -1))
    ]
    a, b, c = derivatives(coeffs, -point)
    ea, eb, ec = derivatives(bounds, point)
    require(a > ea and c > ec, "positive value and second derivative")
    require((abs(b) + eb) ** 2 < (a-ea) * (c-ec), "strict Laguerre bound")


@cache
def row(n, r, d):
    coefficients = []
    for k in range(n*r//d + 1):
        exact = special_count(n, k, r, d)
        coefficients.append(column_count(n, k, r, d) if exact is None else exact)
    return coefficients


def check_records(filename, keys, recount):
    with gzip.open(HERE.parent / "results" / filename, "rt", encoding="utf-8") as stream:
        records = [json.loads(line) for line in stream]
    require([(record["n"], record["r"], record["d"]) for record in records] == keys,
            f"incomplete or unordered record range in {filename}")
    for record, (n, r, d) in zip(records, keys):
        left, right = record["left"], record["right"]
        m, degree = n*r//d, n*r//(d+1)
        require(len(left) == m+1 and len(right) == degree+1 and
                left[0] == right[0] == 1 and min(left + right) > 0, (n, r, d))
        if recount:
            require(left == row(n, r, d) and right == row(n, r, d+1),
                    f"coefficient mismatch at {(n, r, d)}")
        symbol = [Fraction(comb(m, k)*c, left[k]) for k, c in enumerate(right)]
        scale = lcm(*(x.denominator for x in symbol))
        report = root_report([int(scale * x) for x in symbol])
        if (n, r, d) == (7, 90, 105):
            require(report["squarefree_degree"] == 5 and report["distinct_real_roots"] == 3,
                    "three distinct real roots at t=15")
            a, b, c = derivatives(symbol[::-1], Fraction(-57, 100))
            require(b*b < a*c, "exact t=15 symbol Laguerre inequality")
        else:
            require(report["real_rooted"], f"nonreal zero at {(n, r, d)}")
            if filename == "column-extension-seven.jsonl.gz":
                require(report["distinct_real_roots"] == 5, "five distinct roots in prefix")
    print(f"Verified {len(records)} exact symbols from {filename}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--recount", action="store_true", help="recompute each input coefficient")
    args = parser.parse_args()
    check_uniform_bound()
    print("Verified the uniform rational Laguerre bound for t >= 15")
    check_records("column-extension-screen.jsonl.gz", [
        (n, r, d) for n in range(1, 16) for r in range(1, 6)
        for d in range(r, min(r+5, 8)+1)
    ], args.recount)
    check_records("column-extension-cap-two.jsonl.gz", [
        (n, 2, d) for n, last_d in [(16, 6), (20, 7), *[(n, 8) for n in range(24, 73, 6)]]
        for d in range(3, last_d + 1)
    ], args.recount)
    check_records("column-extension-seven.jsonl.gz",
                  [(7, 6*t, 7*t) for t in range(1, 16)], args.recount)


if __name__ == "__main__":
    main()
