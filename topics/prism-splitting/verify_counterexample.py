"""Verify the prism-slice counterexamples with only the Python standard library."""

import argparse
from fractions import Fraction
from itertools import combinations
import json
from math import comb
from pathlib import Path


CERTIFICATE = Path(__file__).with_name("certificates") / "transport_split.json"
SEPARATOR = -850
INTERVALS = (
    (("-857", "-856"), ("-34", "-33"), ("-8", "-7"), ("-3", "-2"),
     ("-1", "-1/2"), ("-1/2", "-1/3"), ("-1/7", "-1/8"),
     ("-1/39", "-1/40"), ("-1/40", "0")),
    (("-839", "-838"), ("-57", "-56"), ("-11", "-10"), ("-4", "-3"),
     ("-2", "-1"), ("-1", "-1/2"), ("-1/3", "-1/4"),
     ("-1/10", "-1/11"), ("-1/56", "-1/57"), ("-1/57", "0")),
)


def count_box_slice(total, bounds):
    """Bounded compositions by inclusion-exclusion over all subsets."""
    dimension = len(bounds) - 1
    count = 0
    for omitted in range(len(bounds) + 1):
        for chosen in combinations(bounds, omitted):
            residual = total - sum(chosen) - omitted
            if residual >= 0:
                count += (-1) ** omitted * comb(residual + dimension, dimension)
    return count


def compute(a, columns):
    dimension = len(columns) - 1
    lattice = [count_box_slice(a * q, [c * q for c in columns]) for q in range(dimension + 1)]
    coefficients = [
        sum((-1) ** j * comb(dimension + 1, j) * lattice[q - j] for j in range(q + 1))
        for q in range(dimension + 1)
    ]
    while coefficients[-1] == 0:
        coefficients.pop()
    interior = [
        count_box_slice(a * q - len(columns), [c * q - 2 for c in columns])
        for q in (2, 3)
    ]
    return {
        "rows": [a, a],
        "columns": columns,
        "dimension": dimension,
        "lattice_counts": lattice,
        "hstar": coefficients,
        "interior_counts_at_2_and_3": interior,
    }


def evaluate(coefficients, value):
    result = 0
    for coefficient in reversed(coefficients):
        result = result * value + coefficient
    return result


def verify_intervals(coefficients, intervals):
    if len(intervals) != len(coefficients) - 1:
        raise AssertionError("the number of root intervals differs from the degree")
    previous = None
    for a, b in intervals:
        a, b = Fraction(a), Fraction(b)
        if (previous is not None and a < previous) or a >= b or b > 0:
            raise AssertionError("root intervals must be ordered, disjoint, and negative")
        if evaluate(coefficients, a) * evaluate(coefficients, b) >= 0:
            raise AssertionError("a root interval lacks a strict sign change")
        previous = b


def compute_certificate():
    first = compute(6, [1] * 10 + [2])
    following = compute(6, [1] * 12)
    p, q = first["hstar"], following["hstar"]
    for instance, intervals in zip((first, following), INTERVALS):
        verify_intervals(instance["hstar"], intervals)
        instance["root_intervals"] = [list(pair) for pair in intervals]

    p_at_separator = evaluate(p, SEPARATOR)
    shifted_q = [
        (-1) ** i * sum(q[j] * comb(j, i) * SEPARATOR ** (j - i) for j in range(i, len(q)))
        for i in range(len(q))
    ]
    if p[-1] != 1 or (len(p) - 1) % 2 != 1 or len(q) != len(p) + 1:
        raise AssertionError("unexpected polynomial degrees or leading signs")
    if p_at_separator <= 0 or min(shifted_q) <= 0:
        raise AssertionError("the proposed rational separator does not verify")

    next_first = compute(7, [1] * 12 + [2])
    next_following = compute(7, [1] * 14)
    for instance in (next_first, next_following):
        top, next_top = instance["interior_counts_at_2_and_3"]
        numerator = instance["hstar"]
        if top != 1 or top != numerator[-1] or next_top - (instance["dimension"] + 1) != numerator[-2]:
            raise AssertionError("interior counts disagree with the last two h*-coefficients")
    next_p, next_q = next_first["hstar"], next_following["hstar"]
    if min(next_p + next_q) <= 0 or len(next_p) + 1 != len(next_q) or next_p[-2] <= next_q[-2]:
        raise AssertionError("the proposed Vieta obstruction does not verify")

    return {
        "a6": {
            "original": first,
            "split": following,
            "separator": SEPARATOR,
            "original_at_separator": p_at_separator,
            "split_at_separator_minus_y": shifted_q,
        },
        "a7": {
            "original": next_first,
            "split": next_following,
            "next_leading_gap": next_p[-2] - next_q[-2],
        },
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--emit", action="store_true", help="print the computed certificate as JSON")
    args = parser.parse_args()
    computed = compute_certificate()
    if args.emit:
        print(json.dumps(computed, indent=2))
        return
    if CERTIFICATE.is_file() and json.loads(CERTIFICATE.read_text()) != computed:
        raise AssertionError("the stored certificate differs from exact recomputation")
    print("Verified a=6 root separation and a=7 Vieta obstruction by exact inclusion-exclusion.")


if __name__ == "__main__":
    main()
