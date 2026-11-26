"""Certify signs of E_d at the limiting balanced-array geometric centers."""
import argparse
import json
from collections import Counter


def partial_sum_sign(even_part, odd_part, radicand):
    """Return the sign of even_part - odd_part * sqrt(radicand)."""
    difference = even_part**2 - radicand * odd_part**2
    return (difference > 0) - (difference < 0)


def certify(dimension, center, max_terms):
    """Enclose E_d(-sqrt(Q)) between two consecutive partial sums."""
    radicand = (center * (center + 1)) ** dimension
    even_part, odd_part = 1, 0
    term_scale = 1
    old_sign = 1
    for index in range(1, max_terms):
        factor = index**dimension
        even_part *= factor
        odd_part *= factor
        if index % 2:
            odd_part += term_scale
        else:
            term_scale *= radicand
            even_part += term_scale
        new_sign = partial_sum_sign(even_part, odd_part, radicand)
        if index > center and old_sign == new_sign and new_sign != 0:
            return {"d": dimension, "k": center, "Q": radicand,
                    "last_index": index, "sign": new_sign,
                    "expected_sign": (-1)**center}
        old_sign = new_sign
    raise ArithmeticError(f"unresolved sign for d={dimension}, k={center}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-d", type=int, default=10)
    parser.add_argument("--max-k", type=int, default=50)
    parser.add_argument("--max-terms", type=int, default=2000)
    args = parser.parse_args()
    if args.max_d < 2 or args.max_k < 1 or args.max_terms <= args.max_k+1:
        parser.error("require max-d >= 2, max-k >= 1 and max-terms >= max-k + 2")
    cases = [
        certify(dimension, center, args.max_terms)
        for dimension in range(2, args.max_d+1)
        for center in range(1, args.max_k+1)
    ]
    totals = []
    for dimension in range(2, args.max_d+1):
        rows = [row for row in cases if row["d"] == dimension]
        counts = Counter(row["sign"] for row in rows)
        totals.append({
            "d": dimension, "positive": counts[1], "negative": counts[-1],
            "agreement": sum(row["sign"] == row["expected_sign"] for row in rows),
            "reversal": sum(row["sign"] != row["expected_sign"] for row in rows),
            "max_last_index": max(row["last_index"] for row in rows),
        })
    print(json.dumps({"tested": len(cases), "totals": totals, "cases": cases},
                     separators=(",", ":")))


if __name__ == "__main__":
    main()
