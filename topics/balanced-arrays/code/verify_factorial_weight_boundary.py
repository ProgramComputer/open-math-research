"""Exact finite prefix and infinite fourth-power-sum certificate for cubic factorial weights."""
import json
from math import factorial
from pathlib import Path
import sys

from flint import fmpq_poly, fmpz_poly

# Isolated mode omits the script's directory. These are the existing topic checkers.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from rank_two_counts import multipartite_matchings, rank_two
from verify_four_column_mehler import array_count
from verify_paired_stability import signs_at_endpoints


def row_count_polynomials():
    """The kth polynomial equals (k!)^3 a(n,k,2,4) as a function of n."""
    x = fmpq_poly([0, 1])
    falling = [fmpq_poly([1])]
    for j in range(16):
        falling.append(falling[-1] * (x-j))
    return [sum(ways * falling[4*k-j] for j, ways in enumerate(multipartite_matchings(4, k)))
            / factorial(k) for k in range(1, 5)]


def power_sum_four(b, c, d, e):
    return b**4 - 4*b*b*c + 2*c*c + 4*b*d - 4*e


def main():
    b = row_count_polynomials()
    p = power_sum_four(*b)
    if p.degree() != 13 or p.leading_coefficient() != -64:
        raise ValueError("Fourth-power-sum polynomial has unexpected degree or leading term")
    shifted = p(fmpq_poly([76, 1]))
    if not all(x < 0 for x in shifted) or p(75) <= 0:
        raise ValueError("Infinite-tail certificate failed")
    print(json.dumps({"shift": 76, "power_sum_coefficients_at_shift":
                      [int(x) for x in shifted]}, separators=(",", ":")))
    for n in range(76):
        raw = [rank_two(n, k, 4) for k in range(n//2+1)]
        independent = [array_count(n, k) for k in range(n//2+1)]
        if raw != independent:
            raise ValueError(f"Labeled arrays disagree at size {n}")
        weighted = [v*factorial(k)**3 for k, v in enumerate(raw)]
        f = fmpz_poly(weighted)
        if any(p(n) != f[k] for k, p in enumerate(b, 1)):
            raise ValueError(f"Symbolic quota counts disagree at size {n}")
        if f.degree() and f.gcd(f.derivative()).degree() != 0:
            raise ValueError(f"Repeated zero at size {n}")
        left, zero, right = signs_at_endpoints(f)
        if zero != right or (left-right == f.degree()) != (n <= 15):
            raise ValueError(f"Unexpected root count at size {n}")
        print(json.dumps({"n": n, "weighted_coefficients": weighted,
                          "sturm_variations": [left, zero, right],
                          "distinct_real_roots": left-right}, separators=(",", ":")))


if __name__ == "__main__":
    main()
